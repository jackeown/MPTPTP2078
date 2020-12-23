%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:16 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 531 expanded)
%              Number of clauses        :   47 (  99 expanded)
%              Number of leaves         :   20 ( 164 expanded)
%              Depth                    :   18
%              Number of atoms          :  196 ( 726 expanded)
%              Number of equality atoms :  135 ( 648 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f10])).

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
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f40,f48,f48])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 )
   => ( sK2 != sK3
      & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK2 != sK3
    & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f30])).

fof(f52,plain,(
    k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f52,f54,f54])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f39,f54])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f72,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X1,X1,X0),k4_xboole_0(k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f39,f48,f48])).

fof(f53,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_453,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_451,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_849,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK3),k1_xboole_0) = k1_enumset1(sK3,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_16,c_12])).

cnf(c_954,plain,
    ( k1_enumset1(sK3,sK3,sK2) = k1_enumset1(sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_5,c_849])).

cnf(c_1050,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_954,c_16])).

cnf(c_1111,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_1050])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_457,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4782,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_457])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_683,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_693,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_683,c_5])).

cnf(c_4785,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
    | r1_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4782,c_693])).

cnf(c_5413,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_4785])).

cnf(c_5421,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_5413])).

cnf(c_1056,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK2),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(sK3,sK3,sK2))) = k1_enumset1(sK3,sK3,X0) ),
    inference(superposition,[status(thm)],[c_954,c_12])).

cnf(c_1080,plain,
    ( k1_enumset1(sK3,sK2,X0) = k1_enumset1(sK3,sK3,X0) ),
    inference(demodulation,[status(thm)],[c_1056,c_12])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_452,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2149,plain,
    ( sK3 = X0
    | r2_hidden(X0,k1_enumset1(sK3,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1080,c_452])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X1))) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1114,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK2),k1_xboole_0) = k1_enumset1(sK2,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1050,c_1])).

cnf(c_1261,plain,
    ( k1_enumset1(sK2,sK3,sK2) = k1_enumset1(sK3,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1114,c_5])).

cnf(c_1064,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(sK3,sK3,sK2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,sK3) ),
    inference(superposition,[status(thm)],[c_954,c_12])).

cnf(c_1828,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(sK2,sK3,sK2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,sK3) ),
    inference(light_normalisation,[status(thm)],[c_1064,c_1261])).

cnf(c_1837,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK3,sK2),k4_xboole_0(k1_enumset1(sK2,sK3,sK2),k1_enumset1(sK2,sK3,sK2))) = k1_enumset1(sK3,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1261,c_1828])).

cnf(c_949,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_693,c_4])).

cnf(c_1841,plain,
    ( k1_enumset1(sK2,sK3,sK2) = k1_enumset1(sK3,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1837,c_5,c_949])).

cnf(c_1246,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0) = k1_enumset1(sK2,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1111,c_12])).

cnf(c_1252,plain,
    ( k1_enumset1(sK2,sK3,sK2) = k1_enumset1(sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1246,c_5])).

cnf(c_2333,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_enumset1(sK3,sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_1841,c_1252])).

cnf(c_4391,plain,
    ( sK3 = X0
    | r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2149,c_2333])).

cnf(c_7503,plain,
    ( sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_5421,c_4391])).

cnf(c_307,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_529,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_705,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_306,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_583,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_15,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7503,c_705,c_583,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:08:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.37/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/0.98  
% 3.37/0.98  ------  iProver source info
% 3.37/0.98  
% 3.37/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.37/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/0.98  git: non_committed_changes: false
% 3.37/0.98  git: last_make_outside_of_git: false
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.98  --extra_neg_conj                        none
% 3.37/0.98  --large_theory_mode                     true
% 3.37/0.98  --prolific_symb_bound                   200
% 3.37/0.98  --lt_threshold                          2000
% 3.37/0.98  --clause_weak_htbl                      true
% 3.37/0.98  --gc_record_bc_elim                     false
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing Options
% 3.37/0.98  
% 3.37/0.98  --preprocessing_flag                    true
% 3.37/0.98  --time_out_prep_mult                    0.1
% 3.37/0.98  --splitting_mode                        input
% 3.37/0.98  --splitting_grd                         true
% 3.37/0.98  --splitting_cvd                         false
% 3.37/0.98  --splitting_cvd_svl                     false
% 3.37/0.98  --splitting_nvd                         32
% 3.37/0.98  --sub_typing                            true
% 3.37/0.98  --prep_gs_sim                           true
% 3.37/0.98  --prep_unflatten                        true
% 3.37/0.98  --prep_res_sim                          true
% 3.37/0.98  --prep_upred                            true
% 3.37/0.98  --prep_sem_filter                       exhaustive
% 3.37/0.98  --prep_sem_filter_out                   false
% 3.37/0.98  --pred_elim                             true
% 3.37/0.98  --res_sim_input                         true
% 3.37/0.98  --eq_ax_congr_red                       true
% 3.37/0.98  --pure_diseq_elim                       true
% 3.37/0.98  --brand_transform                       false
% 3.37/0.98  --non_eq_to_eq                          false
% 3.37/0.98  --prep_def_merge                        true
% 3.37/0.98  --prep_def_merge_prop_impl              false
% 3.37/0.98  --prep_def_merge_mbd                    true
% 3.37/0.98  --prep_def_merge_tr_red                 false
% 3.37/0.98  --prep_def_merge_tr_cl                  false
% 3.37/0.98  --smt_preprocessing                     true
% 3.37/0.98  --smt_ac_axioms                         fast
% 3.37/0.98  --preprocessed_out                      false
% 3.37/0.98  --preprocessed_stats                    false
% 3.37/0.98  
% 3.37/0.98  ------ Abstraction refinement Options
% 3.37/0.98  
% 3.37/0.98  --abstr_ref                             []
% 3.37/0.98  --abstr_ref_prep                        false
% 3.37/0.98  --abstr_ref_until_sat                   false
% 3.37/0.98  --abstr_ref_sig_restrict                funpre
% 3.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.98  --abstr_ref_under                       []
% 3.37/0.98  
% 3.37/0.98  ------ SAT Options
% 3.37/0.98  
% 3.37/0.98  --sat_mode                              false
% 3.37/0.98  --sat_fm_restart_options                ""
% 3.37/0.98  --sat_gr_def                            false
% 3.37/0.98  --sat_epr_types                         true
% 3.37/0.98  --sat_non_cyclic_types                  false
% 3.37/0.98  --sat_finite_models                     false
% 3.37/0.98  --sat_fm_lemmas                         false
% 3.37/0.98  --sat_fm_prep                           false
% 3.37/0.98  --sat_fm_uc_incr                        true
% 3.37/0.98  --sat_out_model                         small
% 3.37/0.98  --sat_out_clauses                       false
% 3.37/0.98  
% 3.37/0.98  ------ QBF Options
% 3.37/0.98  
% 3.37/0.98  --qbf_mode                              false
% 3.37/0.98  --qbf_elim_univ                         false
% 3.37/0.98  --qbf_dom_inst                          none
% 3.37/0.98  --qbf_dom_pre_inst                      false
% 3.37/0.98  --qbf_sk_in                             false
% 3.37/0.98  --qbf_pred_elim                         true
% 3.37/0.98  --qbf_split                             512
% 3.37/0.98  
% 3.37/0.98  ------ BMC1 Options
% 3.37/0.98  
% 3.37/0.98  --bmc1_incremental                      false
% 3.37/0.98  --bmc1_axioms                           reachable_all
% 3.37/0.98  --bmc1_min_bound                        0
% 3.37/0.98  --bmc1_max_bound                        -1
% 3.37/0.98  --bmc1_max_bound_default                -1
% 3.37/0.98  --bmc1_symbol_reachability              true
% 3.37/0.98  --bmc1_property_lemmas                  false
% 3.37/0.98  --bmc1_k_induction                      false
% 3.37/0.98  --bmc1_non_equiv_states                 false
% 3.37/0.98  --bmc1_deadlock                         false
% 3.37/0.98  --bmc1_ucm                              false
% 3.37/0.98  --bmc1_add_unsat_core                   none
% 3.37/0.98  --bmc1_unsat_core_children              false
% 3.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.98  --bmc1_out_stat                         full
% 3.37/0.98  --bmc1_ground_init                      false
% 3.37/0.98  --bmc1_pre_inst_next_state              false
% 3.37/0.98  --bmc1_pre_inst_state                   false
% 3.37/0.98  --bmc1_pre_inst_reach_state             false
% 3.37/0.98  --bmc1_out_unsat_core                   false
% 3.37/0.98  --bmc1_aig_witness_out                  false
% 3.37/0.98  --bmc1_verbose                          false
% 3.37/0.98  --bmc1_dump_clauses_tptp                false
% 3.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.98  --bmc1_dump_file                        -
% 3.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.98  --bmc1_ucm_extend_mode                  1
% 3.37/0.98  --bmc1_ucm_init_mode                    2
% 3.37/0.98  --bmc1_ucm_cone_mode                    none
% 3.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.98  --bmc1_ucm_relax_model                  4
% 3.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.98  --bmc1_ucm_layered_model                none
% 3.37/0.98  --bmc1_ucm_max_lemma_size               10
% 3.37/0.98  
% 3.37/0.98  ------ AIG Options
% 3.37/0.98  
% 3.37/0.98  --aig_mode                              false
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation Options
% 3.37/0.98  
% 3.37/0.98  --instantiation_flag                    true
% 3.37/0.98  --inst_sos_flag                         false
% 3.37/0.98  --inst_sos_phase                        true
% 3.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel_side                     num_symb
% 3.37/0.98  --inst_solver_per_active                1400
% 3.37/0.98  --inst_solver_calls_frac                1.
% 3.37/0.98  --inst_passive_queue_type               priority_queues
% 3.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.98  --inst_passive_queues_freq              [25;2]
% 3.37/0.98  --inst_dismatching                      true
% 3.37/0.98  --inst_eager_unprocessed_to_passive     true
% 3.37/0.98  --inst_prop_sim_given                   true
% 3.37/0.98  --inst_prop_sim_new                     false
% 3.37/0.98  --inst_subs_new                         false
% 3.37/0.98  --inst_eq_res_simp                      false
% 3.37/0.98  --inst_subs_given                       false
% 3.37/0.98  --inst_orphan_elimination               true
% 3.37/0.98  --inst_learning_loop_flag               true
% 3.37/0.98  --inst_learning_start                   3000
% 3.37/0.98  --inst_learning_factor                  2
% 3.37/0.98  --inst_start_prop_sim_after_learn       3
% 3.37/0.98  --inst_sel_renew                        solver
% 3.37/0.98  --inst_lit_activity_flag                true
% 3.37/0.98  --inst_restr_to_given                   false
% 3.37/0.98  --inst_activity_threshold               500
% 3.37/0.98  --inst_out_proof                        true
% 3.37/0.98  
% 3.37/0.98  ------ Resolution Options
% 3.37/0.98  
% 3.37/0.98  --resolution_flag                       true
% 3.37/0.98  --res_lit_sel                           adaptive
% 3.37/0.98  --res_lit_sel_side                      none
% 3.37/0.98  --res_ordering                          kbo
% 3.37/0.98  --res_to_prop_solver                    active
% 3.37/0.98  --res_prop_simpl_new                    false
% 3.37/0.98  --res_prop_simpl_given                  true
% 3.37/0.98  --res_passive_queue_type                priority_queues
% 3.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.98  --res_passive_queues_freq               [15;5]
% 3.37/0.98  --res_forward_subs                      full
% 3.37/0.98  --res_backward_subs                     full
% 3.37/0.98  --res_forward_subs_resolution           true
% 3.37/0.98  --res_backward_subs_resolution          true
% 3.37/0.98  --res_orphan_elimination                true
% 3.37/0.98  --res_time_limit                        2.
% 3.37/0.98  --res_out_proof                         true
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Options
% 3.37/0.98  
% 3.37/0.98  --superposition_flag                    true
% 3.37/0.98  --sup_passive_queue_type                priority_queues
% 3.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.98  --demod_completeness_check              fast
% 3.37/0.98  --demod_use_ground                      true
% 3.37/0.98  --sup_to_prop_solver                    passive
% 3.37/0.98  --sup_prop_simpl_new                    true
% 3.37/0.98  --sup_prop_simpl_given                  true
% 3.37/0.98  --sup_fun_splitting                     false
% 3.37/0.98  --sup_smt_interval                      50000
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Simplification Setup
% 3.37/0.98  
% 3.37/0.98  --sup_indices_passive                   []
% 3.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_full_bw                           [BwDemod]
% 3.37/0.98  --sup_immed_triv                        [TrivRules]
% 3.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_immed_bw_main                     []
% 3.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  
% 3.37/0.98  ------ Combination Options
% 3.37/0.98  
% 3.37/0.98  --comb_res_mult                         3
% 3.37/0.98  --comb_sup_mult                         2
% 3.37/0.98  --comb_inst_mult                        10
% 3.37/0.98  
% 3.37/0.98  ------ Debug Options
% 3.37/0.98  
% 3.37/0.98  --dbg_backtrace                         false
% 3.37/0.98  --dbg_dump_prop_clauses                 false
% 3.37/0.98  --dbg_dump_prop_clauses_file            -
% 3.37/0.98  --dbg_out_stat                          false
% 3.37/0.98  ------ Parsing...
% 3.37/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/0.98  ------ Proving...
% 3.37/0.98  ------ Problem Properties 
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  clauses                                 17
% 3.37/0.98  conjectures                             2
% 3.37/0.98  EPR                                     1
% 3.37/0.98  Horn                                    14
% 3.37/0.98  unary                                   11
% 3.37/0.98  binary                                  4
% 3.37/0.98  lits                                    25
% 3.37/0.98  lits eq                                 15
% 3.37/0.98  fd_pure                                 0
% 3.37/0.98  fd_pseudo                               0
% 3.37/0.98  fd_cond                                 0
% 3.37/0.98  fd_pseudo_cond                          2
% 3.37/0.98  AC symbols                              0
% 3.37/0.98  
% 3.37/0.98  ------ Schedule dynamic 5 is on 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  Current options:
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.98  --extra_neg_conj                        none
% 3.37/0.98  --large_theory_mode                     true
% 3.37/0.98  --prolific_symb_bound                   200
% 3.37/0.98  --lt_threshold                          2000
% 3.37/0.98  --clause_weak_htbl                      true
% 3.37/0.98  --gc_record_bc_elim                     false
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing Options
% 3.37/0.98  
% 3.37/0.98  --preprocessing_flag                    true
% 3.37/0.98  --time_out_prep_mult                    0.1
% 3.37/0.98  --splitting_mode                        input
% 3.37/0.98  --splitting_grd                         true
% 3.37/0.98  --splitting_cvd                         false
% 3.37/0.98  --splitting_cvd_svl                     false
% 3.37/0.98  --splitting_nvd                         32
% 3.37/0.98  --sub_typing                            true
% 3.37/0.98  --prep_gs_sim                           true
% 3.37/0.98  --prep_unflatten                        true
% 3.37/0.98  --prep_res_sim                          true
% 3.37/0.98  --prep_upred                            true
% 3.37/0.98  --prep_sem_filter                       exhaustive
% 3.37/0.98  --prep_sem_filter_out                   false
% 3.37/0.98  --pred_elim                             true
% 3.37/0.98  --res_sim_input                         true
% 3.37/0.98  --eq_ax_congr_red                       true
% 3.37/0.98  --pure_diseq_elim                       true
% 3.37/0.98  --brand_transform                       false
% 3.37/0.98  --non_eq_to_eq                          false
% 3.37/0.98  --prep_def_merge                        true
% 3.37/0.98  --prep_def_merge_prop_impl              false
% 3.37/0.98  --prep_def_merge_mbd                    true
% 3.37/0.98  --prep_def_merge_tr_red                 false
% 3.37/0.98  --prep_def_merge_tr_cl                  false
% 3.37/0.98  --smt_preprocessing                     true
% 3.37/0.98  --smt_ac_axioms                         fast
% 3.37/0.98  --preprocessed_out                      false
% 3.37/0.98  --preprocessed_stats                    false
% 3.37/0.98  
% 3.37/0.98  ------ Abstraction refinement Options
% 3.37/0.98  
% 3.37/0.98  --abstr_ref                             []
% 3.37/0.98  --abstr_ref_prep                        false
% 3.37/0.98  --abstr_ref_until_sat                   false
% 3.37/0.98  --abstr_ref_sig_restrict                funpre
% 3.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.98  --abstr_ref_under                       []
% 3.37/0.98  
% 3.37/0.98  ------ SAT Options
% 3.37/0.98  
% 3.37/0.98  --sat_mode                              false
% 3.37/0.98  --sat_fm_restart_options                ""
% 3.37/0.98  --sat_gr_def                            false
% 3.37/0.98  --sat_epr_types                         true
% 3.37/0.98  --sat_non_cyclic_types                  false
% 3.37/0.98  --sat_finite_models                     false
% 3.37/0.98  --sat_fm_lemmas                         false
% 3.37/0.98  --sat_fm_prep                           false
% 3.37/0.98  --sat_fm_uc_incr                        true
% 3.37/0.98  --sat_out_model                         small
% 3.37/0.98  --sat_out_clauses                       false
% 3.37/0.98  
% 3.37/0.98  ------ QBF Options
% 3.37/0.98  
% 3.37/0.98  --qbf_mode                              false
% 3.37/0.98  --qbf_elim_univ                         false
% 3.37/0.98  --qbf_dom_inst                          none
% 3.37/0.98  --qbf_dom_pre_inst                      false
% 3.37/0.98  --qbf_sk_in                             false
% 3.37/0.98  --qbf_pred_elim                         true
% 3.37/0.98  --qbf_split                             512
% 3.37/0.98  
% 3.37/0.98  ------ BMC1 Options
% 3.37/0.98  
% 3.37/0.98  --bmc1_incremental                      false
% 3.37/0.98  --bmc1_axioms                           reachable_all
% 3.37/0.98  --bmc1_min_bound                        0
% 3.37/0.98  --bmc1_max_bound                        -1
% 3.37/0.98  --bmc1_max_bound_default                -1
% 3.37/0.98  --bmc1_symbol_reachability              true
% 3.37/0.98  --bmc1_property_lemmas                  false
% 3.37/0.98  --bmc1_k_induction                      false
% 3.37/0.98  --bmc1_non_equiv_states                 false
% 3.37/0.98  --bmc1_deadlock                         false
% 3.37/0.98  --bmc1_ucm                              false
% 3.37/0.98  --bmc1_add_unsat_core                   none
% 3.37/0.98  --bmc1_unsat_core_children              false
% 3.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.98  --bmc1_out_stat                         full
% 3.37/0.98  --bmc1_ground_init                      false
% 3.37/0.98  --bmc1_pre_inst_next_state              false
% 3.37/0.98  --bmc1_pre_inst_state                   false
% 3.37/0.98  --bmc1_pre_inst_reach_state             false
% 3.37/0.98  --bmc1_out_unsat_core                   false
% 3.37/0.98  --bmc1_aig_witness_out                  false
% 3.37/0.98  --bmc1_verbose                          false
% 3.37/0.98  --bmc1_dump_clauses_tptp                false
% 3.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.98  --bmc1_dump_file                        -
% 3.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.98  --bmc1_ucm_extend_mode                  1
% 3.37/0.98  --bmc1_ucm_init_mode                    2
% 3.37/0.98  --bmc1_ucm_cone_mode                    none
% 3.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.98  --bmc1_ucm_relax_model                  4
% 3.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.98  --bmc1_ucm_layered_model                none
% 3.37/0.98  --bmc1_ucm_max_lemma_size               10
% 3.37/0.98  
% 3.37/0.98  ------ AIG Options
% 3.37/0.98  
% 3.37/0.98  --aig_mode                              false
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation Options
% 3.37/0.98  
% 3.37/0.98  --instantiation_flag                    true
% 3.37/0.98  --inst_sos_flag                         false
% 3.37/0.98  --inst_sos_phase                        true
% 3.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel_side                     none
% 3.37/0.98  --inst_solver_per_active                1400
% 3.37/0.98  --inst_solver_calls_frac                1.
% 3.37/0.98  --inst_passive_queue_type               priority_queues
% 3.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.98  --inst_passive_queues_freq              [25;2]
% 3.37/0.98  --inst_dismatching                      true
% 3.37/0.98  --inst_eager_unprocessed_to_passive     true
% 3.37/0.98  --inst_prop_sim_given                   true
% 3.37/0.98  --inst_prop_sim_new                     false
% 3.37/0.98  --inst_subs_new                         false
% 3.37/0.98  --inst_eq_res_simp                      false
% 3.37/0.98  --inst_subs_given                       false
% 3.37/0.98  --inst_orphan_elimination               true
% 3.37/0.98  --inst_learning_loop_flag               true
% 3.37/0.98  --inst_learning_start                   3000
% 3.37/0.98  --inst_learning_factor                  2
% 3.37/0.98  --inst_start_prop_sim_after_learn       3
% 3.37/0.98  --inst_sel_renew                        solver
% 3.37/0.98  --inst_lit_activity_flag                true
% 3.37/0.98  --inst_restr_to_given                   false
% 3.37/0.98  --inst_activity_threshold               500
% 3.37/0.98  --inst_out_proof                        true
% 3.37/0.98  
% 3.37/0.98  ------ Resolution Options
% 3.37/0.98  
% 3.37/0.98  --resolution_flag                       false
% 3.37/0.98  --res_lit_sel                           adaptive
% 3.37/0.98  --res_lit_sel_side                      none
% 3.37/0.98  --res_ordering                          kbo
% 3.37/0.98  --res_to_prop_solver                    active
% 3.37/0.98  --res_prop_simpl_new                    false
% 3.37/0.98  --res_prop_simpl_given                  true
% 3.37/0.98  --res_passive_queue_type                priority_queues
% 3.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.98  --res_passive_queues_freq               [15;5]
% 3.37/0.98  --res_forward_subs                      full
% 3.37/0.98  --res_backward_subs                     full
% 3.37/0.98  --res_forward_subs_resolution           true
% 3.37/0.98  --res_backward_subs_resolution          true
% 3.37/0.98  --res_orphan_elimination                true
% 3.37/0.98  --res_time_limit                        2.
% 3.37/0.98  --res_out_proof                         true
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Options
% 3.37/0.98  
% 3.37/0.98  --superposition_flag                    true
% 3.37/0.98  --sup_passive_queue_type                priority_queues
% 3.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.98  --demod_completeness_check              fast
% 3.37/0.98  --demod_use_ground                      true
% 3.37/0.98  --sup_to_prop_solver                    passive
% 3.37/0.98  --sup_prop_simpl_new                    true
% 3.37/0.98  --sup_prop_simpl_given                  true
% 3.37/0.98  --sup_fun_splitting                     false
% 3.37/0.98  --sup_smt_interval                      50000
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Simplification Setup
% 3.37/0.98  
% 3.37/0.98  --sup_indices_passive                   []
% 3.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_full_bw                           [BwDemod]
% 3.37/0.98  --sup_immed_triv                        [TrivRules]
% 3.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_immed_bw_main                     []
% 3.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  
% 3.37/0.98  ------ Combination Options
% 3.37/0.98  
% 3.37/0.98  --comb_res_mult                         3
% 3.37/0.98  --comb_sup_mult                         2
% 3.37/0.98  --comb_inst_mult                        10
% 3.37/0.98  
% 3.37/0.98  ------ Debug Options
% 3.37/0.98  
% 3.37/0.98  --dbg_backtrace                         false
% 3.37/0.98  --dbg_dump_prop_clauses                 false
% 3.37/0.98  --dbg_dump_prop_clauses_file            -
% 3.37/0.98  --dbg_out_stat                          false
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  ------ Proving...
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  % SZS status Theorem for theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  fof(f10,axiom,(
% 3.37/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f26,plain,(
% 3.37/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.37/0.98    inference(nnf_transformation,[],[f10])).
% 3.37/0.98  
% 3.37/0.98  fof(f27,plain,(
% 3.37/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.37/0.98    inference(rectify,[],[f26])).
% 3.37/0.98  
% 3.37/0.98  fof(f28,plain,(
% 3.37/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f29,plain,(
% 3.37/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.37/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 3.37/0.98  
% 3.37/0.98  fof(f42,plain,(
% 3.37/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.37/0.98    inference(cnf_transformation,[],[f29])).
% 3.37/0.98  
% 3.37/0.98  fof(f13,axiom,(
% 3.37/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f47,plain,(
% 3.37/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f13])).
% 3.37/0.98  
% 3.37/0.98  fof(f14,axiom,(
% 3.37/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f48,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f14])).
% 3.37/0.98  
% 3.37/0.98  fof(f54,plain,(
% 3.37/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f47,f48])).
% 3.37/0.98  
% 3.37/0.98  fof(f64,plain,(
% 3.37/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.37/0.98    inference(definition_unfolding,[],[f42,f54])).
% 3.37/0.98  
% 3.37/0.98  fof(f70,plain,(
% 3.37/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.37/0.98    inference(equality_resolution,[],[f64])).
% 3.37/0.98  
% 3.37/0.98  fof(f71,plain,(
% 3.37/0.98    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.37/0.98    inference(equality_resolution,[],[f70])).
% 3.37/0.98  
% 3.37/0.98  fof(f17,axiom,(
% 3.37/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f22,plain,(
% 3.37/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.37/0.98    inference(ennf_transformation,[],[f17])).
% 3.37/0.98  
% 3.37/0.98  fof(f51,plain,(
% 3.37/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f22])).
% 3.37/0.98  
% 3.37/0.98  fof(f68,plain,(
% 3.37/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f51,f54])).
% 3.37/0.98  
% 3.37/0.98  fof(f9,axiom,(
% 3.37/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f40,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f9])).
% 3.37/0.98  
% 3.37/0.98  fof(f61,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f40,f48,f48])).
% 3.37/0.98  
% 3.37/0.98  fof(f6,axiom,(
% 3.37/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f37,plain,(
% 3.37/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.37/0.98    inference(cnf_transformation,[],[f6])).
% 3.37/0.98  
% 3.37/0.98  fof(f18,conjecture,(
% 3.37/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f19,negated_conjecture,(
% 3.37/0.98    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 3.37/0.98    inference(negated_conjecture,[],[f18])).
% 3.37/0.98  
% 3.37/0.98  fof(f23,plain,(
% 3.37/0.98    ? [X0,X1] : (X0 != X1 & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0)),
% 3.37/0.98    inference(ennf_transformation,[],[f19])).
% 3.37/0.98  
% 3.37/0.98  fof(f30,plain,(
% 3.37/0.98    ? [X0,X1] : (X0 != X1 & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0) => (sK2 != sK3 & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0)),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f31,plain,(
% 3.37/0.98    sK2 != sK3 & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0),
% 3.37/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f30])).
% 3.37/0.98  
% 3.37/0.98  fof(f52,plain,(
% 3.37/0.98    k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0),
% 3.37/0.98    inference(cnf_transformation,[],[f31])).
% 3.37/0.98  
% 3.37/0.98  fof(f69,plain,(
% 3.37/0.98    k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_xboole_0),
% 3.37/0.98    inference(definition_unfolding,[],[f52,f54,f54])).
% 3.37/0.98  
% 3.37/0.98  fof(f15,axiom,(
% 3.37/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f49,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f15])).
% 3.37/0.98  
% 3.37/0.98  fof(f12,axiom,(
% 3.37/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f46,plain,(
% 3.37/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f12])).
% 3.37/0.98  
% 3.37/0.98  fof(f8,axiom,(
% 3.37/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f39,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f8])).
% 3.37/0.98  
% 3.37/0.98  fof(f55,plain,(
% 3.37/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f46,f39,f54])).
% 3.37/0.98  
% 3.37/0.98  fof(f66,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f49,f55])).
% 3.37/0.98  
% 3.37/0.98  fof(f2,axiom,(
% 3.37/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f20,plain,(
% 3.37/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.37/0.98    inference(rectify,[],[f2])).
% 3.37/0.98  
% 3.37/0.98  fof(f21,plain,(
% 3.37/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.37/0.98    inference(ennf_transformation,[],[f20])).
% 3.37/0.98  
% 3.37/0.98  fof(f24,plain,(
% 3.37/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f25,plain,(
% 3.37/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.37/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f24])).
% 3.37/0.98  
% 3.37/0.98  fof(f33,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.37/0.98    inference(cnf_transformation,[],[f25])).
% 3.37/0.98  
% 3.37/0.98  fof(f5,axiom,(
% 3.37/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f36,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.37/0.98    inference(cnf_transformation,[],[f5])).
% 3.37/0.98  
% 3.37/0.98  fof(f58,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.37/0.98    inference(definition_unfolding,[],[f33,f36])).
% 3.37/0.98  
% 3.37/0.98  fof(f4,axiom,(
% 3.37/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f35,plain,(
% 3.37/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.37/0.98    inference(cnf_transformation,[],[f4])).
% 3.37/0.98  
% 3.37/0.98  fof(f60,plain,(
% 3.37/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.37/0.98    inference(definition_unfolding,[],[f35,f36])).
% 3.37/0.98  
% 3.37/0.98  fof(f3,axiom,(
% 3.37/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f34,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.37/0.98    inference(cnf_transformation,[],[f3])).
% 3.37/0.98  
% 3.37/0.98  fof(f56,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.37/0.98    inference(definition_unfolding,[],[f34,f36])).
% 3.37/0.98  
% 3.37/0.98  fof(f41,plain,(
% 3.37/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.37/0.98    inference(cnf_transformation,[],[f29])).
% 3.37/0.98  
% 3.37/0.98  fof(f65,plain,(
% 3.37/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.37/0.98    inference(definition_unfolding,[],[f41,f54])).
% 3.37/0.98  
% 3.37/0.98  fof(f72,plain,(
% 3.37/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.37/0.98    inference(equality_resolution,[],[f65])).
% 3.37/0.98  
% 3.37/0.98  fof(f11,axiom,(
% 3.37/0.98    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 3.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f45,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f11])).
% 3.37/0.98  
% 3.37/0.98  fof(f57,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X1,X1,X0),k4_xboole_0(k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X0))) = k1_enumset1(X0,X1,X2)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f45,f39,f48,f48])).
% 3.37/0.98  
% 3.37/0.98  fof(f53,plain,(
% 3.37/0.98    sK2 != sK3),
% 3.37/0.98    inference(cnf_transformation,[],[f31])).
% 3.37/0.98  
% 3.37/0.98  cnf(c_10,plain,
% 3.37/0.98      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.37/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_453,plain,
% 3.37/0.98      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_14,plain,
% 3.37/0.98      ( r2_hidden(X0,X1) | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
% 3.37/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_451,plain,
% 3.37/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.37/0.98      | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_7,plain,
% 3.37/0.98      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.37/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_5,plain,
% 3.37/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.37/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_16,negated_conjecture,
% 3.37/0.98      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_xboole_0 ),
% 3.37/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_12,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
% 3.37/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_849,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK3),k1_xboole_0) = k1_enumset1(sK3,sK3,sK2) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_16,c_12]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_954,plain,
% 3.37/0.98      ( k1_enumset1(sK3,sK3,sK2) = k1_enumset1(sK3,sK3,sK3) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_5,c_849]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1050,plain,
% 3.37/0.98      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK2)) = k1_xboole_0 ),
% 3.37/0.98      inference(demodulation,[status(thm)],[c_954,c_16]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1111,plain,
% 3.37/0.98      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) = k1_xboole_0 ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_7,c_1050]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_2,plain,
% 3.37/0.98      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.37/0.98      | ~ r1_xboole_0(X1,X2) ),
% 3.37/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_457,plain,
% 3.37/0.98      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.37/0.98      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_4782,plain,
% 3.37/0.98      ( r2_hidden(X0,k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_xboole_0)) != iProver_top
% 3.37/0.98      | r1_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_1111,c_457]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_4,plain,
% 3.37/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.37/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_0,plain,
% 3.37/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.37/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_683,plain,
% 3.37/0.98      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_693,plain,
% 3.37/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.37/0.98      inference(light_normalisation,[status(thm)],[c_683,c_5]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_4785,plain,
% 3.37/0.98      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
% 3.37/0.98      | r1_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
% 3.37/0.98      inference(demodulation,[status(thm)],[c_4782,c_693]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_5413,plain,
% 3.37/0.98      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
% 3.37/0.98      | r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_451,c_4785]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_5421,plain,
% 3.37/0.98      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_453,c_5413]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1056,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK2),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(sK3,sK3,sK2))) = k1_enumset1(sK3,sK3,X0) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_954,c_12]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1080,plain,
% 3.37/0.98      ( k1_enumset1(sK3,sK2,X0) = k1_enumset1(sK3,sK3,X0) ),
% 3.37/0.98      inference(demodulation,[status(thm)],[c_1056,c_12]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_11,plain,
% 3.37/0.98      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.37/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_452,plain,
% 3.37/0.98      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_2149,plain,
% 3.37/0.98      ( sK3 = X0
% 3.37/0.98      | r2_hidden(X0,k1_enumset1(sK3,sK2,sK3)) != iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_1080,c_452]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X1))) = k1_enumset1(X1,X0,X2) ),
% 3.37/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1114,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK2),k1_xboole_0) = k1_enumset1(sK2,sK3,sK2) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_1050,c_1]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1261,plain,
% 3.37/0.98      ( k1_enumset1(sK2,sK3,sK2) = k1_enumset1(sK3,sK3,sK2) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_1114,c_5]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1064,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(sK3,sK3,sK2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,sK3) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_954,c_12]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1828,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(sK2,sK3,sK2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,sK3) ),
% 3.37/0.98      inference(light_normalisation,[status(thm)],[c_1064,c_1261]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1837,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(sK2,sK3,sK2),k4_xboole_0(k1_enumset1(sK2,sK3,sK2),k1_enumset1(sK2,sK3,sK2))) = k1_enumset1(sK3,sK2,sK3) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_1261,c_1828]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_949,plain,
% 3.37/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.37/0.98      inference(demodulation,[status(thm)],[c_693,c_4]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1841,plain,
% 3.37/0.98      ( k1_enumset1(sK2,sK3,sK2) = k1_enumset1(sK3,sK2,sK3) ),
% 3.37/0.98      inference(demodulation,[status(thm)],[c_1837,c_5,c_949]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1246,plain,
% 3.37/0.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0) = k1_enumset1(sK2,sK3,sK2) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_1111,c_12]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1252,plain,
% 3.37/0.99      ( k1_enumset1(sK2,sK3,sK2) = k1_enumset1(sK2,sK2,sK3) ),
% 3.37/0.99      inference(demodulation,[status(thm)],[c_1246,c_5]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2333,plain,
% 3.37/0.99      ( k1_enumset1(sK2,sK2,sK3) = k1_enumset1(sK3,sK2,sK3) ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1841,c_1252]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4391,plain,
% 3.37/0.99      ( sK3 = X0
% 3.37/0.99      | r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_2149,c_2333]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7503,plain,
% 3.37/0.99      ( sK3 = sK2 ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5421,c_4391]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_307,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_529,plain,
% 3.37/0.99      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_307]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_705,plain,
% 3.37/0.99      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_529]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_306,plain,( X0 = X0 ),theory(equality) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_583,plain,
% 3.37/0.99      ( sK2 = sK2 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_306]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_15,negated_conjecture,
% 3.37/0.99      ( sK2 != sK3 ),
% 3.37/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(contradiction,plain,
% 3.37/0.99      ( $false ),
% 3.37/0.99      inference(minisat,[status(thm)],[c_7503,c_705,c_583,c_15]) ).
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  ------                               Statistics
% 3.37/0.99  
% 3.37/0.99  ------ General
% 3.37/0.99  
% 3.37/0.99  abstr_ref_over_cycles:                  0
% 3.37/0.99  abstr_ref_under_cycles:                 0
% 3.37/0.99  gc_basic_clause_elim:                   0
% 3.37/0.99  forced_gc_time:                         0
% 3.37/0.99  parsing_time:                           0.008
% 3.37/0.99  unif_index_cands_time:                  0.
% 3.37/0.99  unif_index_add_time:                    0.
% 3.37/0.99  orderings_time:                         0.
% 3.37/0.99  out_proof_time:                         0.01
% 3.37/0.99  total_time:                             0.325
% 3.37/0.99  num_of_symbols:                         42
% 3.37/0.99  num_of_terms:                           6970
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing
% 3.37/0.99  
% 3.37/0.99  num_of_splits:                          0
% 3.37/0.99  num_of_split_atoms:                     0
% 3.37/0.99  num_of_reused_defs:                     0
% 3.37/0.99  num_eq_ax_congr_red:                    20
% 3.37/0.99  num_of_sem_filtered_clauses:            1
% 3.37/0.99  num_of_subtypes:                        0
% 3.37/0.99  monotx_restored_types:                  0
% 3.37/0.99  sat_num_of_epr_types:                   0
% 3.37/0.99  sat_num_of_non_cyclic_types:            0
% 3.37/0.99  sat_guarded_non_collapsed_types:        0
% 3.37/0.99  num_pure_diseq_elim:                    0
% 3.37/0.99  simp_replaced_by:                       0
% 3.37/0.99  res_preprocessed:                       66
% 3.37/0.99  prep_upred:                             0
% 3.37/0.99  prep_unflattend:                        20
% 3.37/0.99  smt_new_axioms:                         0
% 3.37/0.99  pred_elim_cands:                        2
% 3.37/0.99  pred_elim:                              0
% 3.37/0.99  pred_elim_cl:                           0
% 3.37/0.99  pred_elim_cycles:                       2
% 3.37/0.99  merged_defs:                            0
% 3.37/0.99  merged_defs_ncl:                        0
% 3.37/0.99  bin_hyper_res:                          0
% 3.37/0.99  prep_cycles:                            3
% 3.37/0.99  pred_elim_time:                         0.003
% 3.37/0.99  splitting_time:                         0.
% 3.37/0.99  sem_filter_time:                        0.
% 3.37/0.99  monotx_time:                            0.
% 3.37/0.99  subtype_inf_time:                       0.
% 3.37/0.99  
% 3.37/0.99  ------ Problem properties
% 3.37/0.99  
% 3.37/0.99  clauses:                                17
% 3.37/0.99  conjectures:                            2
% 3.37/0.99  epr:                                    1
% 3.37/0.99  horn:                                   14
% 3.37/0.99  ground:                                 2
% 3.37/0.99  unary:                                  11
% 3.37/0.99  binary:                                 4
% 3.37/0.99  lits:                                   25
% 3.37/0.99  lits_eq:                                15
% 3.37/0.99  fd_pure:                                0
% 3.37/0.99  fd_pseudo:                              0
% 3.37/0.99  fd_cond:                                0
% 3.37/0.99  fd_pseudo_cond:                         2
% 3.37/0.99  ac_symbols:                             0
% 3.37/0.99  
% 3.37/0.99  ------ Propositional Solver
% 3.37/0.99  
% 3.37/0.99  prop_solver_calls:                      27
% 3.37/0.99  prop_fast_solver_calls:                 422
% 3.37/0.99  smt_solver_calls:                       0
% 3.37/0.99  smt_fast_solver_calls:                  0
% 3.37/0.99  prop_num_of_clauses:                    2876
% 3.37/0.99  prop_preprocess_simplified:             5202
% 3.37/0.99  prop_fo_subsumed:                       1
% 3.37/0.99  prop_solver_time:                       0.
% 3.37/0.99  smt_solver_time:                        0.
% 3.37/0.99  smt_fast_solver_time:                   0.
% 3.37/0.99  prop_fast_solver_time:                  0.
% 3.37/0.99  prop_unsat_core_time:                   0.
% 3.37/0.99  
% 3.37/0.99  ------ QBF
% 3.37/0.99  
% 3.37/0.99  qbf_q_res:                              0
% 3.37/0.99  qbf_num_tautologies:                    0
% 3.37/0.99  qbf_prep_cycles:                        0
% 3.37/0.99  
% 3.37/0.99  ------ BMC1
% 3.37/0.99  
% 3.37/0.99  bmc1_current_bound:                     -1
% 3.37/0.99  bmc1_last_solved_bound:                 -1
% 3.37/0.99  bmc1_unsat_core_size:                   -1
% 3.37/0.99  bmc1_unsat_core_parents_size:           -1
% 3.37/0.99  bmc1_merge_next_fun:                    0
% 3.37/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.37/0.99  
% 3.37/0.99  ------ Instantiation
% 3.37/0.99  
% 3.37/0.99  inst_num_of_clauses:                    944
% 3.37/0.99  inst_num_in_passive:                    142
% 3.37/0.99  inst_num_in_active:                     355
% 3.37/0.99  inst_num_in_unprocessed:                447
% 3.37/0.99  inst_num_of_loops:                      470
% 3.37/0.99  inst_num_of_learning_restarts:          0
% 3.37/0.99  inst_num_moves_active_passive:          109
% 3.37/0.99  inst_lit_activity:                      0
% 3.37/0.99  inst_lit_activity_moves:                0
% 3.37/0.99  inst_num_tautologies:                   0
% 3.37/0.99  inst_num_prop_implied:                  0
% 3.37/0.99  inst_num_existing_simplified:           0
% 3.37/0.99  inst_num_eq_res_simplified:             0
% 3.37/0.99  inst_num_child_elim:                    0
% 3.37/0.99  inst_num_of_dismatching_blockings:      545
% 3.37/0.99  inst_num_of_non_proper_insts:           1200
% 3.37/0.99  inst_num_of_duplicates:                 0
% 3.37/0.99  inst_inst_num_from_inst_to_res:         0
% 3.37/0.99  inst_dismatching_checking_time:         0.
% 3.37/0.99  
% 3.37/0.99  ------ Resolution
% 3.37/0.99  
% 3.37/0.99  res_num_of_clauses:                     0
% 3.37/0.99  res_num_in_passive:                     0
% 3.37/0.99  res_num_in_active:                      0
% 3.37/0.99  res_num_of_loops:                       69
% 3.37/0.99  res_forward_subset_subsumed:            94
% 3.37/0.99  res_backward_subset_subsumed:           2
% 3.37/0.99  res_forward_subsumed:                   0
% 3.37/0.99  res_backward_subsumed:                  0
% 3.37/0.99  res_forward_subsumption_resolution:     0
% 3.37/0.99  res_backward_subsumption_resolution:    0
% 3.37/0.99  res_clause_to_clause_subsumption:       1300
% 3.37/0.99  res_orphan_elimination:                 0
% 3.37/0.99  res_tautology_del:                      94
% 3.37/0.99  res_num_eq_res_simplified:              0
% 3.37/0.99  res_num_sel_changes:                    0
% 3.37/0.99  res_moves_from_active_to_pass:          0
% 3.37/0.99  
% 3.37/0.99  ------ Superposition
% 3.37/0.99  
% 3.37/0.99  sup_time_total:                         0.
% 3.37/0.99  sup_time_generating:                    0.
% 3.37/0.99  sup_time_sim_full:                      0.
% 3.37/0.99  sup_time_sim_immed:                     0.
% 3.37/0.99  
% 3.37/0.99  sup_num_of_clauses:                     175
% 3.37/0.99  sup_num_in_active:                      68
% 3.37/0.99  sup_num_in_passive:                     107
% 3.37/0.99  sup_num_of_loops:                       92
% 3.37/0.99  sup_fw_superposition:                   457
% 3.37/0.99  sup_bw_superposition:                   309
% 3.37/0.99  sup_immediate_simplified:               169
% 3.37/0.99  sup_given_eliminated:                   4
% 3.37/0.99  comparisons_done:                       0
% 3.37/0.99  comparisons_avoided:                    2
% 3.37/0.99  
% 3.37/0.99  ------ Simplifications
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  sim_fw_subset_subsumed:                 3
% 3.37/0.99  sim_bw_subset_subsumed:                 3
% 3.37/0.99  sim_fw_subsumed:                        44
% 3.37/0.99  sim_bw_subsumed:                        3
% 3.37/0.99  sim_fw_subsumption_res:                 0
% 3.37/0.99  sim_bw_subsumption_res:                 0
% 3.37/0.99  sim_tautology_del:                      1
% 3.37/0.99  sim_eq_tautology_del:                   20
% 3.37/0.99  sim_eq_res_simp:                        0
% 3.37/0.99  sim_fw_demodulated:                     89
% 3.37/0.99  sim_bw_demodulated:                     31
% 3.37/0.99  sim_light_normalised:                   108
% 3.37/0.99  sim_joinable_taut:                      0
% 3.37/0.99  sim_joinable_simp:                      0
% 3.37/0.99  sim_ac_normalised:                      0
% 3.37/0.99  sim_smt_subsumption:                    0
% 3.37/0.99  
%------------------------------------------------------------------------------
