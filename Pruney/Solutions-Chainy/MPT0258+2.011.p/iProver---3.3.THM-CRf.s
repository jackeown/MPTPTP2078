%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:56 EST 2020

% Result     : Theorem 26.67s
% Output     : CNFRefutation 26.67s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 379 expanded)
%              Number of clauses        :   49 (  91 expanded)
%              Number of leaves         :   15 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  229 ( 657 expanded)
%              Number of equality atoms :  100 ( 372 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK0(X0,X1,X2),X0)
        & r1_tarski(sK0(X0,X1,X2),X2)
        & r1_tarski(sK0(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK0(X0,X1,X2),X0)
        & r1_tarski(sK0(X0,X1,X2),X2)
        & r1_tarski(sK0(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK0(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0
      | r1_tarski(sK0(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK0(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0
      | ~ r1_tarski(sK0(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2)
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK1,sK3),sK2) != k2_tarski(sK1,sK3)
      & r2_hidden(sK3,sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k3_xboole_0(k2_tarski(sK1,sK3),sK2) != k2_tarski(sK1,sK3)
    & r2_hidden(sK3,sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f26])).

fof(f47,plain,(
    k3_xboole_0(k2_tarski(sK1,sK3),sK2) != k2_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    k4_xboole_0(k1_enumset1(sK1,sK1,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK3),sK2)) != k1_enumset1(sK1,sK1,sK3) ),
    inference(definition_unfolding,[],[f47,f35,f40,f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f46,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(sK0(X0,X2,X1),X2)
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1956,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X0)
    | r1_tarski(sK0(X0,X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_2,c_9])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(sK0(X0,X2,X1),X0)
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10718,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X0)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_1956,c_0])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_495,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,k4_xboole_0(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2050,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))) = iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_495])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_493,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2641,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))) = X0
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_493])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_496,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2230,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_496])).

cnf(c_2640,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_2230])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_656,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_910,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X0),X1),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_656])).

cnf(c_2052,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X2)))) = iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_495])).

cnf(c_2065,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2052,c_5])).

cnf(c_2756,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3)) = iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2065])).

cnf(c_3352,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
    | r1_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_2756])).

cnf(c_494,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1407,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_494])).

cnf(c_1555,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1407])).

cnf(c_915,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_656,c_656])).

cnf(c_4798,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1555,c_915])).

cnf(c_2761,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2065])).

cnf(c_5950,plain,
    ( r1_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) = iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_2761])).

cnf(c_5985,plain,
    ( r1_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k1_xboole_0) = iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5950,c_915])).

cnf(c_16662,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2641,c_2640,c_3352,c_4798,c_5985])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_497,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16693,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16662,c_497])).

cnf(c_17787,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16693])).

cnf(c_498,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(sK0(X2,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_500,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(sK0(X2,X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_65339,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_500])).

cnf(c_65353,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X0)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_65339])).

cnf(c_101656,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10718,c_17787,c_65353])).

cnf(c_14,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(sK1,sK1,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK3),sK2)) != k1_enumset1(sK1,sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_101805,plain,
    ( ~ r1_tarski(k1_enumset1(sK1,sK1,sK3),sK2) ),
    inference(resolution,[status(thm)],[c_101656,c_14])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k1_enumset1(X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_102550,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_101805,c_11])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_102550,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:11:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 26.67/3.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.67/3.97  
% 26.67/3.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 26.67/3.97  
% 26.67/3.97  ------  iProver source info
% 26.67/3.97  
% 26.67/3.97  git: date: 2020-06-30 10:37:57 +0100
% 26.67/3.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 26.67/3.97  git: non_committed_changes: false
% 26.67/3.97  git: last_make_outside_of_git: false
% 26.67/3.97  
% 26.67/3.97  ------ 
% 26.67/3.97  
% 26.67/3.97  ------ Input Options
% 26.67/3.97  
% 26.67/3.97  --out_options                           all
% 26.67/3.97  --tptp_safe_out                         true
% 26.67/3.97  --problem_path                          ""
% 26.67/3.97  --include_path                          ""
% 26.67/3.97  --clausifier                            res/vclausify_rel
% 26.67/3.97  --clausifier_options                    --mode clausify
% 26.67/3.97  --stdin                                 false
% 26.67/3.97  --stats_out                             sel
% 26.67/3.97  
% 26.67/3.97  ------ General Options
% 26.67/3.97  
% 26.67/3.97  --fof                                   false
% 26.67/3.97  --time_out_real                         604.99
% 26.67/3.97  --time_out_virtual                      -1.
% 26.67/3.97  --symbol_type_check                     false
% 26.67/3.97  --clausify_out                          false
% 26.67/3.97  --sig_cnt_out                           false
% 26.67/3.97  --trig_cnt_out                          false
% 26.67/3.97  --trig_cnt_out_tolerance                1.
% 26.67/3.97  --trig_cnt_out_sk_spl                   false
% 26.67/3.97  --abstr_cl_out                          false
% 26.67/3.97  
% 26.67/3.97  ------ Global Options
% 26.67/3.97  
% 26.67/3.97  --schedule                              none
% 26.67/3.97  --add_important_lit                     false
% 26.67/3.97  --prop_solver_per_cl                    1000
% 26.67/3.97  --min_unsat_core                        false
% 26.67/3.97  --soft_assumptions                      false
% 26.67/3.97  --soft_lemma_size                       3
% 26.67/3.97  --prop_impl_unit_size                   0
% 26.67/3.97  --prop_impl_unit                        []
% 26.67/3.97  --share_sel_clauses                     true
% 26.67/3.97  --reset_solvers                         false
% 26.67/3.97  --bc_imp_inh                            [conj_cone]
% 26.67/3.97  --conj_cone_tolerance                   3.
% 26.67/3.97  --extra_neg_conj                        none
% 26.67/3.97  --large_theory_mode                     true
% 26.67/3.97  --prolific_symb_bound                   200
% 26.67/3.97  --lt_threshold                          2000
% 26.67/3.97  --clause_weak_htbl                      true
% 26.67/3.97  --gc_record_bc_elim                     false
% 26.67/3.97  
% 26.67/3.97  ------ Preprocessing Options
% 26.67/3.97  
% 26.67/3.97  --preprocessing_flag                    true
% 26.67/3.97  --time_out_prep_mult                    0.1
% 26.67/3.97  --splitting_mode                        input
% 26.67/3.97  --splitting_grd                         true
% 26.67/3.97  --splitting_cvd                         false
% 26.67/3.97  --splitting_cvd_svl                     false
% 26.67/3.97  --splitting_nvd                         32
% 26.67/3.97  --sub_typing                            true
% 26.67/3.97  --prep_gs_sim                           false
% 26.67/3.97  --prep_unflatten                        true
% 26.67/3.97  --prep_res_sim                          true
% 26.67/3.97  --prep_upred                            true
% 26.67/3.97  --prep_sem_filter                       exhaustive
% 26.67/3.97  --prep_sem_filter_out                   false
% 26.67/3.97  --pred_elim                             false
% 26.67/3.97  --res_sim_input                         true
% 26.67/3.97  --eq_ax_congr_red                       true
% 26.67/3.97  --pure_diseq_elim                       true
% 26.67/3.97  --brand_transform                       false
% 26.67/3.97  --non_eq_to_eq                          false
% 26.67/3.97  --prep_def_merge                        true
% 26.67/3.97  --prep_def_merge_prop_impl              false
% 26.67/3.97  --prep_def_merge_mbd                    true
% 26.67/3.97  --prep_def_merge_tr_red                 false
% 26.67/3.97  --prep_def_merge_tr_cl                  false
% 26.67/3.97  --smt_preprocessing                     true
% 26.67/3.97  --smt_ac_axioms                         fast
% 26.67/3.97  --preprocessed_out                      false
% 26.67/3.97  --preprocessed_stats                    false
% 26.67/3.97  
% 26.67/3.97  ------ Abstraction refinement Options
% 26.67/3.97  
% 26.67/3.97  --abstr_ref                             []
% 26.67/3.97  --abstr_ref_prep                        false
% 26.67/3.97  --abstr_ref_until_sat                   false
% 26.67/3.97  --abstr_ref_sig_restrict                funpre
% 26.67/3.97  --abstr_ref_af_restrict_to_split_sk     false
% 26.67/3.97  --abstr_ref_under                       []
% 26.67/3.97  
% 26.67/3.97  ------ SAT Options
% 26.67/3.97  
% 26.67/3.97  --sat_mode                              false
% 26.67/3.97  --sat_fm_restart_options                ""
% 26.67/3.97  --sat_gr_def                            false
% 26.67/3.97  --sat_epr_types                         true
% 26.67/3.97  --sat_non_cyclic_types                  false
% 26.67/3.97  --sat_finite_models                     false
% 26.67/3.97  --sat_fm_lemmas                         false
% 26.67/3.97  --sat_fm_prep                           false
% 26.67/3.97  --sat_fm_uc_incr                        true
% 26.67/3.97  --sat_out_model                         small
% 26.67/3.97  --sat_out_clauses                       false
% 26.67/3.97  
% 26.67/3.97  ------ QBF Options
% 26.67/3.97  
% 26.67/3.97  --qbf_mode                              false
% 26.67/3.97  --qbf_elim_univ                         false
% 26.67/3.97  --qbf_dom_inst                          none
% 26.67/3.97  --qbf_dom_pre_inst                      false
% 26.67/3.97  --qbf_sk_in                             false
% 26.67/3.97  --qbf_pred_elim                         true
% 26.67/3.97  --qbf_split                             512
% 26.67/3.97  
% 26.67/3.97  ------ BMC1 Options
% 26.67/3.97  
% 26.67/3.97  --bmc1_incremental                      false
% 26.67/3.97  --bmc1_axioms                           reachable_all
% 26.67/3.97  --bmc1_min_bound                        0
% 26.67/3.97  --bmc1_max_bound                        -1
% 26.67/3.97  --bmc1_max_bound_default                -1
% 26.67/3.97  --bmc1_symbol_reachability              true
% 26.67/3.97  --bmc1_property_lemmas                  false
% 26.67/3.97  --bmc1_k_induction                      false
% 26.67/3.97  --bmc1_non_equiv_states                 false
% 26.67/3.97  --bmc1_deadlock                         false
% 26.67/3.97  --bmc1_ucm                              false
% 26.67/3.97  --bmc1_add_unsat_core                   none
% 26.67/3.97  --bmc1_unsat_core_children              false
% 26.67/3.97  --bmc1_unsat_core_extrapolate_axioms    false
% 26.67/3.97  --bmc1_out_stat                         full
% 26.67/3.97  --bmc1_ground_init                      false
% 26.67/3.97  --bmc1_pre_inst_next_state              false
% 26.67/3.97  --bmc1_pre_inst_state                   false
% 26.67/3.97  --bmc1_pre_inst_reach_state             false
% 26.67/3.97  --bmc1_out_unsat_core                   false
% 26.67/3.97  --bmc1_aig_witness_out                  false
% 26.67/3.97  --bmc1_verbose                          false
% 26.67/3.97  --bmc1_dump_clauses_tptp                false
% 26.67/3.97  --bmc1_dump_unsat_core_tptp             false
% 26.67/3.97  --bmc1_dump_file                        -
% 26.67/3.97  --bmc1_ucm_expand_uc_limit              128
% 26.67/3.97  --bmc1_ucm_n_expand_iterations          6
% 26.67/3.97  --bmc1_ucm_extend_mode                  1
% 26.67/3.97  --bmc1_ucm_init_mode                    2
% 26.67/3.97  --bmc1_ucm_cone_mode                    none
% 26.67/3.97  --bmc1_ucm_reduced_relation_type        0
% 26.67/3.97  --bmc1_ucm_relax_model                  4
% 26.67/3.97  --bmc1_ucm_full_tr_after_sat            true
% 26.67/3.97  --bmc1_ucm_expand_neg_assumptions       false
% 26.67/3.97  --bmc1_ucm_layered_model                none
% 26.67/3.97  --bmc1_ucm_max_lemma_size               10
% 26.67/3.97  
% 26.67/3.97  ------ AIG Options
% 26.67/3.97  
% 26.67/3.97  --aig_mode                              false
% 26.67/3.97  
% 26.67/3.97  ------ Instantiation Options
% 26.67/3.97  
% 26.67/3.97  --instantiation_flag                    true
% 26.67/3.97  --inst_sos_flag                         false
% 26.67/3.97  --inst_sos_phase                        true
% 26.67/3.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 26.67/3.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 26.67/3.97  --inst_lit_sel_side                     num_symb
% 26.67/3.97  --inst_solver_per_active                1400
% 26.67/3.97  --inst_solver_calls_frac                1.
% 26.67/3.97  --inst_passive_queue_type               priority_queues
% 26.67/3.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 26.67/3.97  --inst_passive_queues_freq              [25;2]
% 26.67/3.97  --inst_dismatching                      true
% 26.67/3.97  --inst_eager_unprocessed_to_passive     true
% 26.67/3.97  --inst_prop_sim_given                   true
% 26.67/3.97  --inst_prop_sim_new                     false
% 26.67/3.97  --inst_subs_new                         false
% 26.67/3.97  --inst_eq_res_simp                      false
% 26.67/3.97  --inst_subs_given                       false
% 26.67/3.97  --inst_orphan_elimination               true
% 26.67/3.97  --inst_learning_loop_flag               true
% 26.67/3.97  --inst_learning_start                   3000
% 26.67/3.97  --inst_learning_factor                  2
% 26.67/3.97  --inst_start_prop_sim_after_learn       3
% 26.67/3.97  --inst_sel_renew                        solver
% 26.67/3.97  --inst_lit_activity_flag                true
% 26.67/3.97  --inst_restr_to_given                   false
% 26.67/3.97  --inst_activity_threshold               500
% 26.67/3.97  --inst_out_proof                        true
% 26.67/3.97  
% 26.67/3.97  ------ Resolution Options
% 26.67/3.97  
% 26.67/3.97  --resolution_flag                       true
% 26.67/3.97  --res_lit_sel                           adaptive
% 26.67/3.97  --res_lit_sel_side                      none
% 26.67/3.97  --res_ordering                          kbo
% 26.67/3.97  --res_to_prop_solver                    active
% 26.67/3.97  --res_prop_simpl_new                    false
% 26.67/3.97  --res_prop_simpl_given                  true
% 26.67/3.97  --res_passive_queue_type                priority_queues
% 26.67/3.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 26.67/3.97  --res_passive_queues_freq               [15;5]
% 26.67/3.97  --res_forward_subs                      full
% 26.67/3.97  --res_backward_subs                     full
% 26.67/3.97  --res_forward_subs_resolution           true
% 26.67/3.97  --res_backward_subs_resolution          true
% 26.67/3.97  --res_orphan_elimination                true
% 26.67/3.97  --res_time_limit                        2.
% 26.67/3.97  --res_out_proof                         true
% 26.67/3.97  
% 26.67/3.97  ------ Superposition Options
% 26.67/3.97  
% 26.67/3.97  --superposition_flag                    true
% 26.67/3.97  --sup_passive_queue_type                priority_queues
% 26.67/3.97  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 26.67/3.97  --sup_passive_queues_freq               [1;4]
% 26.67/3.97  --demod_completeness_check              fast
% 26.67/3.97  --demod_use_ground                      true
% 26.67/3.97  --sup_to_prop_solver                    passive
% 26.67/3.97  --sup_prop_simpl_new                    true
% 26.67/3.97  --sup_prop_simpl_given                  true
% 26.67/3.97  --sup_fun_splitting                     false
% 26.67/3.97  --sup_smt_interval                      50000
% 26.67/3.97  
% 26.67/3.97  ------ Superposition Simplification Setup
% 26.67/3.97  
% 26.67/3.97  --sup_indices_passive                   []
% 26.67/3.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 26.67/3.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 26.67/3.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 26.67/3.97  --sup_full_triv                         [TrivRules;PropSubs]
% 26.67/3.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 26.67/3.97  --sup_full_bw                           [BwDemod]
% 26.67/3.97  --sup_immed_triv                        [TrivRules]
% 26.67/3.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 26.67/3.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 26.67/3.97  --sup_immed_bw_main                     []
% 26.67/3.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 26.67/3.97  --sup_input_triv                        [Unflattening;TrivRules]
% 26.67/3.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 26.67/3.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 26.67/3.97  
% 26.67/3.97  ------ Combination Options
% 26.67/3.97  
% 26.67/3.97  --comb_res_mult                         3
% 26.67/3.97  --comb_sup_mult                         2
% 26.67/3.97  --comb_inst_mult                        10
% 26.67/3.97  
% 26.67/3.97  ------ Debug Options
% 26.67/3.97  
% 26.67/3.97  --dbg_backtrace                         false
% 26.67/3.97  --dbg_dump_prop_clauses                 false
% 26.67/3.97  --dbg_dump_prop_clauses_file            -
% 26.67/3.97  --dbg_out_stat                          false
% 26.67/3.97  ------ Parsing...
% 26.67/3.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 26.67/3.97  
% 26.67/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 26.67/3.97  
% 26.67/3.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 26.67/3.97  
% 26.67/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 26.67/3.97  ------ Proving...
% 26.67/3.97  ------ Problem Properties 
% 26.67/3.97  
% 26.67/3.97  
% 26.67/3.97  clauses                                 17
% 26.67/3.97  conjectures                             3
% 26.67/3.97  EPR                                     2
% 26.67/3.97  Horn                                    15
% 26.67/3.97  unary                                   7
% 26.67/3.97  binary                                  6
% 26.67/3.97  lits                                    34
% 26.67/3.97  lits eq                                 9
% 26.67/3.97  fd_pure                                 0
% 26.67/3.97  fd_pseudo                               0
% 26.67/3.97  fd_cond                                 0
% 26.67/3.97  fd_pseudo_cond                          3
% 26.67/3.97  AC symbols                              0
% 26.67/3.97  
% 26.67/3.97  ------ Input Options Time Limit: Unbounded
% 26.67/3.97  
% 26.67/3.97  
% 26.67/3.97  ------ 
% 26.67/3.97  Current options:
% 26.67/3.97  ------ 
% 26.67/3.97  
% 26.67/3.97  ------ Input Options
% 26.67/3.97  
% 26.67/3.97  --out_options                           all
% 26.67/3.97  --tptp_safe_out                         true
% 26.67/3.97  --problem_path                          ""
% 26.67/3.97  --include_path                          ""
% 26.67/3.97  --clausifier                            res/vclausify_rel
% 26.67/3.97  --clausifier_options                    --mode clausify
% 26.67/3.97  --stdin                                 false
% 26.67/3.97  --stats_out                             sel
% 26.67/3.97  
% 26.67/3.97  ------ General Options
% 26.67/3.97  
% 26.67/3.97  --fof                                   false
% 26.67/3.97  --time_out_real                         604.99
% 26.67/3.97  --time_out_virtual                      -1.
% 26.67/3.97  --symbol_type_check                     false
% 26.67/3.97  --clausify_out                          false
% 26.67/3.97  --sig_cnt_out                           false
% 26.67/3.97  --trig_cnt_out                          false
% 26.67/3.97  --trig_cnt_out_tolerance                1.
% 26.67/3.97  --trig_cnt_out_sk_spl                   false
% 26.67/3.97  --abstr_cl_out                          false
% 26.67/3.97  
% 26.67/3.97  ------ Global Options
% 26.67/3.97  
% 26.67/3.97  --schedule                              none
% 26.67/3.97  --add_important_lit                     false
% 26.67/3.97  --prop_solver_per_cl                    1000
% 26.67/3.97  --min_unsat_core                        false
% 26.67/3.97  --soft_assumptions                      false
% 26.67/3.97  --soft_lemma_size                       3
% 26.67/3.97  --prop_impl_unit_size                   0
% 26.67/3.97  --prop_impl_unit                        []
% 26.67/3.97  --share_sel_clauses                     true
% 26.67/3.97  --reset_solvers                         false
% 26.67/3.97  --bc_imp_inh                            [conj_cone]
% 26.67/3.97  --conj_cone_tolerance                   3.
% 26.67/3.97  --extra_neg_conj                        none
% 26.67/3.97  --large_theory_mode                     true
% 26.67/3.97  --prolific_symb_bound                   200
% 26.67/3.97  --lt_threshold                          2000
% 26.67/3.97  --clause_weak_htbl                      true
% 26.67/3.97  --gc_record_bc_elim                     false
% 26.67/3.97  
% 26.67/3.97  ------ Preprocessing Options
% 26.67/3.97  
% 26.67/3.97  --preprocessing_flag                    true
% 26.67/3.97  --time_out_prep_mult                    0.1
% 26.67/3.97  --splitting_mode                        input
% 26.67/3.97  --splitting_grd                         true
% 26.67/3.97  --splitting_cvd                         false
% 26.67/3.97  --splitting_cvd_svl                     false
% 26.67/3.97  --splitting_nvd                         32
% 26.67/3.97  --sub_typing                            true
% 26.67/3.97  --prep_gs_sim                           false
% 26.67/3.97  --prep_unflatten                        true
% 26.67/3.97  --prep_res_sim                          true
% 26.67/3.97  --prep_upred                            true
% 26.67/3.97  --prep_sem_filter                       exhaustive
% 26.67/3.97  --prep_sem_filter_out                   false
% 26.67/3.97  --pred_elim                             false
% 26.67/3.97  --res_sim_input                         true
% 26.67/3.97  --eq_ax_congr_red                       true
% 26.67/3.97  --pure_diseq_elim                       true
% 26.67/3.97  --brand_transform                       false
% 26.67/3.98  --non_eq_to_eq                          false
% 26.67/3.98  --prep_def_merge                        true
% 26.67/3.98  --prep_def_merge_prop_impl              false
% 26.67/3.98  --prep_def_merge_mbd                    true
% 26.67/3.98  --prep_def_merge_tr_red                 false
% 26.67/3.98  --prep_def_merge_tr_cl                  false
% 26.67/3.98  --smt_preprocessing                     true
% 26.67/3.98  --smt_ac_axioms                         fast
% 26.67/3.98  --preprocessed_out                      false
% 26.67/3.98  --preprocessed_stats                    false
% 26.67/3.98  
% 26.67/3.98  ------ Abstraction refinement Options
% 26.67/3.98  
% 26.67/3.98  --abstr_ref                             []
% 26.67/3.98  --abstr_ref_prep                        false
% 26.67/3.98  --abstr_ref_until_sat                   false
% 26.67/3.98  --abstr_ref_sig_restrict                funpre
% 26.67/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 26.67/3.98  --abstr_ref_under                       []
% 26.67/3.98  
% 26.67/3.98  ------ SAT Options
% 26.67/3.98  
% 26.67/3.98  --sat_mode                              false
% 26.67/3.98  --sat_fm_restart_options                ""
% 26.67/3.98  --sat_gr_def                            false
% 26.67/3.98  --sat_epr_types                         true
% 26.67/3.98  --sat_non_cyclic_types                  false
% 26.67/3.98  --sat_finite_models                     false
% 26.67/3.98  --sat_fm_lemmas                         false
% 26.67/3.98  --sat_fm_prep                           false
% 26.67/3.98  --sat_fm_uc_incr                        true
% 26.67/3.98  --sat_out_model                         small
% 26.67/3.98  --sat_out_clauses                       false
% 26.67/3.98  
% 26.67/3.98  ------ QBF Options
% 26.67/3.98  
% 26.67/3.98  --qbf_mode                              false
% 26.67/3.98  --qbf_elim_univ                         false
% 26.67/3.98  --qbf_dom_inst                          none
% 26.67/3.98  --qbf_dom_pre_inst                      false
% 26.67/3.98  --qbf_sk_in                             false
% 26.67/3.98  --qbf_pred_elim                         true
% 26.67/3.98  --qbf_split                             512
% 26.67/3.98  
% 26.67/3.98  ------ BMC1 Options
% 26.67/3.98  
% 26.67/3.98  --bmc1_incremental                      false
% 26.67/3.98  --bmc1_axioms                           reachable_all
% 26.67/3.98  --bmc1_min_bound                        0
% 26.67/3.98  --bmc1_max_bound                        -1
% 26.67/3.98  --bmc1_max_bound_default                -1
% 26.67/3.98  --bmc1_symbol_reachability              true
% 26.67/3.98  --bmc1_property_lemmas                  false
% 26.67/3.98  --bmc1_k_induction                      false
% 26.67/3.98  --bmc1_non_equiv_states                 false
% 26.67/3.98  --bmc1_deadlock                         false
% 26.67/3.98  --bmc1_ucm                              false
% 26.67/3.98  --bmc1_add_unsat_core                   none
% 26.67/3.98  --bmc1_unsat_core_children              false
% 26.67/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 26.67/3.98  --bmc1_out_stat                         full
% 26.67/3.98  --bmc1_ground_init                      false
% 26.67/3.98  --bmc1_pre_inst_next_state              false
% 26.67/3.98  --bmc1_pre_inst_state                   false
% 26.67/3.98  --bmc1_pre_inst_reach_state             false
% 26.67/3.98  --bmc1_out_unsat_core                   false
% 26.67/3.98  --bmc1_aig_witness_out                  false
% 26.67/3.98  --bmc1_verbose                          false
% 26.67/3.98  --bmc1_dump_clauses_tptp                false
% 26.67/3.98  --bmc1_dump_unsat_core_tptp             false
% 26.67/3.98  --bmc1_dump_file                        -
% 26.67/3.98  --bmc1_ucm_expand_uc_limit              128
% 26.67/3.98  --bmc1_ucm_n_expand_iterations          6
% 26.67/3.98  --bmc1_ucm_extend_mode                  1
% 26.67/3.98  --bmc1_ucm_init_mode                    2
% 26.67/3.98  --bmc1_ucm_cone_mode                    none
% 26.67/3.98  --bmc1_ucm_reduced_relation_type        0
% 26.67/3.98  --bmc1_ucm_relax_model                  4
% 26.67/3.98  --bmc1_ucm_full_tr_after_sat            true
% 26.67/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 26.67/3.98  --bmc1_ucm_layered_model                none
% 26.67/3.98  --bmc1_ucm_max_lemma_size               10
% 26.67/3.98  
% 26.67/3.98  ------ AIG Options
% 26.67/3.98  
% 26.67/3.98  --aig_mode                              false
% 26.67/3.98  
% 26.67/3.98  ------ Instantiation Options
% 26.67/3.98  
% 26.67/3.98  --instantiation_flag                    true
% 26.67/3.98  --inst_sos_flag                         false
% 26.67/3.98  --inst_sos_phase                        true
% 26.67/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 26.67/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 26.67/3.98  --inst_lit_sel_side                     num_symb
% 26.67/3.98  --inst_solver_per_active                1400
% 26.67/3.98  --inst_solver_calls_frac                1.
% 26.67/3.98  --inst_passive_queue_type               priority_queues
% 26.67/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 26.67/3.98  --inst_passive_queues_freq              [25;2]
% 26.67/3.98  --inst_dismatching                      true
% 26.67/3.98  --inst_eager_unprocessed_to_passive     true
% 26.67/3.98  --inst_prop_sim_given                   true
% 26.67/3.98  --inst_prop_sim_new                     false
% 26.67/3.98  --inst_subs_new                         false
% 26.67/3.98  --inst_eq_res_simp                      false
% 26.67/3.98  --inst_subs_given                       false
% 26.67/3.98  --inst_orphan_elimination               true
% 26.67/3.98  --inst_learning_loop_flag               true
% 26.67/3.98  --inst_learning_start                   3000
% 26.67/3.98  --inst_learning_factor                  2
% 26.67/3.98  --inst_start_prop_sim_after_learn       3
% 26.67/3.98  --inst_sel_renew                        solver
% 26.67/3.98  --inst_lit_activity_flag                true
% 26.67/3.98  --inst_restr_to_given                   false
% 26.67/3.98  --inst_activity_threshold               500
% 26.67/3.98  --inst_out_proof                        true
% 26.67/3.98  
% 26.67/3.98  ------ Resolution Options
% 26.67/3.98  
% 26.67/3.98  --resolution_flag                       true
% 26.67/3.98  --res_lit_sel                           adaptive
% 26.67/3.98  --res_lit_sel_side                      none
% 26.67/3.98  --res_ordering                          kbo
% 26.67/3.98  --res_to_prop_solver                    active
% 26.67/3.98  --res_prop_simpl_new                    false
% 26.67/3.98  --res_prop_simpl_given                  true
% 26.67/3.98  --res_passive_queue_type                priority_queues
% 26.67/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 26.67/3.98  --res_passive_queues_freq               [15;5]
% 26.67/3.98  --res_forward_subs                      full
% 26.67/3.98  --res_backward_subs                     full
% 26.67/3.98  --res_forward_subs_resolution           true
% 26.67/3.98  --res_backward_subs_resolution          true
% 26.67/3.98  --res_orphan_elimination                true
% 26.67/3.98  --res_time_limit                        2.
% 26.67/3.98  --res_out_proof                         true
% 26.67/3.98  
% 26.67/3.98  ------ Superposition Options
% 26.67/3.98  
% 26.67/3.98  --superposition_flag                    true
% 26.67/3.98  --sup_passive_queue_type                priority_queues
% 26.67/3.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 26.67/3.98  --sup_passive_queues_freq               [1;4]
% 26.67/3.98  --demod_completeness_check              fast
% 26.67/3.98  --demod_use_ground                      true
% 26.67/3.98  --sup_to_prop_solver                    passive
% 26.67/3.98  --sup_prop_simpl_new                    true
% 26.67/3.98  --sup_prop_simpl_given                  true
% 26.67/3.98  --sup_fun_splitting                     false
% 26.67/3.98  --sup_smt_interval                      50000
% 26.67/3.98  
% 26.67/3.98  ------ Superposition Simplification Setup
% 26.67/3.98  
% 26.67/3.98  --sup_indices_passive                   []
% 26.67/3.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 26.67/3.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 26.67/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 26.67/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 26.67/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 26.67/3.98  --sup_full_bw                           [BwDemod]
% 26.67/3.98  --sup_immed_triv                        [TrivRules]
% 26.67/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 26.67/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 26.67/3.98  --sup_immed_bw_main                     []
% 26.67/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 26.67/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 26.67/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 26.67/3.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 26.67/3.98  
% 26.67/3.98  ------ Combination Options
% 26.67/3.98  
% 26.67/3.98  --comb_res_mult                         3
% 26.67/3.98  --comb_sup_mult                         2
% 26.67/3.98  --comb_inst_mult                        10
% 26.67/3.98  
% 26.67/3.98  ------ Debug Options
% 26.67/3.98  
% 26.67/3.98  --dbg_backtrace                         false
% 26.67/3.98  --dbg_dump_prop_clauses                 false
% 26.67/3.98  --dbg_dump_prop_clauses_file            -
% 26.67/3.98  --dbg_out_stat                          false
% 26.67/3.98  
% 26.67/3.98  
% 26.67/3.98  
% 26.67/3.98  
% 26.67/3.98  ------ Proving...
% 26.67/3.98  
% 26.67/3.98  
% 26.67/3.98  % SZS status Theorem for theBenchmark.p
% 26.67/3.98  
% 26.67/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 26.67/3.98  
% 26.67/3.98  fof(f1,axiom,(
% 26.67/3.98    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f15,plain,(
% 26.67/3.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 26.67/3.98    inference(ennf_transformation,[],[f1])).
% 26.67/3.98  
% 26.67/3.98  fof(f16,plain,(
% 26.67/3.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 26.67/3.98    inference(flattening,[],[f15])).
% 26.67/3.98  
% 26.67/3.98  fof(f21,plain,(
% 26.67/3.98    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK0(X0,X1,X2),X0) & r1_tarski(sK0(X0,X1,X2),X2) & r1_tarski(sK0(X0,X1,X2),X1)))),
% 26.67/3.98    introduced(choice_axiom,[])).
% 26.67/3.98  
% 26.67/3.98  fof(f22,plain,(
% 26.67/3.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK0(X0,X1,X2),X0) & r1_tarski(sK0(X0,X1,X2),X2) & r1_tarski(sK0(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 26.67/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f21])).
% 26.67/3.98  
% 26.67/3.98  fof(f28,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK0(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 26.67/3.98    inference(cnf_transformation,[],[f22])).
% 26.67/3.98  
% 26.67/3.98  fof(f6,axiom,(
% 26.67/3.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f35,plain,(
% 26.67/3.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 26.67/3.98    inference(cnf_transformation,[],[f6])).
% 26.67/3.98  
% 26.67/3.98  fof(f51,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0 | r1_tarski(sK0(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 26.67/3.98    inference(definition_unfolding,[],[f28,f35])).
% 26.67/3.98  
% 26.67/3.98  fof(f9,axiom,(
% 26.67/3.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f23,plain,(
% 26.67/3.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 26.67/3.98    inference(nnf_transformation,[],[f9])).
% 26.67/3.98  
% 26.67/3.98  fof(f39,plain,(
% 26.67/3.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 26.67/3.98    inference(cnf_transformation,[],[f23])).
% 26.67/3.98  
% 26.67/3.98  fof(f30,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK0(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 26.67/3.98    inference(cnf_transformation,[],[f22])).
% 26.67/3.98  
% 26.67/3.98  fof(f49,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0 | ~r1_tarski(sK0(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 26.67/3.98    inference(definition_unfolding,[],[f30,f35])).
% 26.67/3.98  
% 26.67/3.98  fof(f2,axiom,(
% 26.67/3.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f31,plain,(
% 26.67/3.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 26.67/3.98    inference(cnf_transformation,[],[f2])).
% 26.67/3.98  
% 26.67/3.98  fof(f52,plain,(
% 26.67/3.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 26.67/3.98    inference(definition_unfolding,[],[f31,f35])).
% 26.67/3.98  
% 26.67/3.98  fof(f8,axiom,(
% 26.67/3.98    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f18,plain,(
% 26.67/3.98    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 26.67/3.98    inference(ennf_transformation,[],[f8])).
% 26.67/3.98  
% 26.67/3.98  fof(f37,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 26.67/3.98    inference(cnf_transformation,[],[f18])).
% 26.67/3.98  
% 26.67/3.98  fof(f38,plain,(
% 26.67/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 26.67/3.98    inference(cnf_transformation,[],[f23])).
% 26.67/3.98  
% 26.67/3.98  fof(f7,axiom,(
% 26.67/3.98    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f17,plain,(
% 26.67/3.98    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 26.67/3.98    inference(ennf_transformation,[],[f7])).
% 26.67/3.98  
% 26.67/3.98  fof(f36,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 26.67/3.98    inference(cnf_transformation,[],[f17])).
% 26.67/3.98  
% 26.67/3.98  fof(f55,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 26.67/3.98    inference(definition_unfolding,[],[f36,f35])).
% 26.67/3.98  
% 26.67/3.98  fof(f4,axiom,(
% 26.67/3.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f33,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 26.67/3.98    inference(cnf_transformation,[],[f4])).
% 26.67/3.98  
% 26.67/3.98  fof(f11,axiom,(
% 26.67/3.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f41,plain,(
% 26.67/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 26.67/3.98    inference(cnf_transformation,[],[f11])).
% 26.67/3.98  
% 26.67/3.98  fof(f10,axiom,(
% 26.67/3.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f40,plain,(
% 26.67/3.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 26.67/3.98    inference(cnf_transformation,[],[f10])).
% 26.67/3.98  
% 26.67/3.98  fof(f48,plain,(
% 26.67/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 26.67/3.98    inference(definition_unfolding,[],[f41,f40])).
% 26.67/3.98  
% 26.67/3.98  fof(f53,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 26.67/3.98    inference(definition_unfolding,[],[f33,f48])).
% 26.67/3.98  
% 26.67/3.98  fof(f5,axiom,(
% 26.67/3.98    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f34,plain,(
% 26.67/3.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 26.67/3.98    inference(cnf_transformation,[],[f5])).
% 26.67/3.98  
% 26.67/3.98  fof(f54,plain,(
% 26.67/3.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 26.67/3.98    inference(definition_unfolding,[],[f34,f48])).
% 26.67/3.98  
% 26.67/3.98  fof(f3,axiom,(
% 26.67/3.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f32,plain,(
% 26.67/3.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 26.67/3.98    inference(cnf_transformation,[],[f3])).
% 26.67/3.98  
% 26.67/3.98  fof(f13,conjecture,(
% 26.67/3.98    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2))),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f14,negated_conjecture,(
% 26.67/3.98    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2))),
% 26.67/3.98    inference(negated_conjecture,[],[f13])).
% 26.67/3.98  
% 26.67/3.98  fof(f19,plain,(
% 26.67/3.98    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2) & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 26.67/3.98    inference(ennf_transformation,[],[f14])).
% 26.67/3.98  
% 26.67/3.98  fof(f20,plain,(
% 26.67/3.98    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2) & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 26.67/3.98    inference(flattening,[],[f19])).
% 26.67/3.98  
% 26.67/3.98  fof(f26,plain,(
% 26.67/3.98    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2) & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k3_xboole_0(k2_tarski(sK1,sK3),sK2) != k2_tarski(sK1,sK3) & r2_hidden(sK3,sK2) & r2_hidden(sK1,sK2))),
% 26.67/3.98    introduced(choice_axiom,[])).
% 26.67/3.98  
% 26.67/3.98  fof(f27,plain,(
% 26.67/3.98    k3_xboole_0(k2_tarski(sK1,sK3),sK2) != k2_tarski(sK1,sK3) & r2_hidden(sK3,sK2) & r2_hidden(sK1,sK2)),
% 26.67/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f26])).
% 26.67/3.98  
% 26.67/3.98  fof(f47,plain,(
% 26.67/3.98    k3_xboole_0(k2_tarski(sK1,sK3),sK2) != k2_tarski(sK1,sK3)),
% 26.67/3.98    inference(cnf_transformation,[],[f27])).
% 26.67/3.98  
% 26.67/3.98  fof(f59,plain,(
% 26.67/3.98    k4_xboole_0(k1_enumset1(sK1,sK1,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK3),sK2)) != k1_enumset1(sK1,sK1,sK3)),
% 26.67/3.98    inference(definition_unfolding,[],[f47,f35,f40,f40])).
% 26.67/3.98  
% 26.67/3.98  fof(f12,axiom,(
% 26.67/3.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 26.67/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.67/3.98  
% 26.67/3.98  fof(f24,plain,(
% 26.67/3.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 26.67/3.98    inference(nnf_transformation,[],[f12])).
% 26.67/3.98  
% 26.67/3.98  fof(f25,plain,(
% 26.67/3.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 26.67/3.98    inference(flattening,[],[f24])).
% 26.67/3.98  
% 26.67/3.98  fof(f44,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 26.67/3.98    inference(cnf_transformation,[],[f25])).
% 26.67/3.98  
% 26.67/3.98  fof(f56,plain,(
% 26.67/3.98    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 26.67/3.98    inference(definition_unfolding,[],[f44,f40])).
% 26.67/3.98  
% 26.67/3.98  fof(f46,plain,(
% 26.67/3.98    r2_hidden(sK3,sK2)),
% 26.67/3.98    inference(cnf_transformation,[],[f27])).
% 26.67/3.98  
% 26.67/3.98  fof(f45,plain,(
% 26.67/3.98    r2_hidden(sK1,sK2)),
% 26.67/3.98    inference(cnf_transformation,[],[f27])).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2,plain,
% 26.67/3.98      ( ~ r1_tarski(X0,X1)
% 26.67/3.98      | ~ r1_tarski(X0,X2)
% 26.67/3.98      | r1_tarski(sK0(X0,X2,X1),X2)
% 26.67/3.98      | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
% 26.67/3.98      inference(cnf_transformation,[],[f51]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_9,plain,
% 26.67/3.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 26.67/3.98      inference(cnf_transformation,[],[f39]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_1956,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k4_xboole_0(X0,X1))
% 26.67/3.98      | ~ r1_tarski(X0,X1)
% 26.67/3.98      | ~ r1_tarski(X0,X0)
% 26.67/3.98      | r1_tarski(sK0(X0,X0,X1),X0) ),
% 26.67/3.98      inference(resolution,[status(thm)],[c_2,c_9]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_0,plain,
% 26.67/3.98      ( ~ r1_tarski(X0,X1)
% 26.67/3.98      | ~ r1_tarski(X0,X2)
% 26.67/3.98      | ~ r1_tarski(sK0(X0,X2,X1),X0)
% 26.67/3.98      | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
% 26.67/3.98      inference(cnf_transformation,[],[f49]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_10718,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k4_xboole_0(X0,X1))
% 26.67/3.98      | ~ r1_tarski(X0,X1)
% 26.67/3.98      | ~ r1_tarski(X0,X0)
% 26.67/3.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 26.67/3.98      inference(resolution,[status(thm)],[c_1956,c_0]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_3,plain,
% 26.67/3.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 26.67/3.98      inference(cnf_transformation,[],[f52]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_8,plain,
% 26.67/3.98      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 26.67/3.98      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 26.67/3.98      inference(cnf_transformation,[],[f37]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_495,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) != iProver_top
% 26.67/3.98      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) = iProver_top ),
% 26.67/3.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2050,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))) = iProver_top
% 26.67/3.98      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_3,c_495]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_10,plain,
% 26.67/3.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 26.67/3.98      inference(cnf_transformation,[],[f38]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_493,plain,
% 26.67/3.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 26.67/3.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2641,plain,
% 26.67/3.98      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))) = X0
% 26.67/3.98      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_2050,c_493]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_7,plain,
% 26.67/3.98      ( ~ r1_xboole_0(X0,X1)
% 26.67/3.98      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 26.67/3.98      inference(cnf_transformation,[],[f55]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_496,plain,
% 26.67/3.98      ( r1_xboole_0(X0,X1) != iProver_top
% 26.67/3.98      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
% 26.67/3.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2230,plain,
% 26.67/3.98      ( r1_xboole_0(X0,X1) != iProver_top
% 26.67/3.98      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_3,c_496]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2640,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 26.67/3.98      | r1_xboole_0(X1,k1_xboole_0) = iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_2050,c_2230]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_5,plain,
% 26.67/3.98      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 26.67/3.98      inference(cnf_transformation,[],[f53]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_6,plain,
% 26.67/3.98      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
% 26.67/3.98      inference(cnf_transformation,[],[f54]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_656,plain,
% 26.67/3.98      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_910,plain,
% 26.67/3.98      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X0),X1),X2) = k1_xboole_0 ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_5,c_656]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2052,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k4_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X2)))) = iProver_top
% 26.67/3.98      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_6,c_495]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2065,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = iProver_top
% 26.67/3.98      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 26.67/3.98      inference(demodulation,[status(thm)],[c_2052,c_5]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2756,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3)) = iProver_top
% 26.67/3.98      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_5,c_2065]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_3352,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
% 26.67/3.98      | r1_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k1_xboole_0) != iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_910,c_2756]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_494,plain,
% 26.67/3.98      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 26.67/3.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_1407,plain,
% 26.67/3.98      ( k1_xboole_0 != X0
% 26.67/3.98      | r1_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_3,c_494]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_1555,plain,
% 26.67/3.98      ( r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 26.67/3.98      inference(equality_resolution,[status(thm)],[c_1407]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_915,plain,
% 26.67/3.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_656,c_656]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_4798,plain,
% 26.67/3.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 26.67/3.98      inference(demodulation,[status(thm)],[c_1555,c_915]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_2761,plain,
% 26.67/3.98      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 26.67/3.98      | r1_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_5,c_2065]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_5950,plain,
% 26.67/3.98      ( r1_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) = iProver_top
% 26.67/3.98      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_915,c_2761]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_5985,plain,
% 26.67/3.98      ( r1_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k1_xboole_0) = iProver_top
% 26.67/3.98      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 26.67/3.98      inference(demodulation,[status(thm)],[c_5950,c_915]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_16662,plain,
% 26.67/3.98      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
% 26.67/3.98      inference(global_propositional_subsumption,
% 26.67/3.98                [status(thm)],
% 26.67/3.98                [c_2641,c_2640,c_3352,c_4798,c_5985]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_4,plain,
% 26.67/3.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 26.67/3.98      inference(cnf_transformation,[],[f32]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_497,plain,
% 26.67/3.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 26.67/3.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_16693,plain,
% 26.67/3.98      ( r1_tarski(X0,X0) = iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_16662,c_497]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_17787,plain,
% 26.67/3.98      ( r1_tarski(X0,X0) ),
% 26.67/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_16693]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_498,plain,
% 26.67/3.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 26.67/3.98      | r1_tarski(X2,X1) != iProver_top
% 26.67/3.98      | r1_tarski(X2,X0) != iProver_top
% 26.67/3.98      | r1_tarski(sK0(X2,X0,X1),X0) = iProver_top ),
% 26.67/3.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_500,plain,
% 26.67/3.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 26.67/3.98      | r1_tarski(X2,X1) != iProver_top
% 26.67/3.98      | r1_tarski(X2,X0) != iProver_top
% 26.67/3.98      | r1_tarski(sK0(X2,X0,X1),X2) != iProver_top ),
% 26.67/3.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_65339,plain,
% 26.67/3.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 26.67/3.98      | r1_tarski(X0,X1) != iProver_top
% 26.67/3.98      | r1_tarski(X0,X0) != iProver_top ),
% 26.67/3.98      inference(superposition,[status(thm)],[c_498,c_500]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_65353,plain,
% 26.67/3.98      ( ~ r1_tarski(X0,X1)
% 26.67/3.98      | ~ r1_tarski(X0,X0)
% 26.67/3.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 26.67/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_65339]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_101656,plain,
% 26.67/3.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 26.67/3.98      inference(global_propositional_subsumption,
% 26.67/3.98                [status(thm)],
% 26.67/3.98                [c_10718,c_17787,c_65353]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_14,negated_conjecture,
% 26.67/3.98      ( k4_xboole_0(k1_enumset1(sK1,sK1,sK3),k4_xboole_0(k1_enumset1(sK1,sK1,sK3),sK2)) != k1_enumset1(sK1,sK1,sK3) ),
% 26.67/3.98      inference(cnf_transformation,[],[f59]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_101805,plain,
% 26.67/3.98      ( ~ r1_tarski(k1_enumset1(sK1,sK1,sK3),sK2) ),
% 26.67/3.98      inference(resolution,[status(thm)],[c_101656,c_14]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_11,plain,
% 26.67/3.98      ( ~ r2_hidden(X0,X1)
% 26.67/3.98      | ~ r2_hidden(X2,X1)
% 26.67/3.98      | r1_tarski(k1_enumset1(X2,X2,X0),X1) ),
% 26.67/3.98      inference(cnf_transformation,[],[f56]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_102550,plain,
% 26.67/3.98      ( ~ r2_hidden(sK3,sK2) | ~ r2_hidden(sK1,sK2) ),
% 26.67/3.98      inference(resolution,[status(thm)],[c_101805,c_11]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_15,negated_conjecture,
% 26.67/3.98      ( r2_hidden(sK3,sK2) ),
% 26.67/3.98      inference(cnf_transformation,[],[f46]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(c_16,negated_conjecture,
% 26.67/3.98      ( r2_hidden(sK1,sK2) ),
% 26.67/3.98      inference(cnf_transformation,[],[f45]) ).
% 26.67/3.98  
% 26.67/3.98  cnf(contradiction,plain,
% 26.67/3.98      ( $false ),
% 26.67/3.98      inference(minisat,[status(thm)],[c_102550,c_15,c_16]) ).
% 26.67/3.98  
% 26.67/3.98  
% 26.67/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 26.67/3.98  
% 26.67/3.98  ------                               Statistics
% 26.67/3.98  
% 26.67/3.98  ------ Selected
% 26.67/3.98  
% 26.67/3.98  total_time:                             3.23
% 26.67/3.98  
%------------------------------------------------------------------------------
