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
% DateTime   : Thu Dec  3 11:23:29 EST 2020

% Result     : Theorem 31.83s
% Output     : CNFRefutation 31.83s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 559 expanded)
%              Number of clauses        :   64 ( 197 expanded)
%              Number of leaves         :   16 ( 141 expanded)
%              Depth                    :   19
%              Number of atoms          :  180 ( 911 expanded)
%              Number of equality atoms :  110 ( 574 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK2
      & r1_xboole_0(sK3,sK4)
      & r1_tarski(sK2,sK4)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k1_xboole_0 != sK2
    & r1_xboole_0(sK3,sK4)
    & r1_tarski(sK2,sK4)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f26])).

fof(f43,plain,(
    r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f23])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f21])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f41,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_414,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_418,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_420,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2514,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_418,c_420])).

cnf(c_140377,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_414,c_2514])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_434,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_9])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_859,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_10,c_11])).

cnf(c_878,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_859,c_11])).

cnf(c_7368,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_434,c_878])).

cnf(c_7613,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7368,c_9])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_412,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_417,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1491,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_412,c_417])).

cnf(c_2022,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1491,c_11])).

cnf(c_864,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_434,c_11])).

cnf(c_866,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_864,c_9])).

cnf(c_1048,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_434,c_866])).

cnf(c_1053,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1048,c_9,c_434])).

cnf(c_2032,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_2022,c_1053])).

cnf(c_13362,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))))) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_7613,c_2032])).

cnf(c_13400,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13362,c_1491])).

cnf(c_14529,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))))) = k2_xboole_0(k4_xboole_0(sK2,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13400,c_11])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15283,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))))) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_14529,c_4])).

cnf(c_863,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_10,c_11])).

cnf(c_868,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_863,c_11])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_413,plain,
    ( r1_tarski(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1490,plain,
    ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_413,c_417])).

cnf(c_861,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_10,c_11])).

cnf(c_4737,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,X0))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1490,c_861])).

cnf(c_1985,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_1490,c_11])).

cnf(c_1995,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK4,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_1985,c_1053])).

cnf(c_4838,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_4737,c_1053,c_1995])).

cnf(c_5625,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))) ),
    inference(superposition,[status(thm)],[c_868,c_4838])).

cnf(c_5730,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_5625,c_4838])).

cnf(c_119933,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = k4_xboole_0(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_15283,c_5730])).

cnf(c_120030,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_119933,c_1490])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_416,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_120728,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_120030,c_416])).

cnf(c_140930,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_140377,c_120728])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_415,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_845,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_415])).

cnf(c_4205,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_845])).

cnf(c_4252,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4205,c_1491])).

cnf(c_4253,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4252,c_9])).

cnf(c_136,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_524,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_525,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_135,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_148,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_140930,c_4253,c_525,c_148,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:59:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.83/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.83/4.50  
% 31.83/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.83/4.50  
% 31.83/4.50  ------  iProver source info
% 31.83/4.50  
% 31.83/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.83/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.83/4.50  git: non_committed_changes: false
% 31.83/4.50  git: last_make_outside_of_git: false
% 31.83/4.50  
% 31.83/4.50  ------ 
% 31.83/4.50  ------ Parsing...
% 31.83/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.83/4.50  
% 31.83/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 31.83/4.50  
% 31.83/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.83/4.50  
% 31.83/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.83/4.50  ------ Proving...
% 31.83/4.50  ------ Problem Properties 
% 31.83/4.50  
% 31.83/4.50  
% 31.83/4.50  clauses                                 16
% 31.83/4.50  conjectures                             4
% 31.83/4.50  EPR                                     5
% 31.83/4.50  Horn                                    14
% 31.83/4.50  unary                                   9
% 31.83/4.50  binary                                  7
% 31.83/4.50  lits                                    23
% 31.83/4.50  lits eq                                 10
% 31.83/4.50  fd_pure                                 0
% 31.83/4.50  fd_pseudo                               0
% 31.83/4.50  fd_cond                                 2
% 31.83/4.50  fd_pseudo_cond                          0
% 31.83/4.50  AC symbols                              0
% 31.83/4.50  
% 31.83/4.50  ------ Input Options Time Limit: Unbounded
% 31.83/4.50  
% 31.83/4.50  
% 31.83/4.50  ------ 
% 31.83/4.50  Current options:
% 31.83/4.50  ------ 
% 31.83/4.50  
% 31.83/4.50  
% 31.83/4.50  
% 31.83/4.50  
% 31.83/4.50  ------ Proving...
% 31.83/4.50  
% 31.83/4.50  
% 31.83/4.50  % SZS status Theorem for theBenchmark.p
% 31.83/4.50  
% 31.83/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.83/4.50  
% 31.83/4.50  fof(f12,conjecture,(
% 31.83/4.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f13,negated_conjecture,(
% 31.83/4.50    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 31.83/4.50    inference(negated_conjecture,[],[f12])).
% 31.83/4.50  
% 31.83/4.50  fof(f19,plain,(
% 31.83/4.50    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 31.83/4.50    inference(ennf_transformation,[],[f13])).
% 31.83/4.50  
% 31.83/4.50  fof(f20,plain,(
% 31.83/4.50    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 31.83/4.50    inference(flattening,[],[f19])).
% 31.83/4.50  
% 31.83/4.50  fof(f26,plain,(
% 31.83/4.50    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => (k1_xboole_0 != sK2 & r1_xboole_0(sK3,sK4) & r1_tarski(sK2,sK4) & r1_tarski(sK2,sK3))),
% 31.83/4.50    introduced(choice_axiom,[])).
% 31.83/4.50  
% 31.83/4.50  fof(f27,plain,(
% 31.83/4.50    k1_xboole_0 != sK2 & r1_xboole_0(sK3,sK4) & r1_tarski(sK2,sK4) & r1_tarski(sK2,sK3)),
% 31.83/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f26])).
% 31.83/4.50  
% 31.83/4.50  fof(f43,plain,(
% 31.83/4.50    r1_xboole_0(sK3,sK4)),
% 31.83/4.50    inference(cnf_transformation,[],[f27])).
% 31.83/4.50  
% 31.83/4.50  fof(f3,axiom,(
% 31.83/4.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f17,plain,(
% 31.83/4.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 31.83/4.50    inference(ennf_transformation,[],[f3])).
% 31.83/4.50  
% 31.83/4.50  fof(f23,plain,(
% 31.83/4.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 31.83/4.50    introduced(choice_axiom,[])).
% 31.83/4.50  
% 31.83/4.50  fof(f24,plain,(
% 31.83/4.50    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 31.83/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f23])).
% 31.83/4.50  
% 31.83/4.50  fof(f31,plain,(
% 31.83/4.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 31.83/4.50    inference(cnf_transformation,[],[f24])).
% 31.83/4.50  
% 31.83/4.50  fof(f2,axiom,(
% 31.83/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f14,plain,(
% 31.83/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 31.83/4.50    inference(rectify,[],[f2])).
% 31.83/4.50  
% 31.83/4.50  fof(f16,plain,(
% 31.83/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 31.83/4.50    inference(ennf_transformation,[],[f14])).
% 31.83/4.50  
% 31.83/4.50  fof(f21,plain,(
% 31.83/4.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 31.83/4.50    introduced(choice_axiom,[])).
% 31.83/4.50  
% 31.83/4.50  fof(f22,plain,(
% 31.83/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 31.83/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f21])).
% 31.83/4.50  
% 31.83/4.50  fof(f30,plain,(
% 31.83/4.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 31.83/4.50    inference(cnf_transformation,[],[f22])).
% 31.83/4.50  
% 31.83/4.50  fof(f10,axiom,(
% 31.83/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f39,plain,(
% 31.83/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.83/4.50    inference(cnf_transformation,[],[f10])).
% 31.83/4.50  
% 31.83/4.50  fof(f45,plain,(
% 31.83/4.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 31.83/4.50    inference(definition_unfolding,[],[f30,f39])).
% 31.83/4.50  
% 31.83/4.50  fof(f5,axiom,(
% 31.83/4.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f33,plain,(
% 31.83/4.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 31.83/4.50    inference(cnf_transformation,[],[f5])).
% 31.83/4.50  
% 31.83/4.50  fof(f47,plain,(
% 31.83/4.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 31.83/4.50    inference(definition_unfolding,[],[f33,f39])).
% 31.83/4.50  
% 31.83/4.50  fof(f8,axiom,(
% 31.83/4.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f37,plain,(
% 31.83/4.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.83/4.50    inference(cnf_transformation,[],[f8])).
% 31.83/4.50  
% 31.83/4.50  fof(f9,axiom,(
% 31.83/4.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f38,plain,(
% 31.83/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.83/4.50    inference(cnf_transformation,[],[f9])).
% 31.83/4.50  
% 31.83/4.50  fof(f48,plain,(
% 31.83/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 31.83/4.50    inference(definition_unfolding,[],[f38,f39])).
% 31.83/4.50  
% 31.83/4.50  fof(f11,axiom,(
% 31.83/4.50    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f40,plain,(
% 31.83/4.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 31.83/4.50    inference(cnf_transformation,[],[f11])).
% 31.83/4.50  
% 31.83/4.50  fof(f49,plain,(
% 31.83/4.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 31.83/4.50    inference(definition_unfolding,[],[f40,f39])).
% 31.83/4.50  
% 31.83/4.50  fof(f41,plain,(
% 31.83/4.50    r1_tarski(sK2,sK3)),
% 31.83/4.50    inference(cnf_transformation,[],[f27])).
% 31.83/4.50  
% 31.83/4.50  fof(f6,axiom,(
% 31.83/4.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f25,plain,(
% 31.83/4.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 31.83/4.50    inference(nnf_transformation,[],[f6])).
% 31.83/4.50  
% 31.83/4.50  fof(f35,plain,(
% 31.83/4.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 31.83/4.50    inference(cnf_transformation,[],[f25])).
% 31.83/4.50  
% 31.83/4.50  fof(f4,axiom,(
% 31.83/4.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f32,plain,(
% 31.83/4.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.83/4.50    inference(cnf_transformation,[],[f4])).
% 31.83/4.50  
% 31.83/4.50  fof(f42,plain,(
% 31.83/4.50    r1_tarski(sK2,sK4)),
% 31.83/4.50    inference(cnf_transformation,[],[f27])).
% 31.83/4.50  
% 31.83/4.50  fof(f34,plain,(
% 31.83/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 31.83/4.50    inference(cnf_transformation,[],[f25])).
% 31.83/4.50  
% 31.83/4.50  fof(f7,axiom,(
% 31.83/4.50    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 31.83/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.83/4.50  
% 31.83/4.50  fof(f18,plain,(
% 31.83/4.50    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 31.83/4.50    inference(ennf_transformation,[],[f7])).
% 31.83/4.50  
% 31.83/4.50  fof(f36,plain,(
% 31.83/4.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 31.83/4.50    inference(cnf_transformation,[],[f18])).
% 31.83/4.50  
% 31.83/4.50  fof(f44,plain,(
% 31.83/4.50    k1_xboole_0 != sK2),
% 31.83/4.50    inference(cnf_transformation,[],[f27])).
% 31.83/4.50  
% 31.83/4.50  cnf(c_13,negated_conjecture,
% 31.83/4.50      ( r1_xboole_0(sK3,sK4) ),
% 31.83/4.50      inference(cnf_transformation,[],[f43]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_414,plain,
% 31.83/4.50      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 31.83/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_3,plain,
% 31.83/4.50      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 31.83/4.50      inference(cnf_transformation,[],[f31]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_418,plain,
% 31.83/4.50      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 31.83/4.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_1,plain,
% 31.83/4.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 31.83/4.50      | ~ r1_xboole_0(X1,X2) ),
% 31.83/4.50      inference(cnf_transformation,[],[f45]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_420,plain,
% 31.83/4.50      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 31.83/4.50      | r1_xboole_0(X1,X2) != iProver_top ),
% 31.83/4.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_2514,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 31.83/4.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_418,c_420]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_140377,plain,
% 31.83/4.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k1_xboole_0 ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_414,c_2514]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_5,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 31.83/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_9,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.83/4.50      inference(cnf_transformation,[],[f37]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_434,plain,
% 31.83/4.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_5,c_9]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_10,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.83/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_11,plain,
% 31.83/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 31.83/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_859,plain,
% 31.83/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_10,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_878,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_859,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_7368,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_434,c_878]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_7613,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_7368,c_9]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_15,negated_conjecture,
% 31.83/4.50      ( r1_tarski(sK2,sK3) ),
% 31.83/4.50      inference(cnf_transformation,[],[f41]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_412,plain,
% 31.83/4.50      ( r1_tarski(sK2,sK3) = iProver_top ),
% 31.83/4.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_6,plain,
% 31.83/4.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 31.83/4.50      inference(cnf_transformation,[],[f35]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_417,plain,
% 31.83/4.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 31.83/4.50      | r1_tarski(X0,X1) != iProver_top ),
% 31.83/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_1491,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_412,c_417]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_2022,plain,
% 31.83/4.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_1491,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_864,plain,
% 31.83/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_434,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_866,plain,
% 31.83/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_864,c_9]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_1048,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_434,c_866]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_1053,plain,
% 31.83/4.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_1048,c_9,c_434]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_2032,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 31.83/4.50      inference(demodulation,[status(thm)],[c_2022,c_1053]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_13362,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))))) = k4_xboole_0(sK2,sK3) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_7613,c_2032]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_13400,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))))) = k1_xboole_0 ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_13362,c_1491]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_14529,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))))) = k2_xboole_0(k4_xboole_0(sK2,X0),k1_xboole_0) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_13400,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_4,plain,
% 31.83/4.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.83/4.50      inference(cnf_transformation,[],[f32]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_15283,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))))) = k4_xboole_0(sK2,X0) ),
% 31.83/4.50      inference(demodulation,[status(thm)],[c_14529,c_4]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_863,plain,
% 31.83/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_10,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_868,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_863,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_14,negated_conjecture,
% 31.83/4.50      ( r1_tarski(sK2,sK4) ),
% 31.83/4.50      inference(cnf_transformation,[],[f42]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_413,plain,
% 31.83/4.50      ( r1_tarski(sK2,sK4) = iProver_top ),
% 31.83/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_1490,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_413,c_417]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_861,plain,
% 31.83/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_10,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_4737,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,X0))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0)) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_1490,c_861]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_1985,plain,
% 31.83/4.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK4,X0)) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_1490,c_11]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_1995,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK4,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 31.83/4.50      inference(demodulation,[status(thm)],[c_1985,c_1053]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_4838,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
% 31.83/4.50      inference(demodulation,[status(thm)],[c_4737,c_1053,c_1995]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_5625,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_868,c_4838]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_5730,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))) = k4_xboole_0(sK2,X0) ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_5625,c_4838]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_119933,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = k4_xboole_0(sK2,sK4) ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_15283,c_5730]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_120030,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = k1_xboole_0 ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_119933,c_1490]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_7,plain,
% 31.83/4.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 31.83/4.50      inference(cnf_transformation,[],[f34]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_416,plain,
% 31.83/4.50      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 31.83/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.83/4.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_120728,plain,
% 31.83/4.50      ( r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_120030,c_416]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_140930,plain,
% 31.83/4.50      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 31.83/4.50      inference(demodulation,[status(thm)],[c_140377,c_120728]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_8,plain,
% 31.83/4.50      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 31.83/4.50      inference(cnf_transformation,[],[f36]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_415,plain,
% 31.83/4.50      ( k1_xboole_0 = X0
% 31.83/4.50      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 31.83/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_845,plain,
% 31.83/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 31.83/4.50      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) != iProver_top ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_10,c_415]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_4205,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0
% 31.83/4.50      | r1_tarski(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 31.83/4.50      inference(superposition,[status(thm)],[c_1491,c_845]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_4252,plain,
% 31.83/4.50      ( k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0
% 31.83/4.50      | r1_tarski(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 31.83/4.50      inference(light_normalisation,[status(thm)],[c_4205,c_1491]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_4253,plain,
% 31.83/4.50      ( sK2 = k1_xboole_0 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 31.83/4.50      inference(demodulation,[status(thm)],[c_4252,c_9]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_136,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_524,plain,
% 31.83/4.50      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 31.83/4.50      inference(instantiation,[status(thm)],[c_136]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_525,plain,
% 31.83/4.50      ( sK2 != k1_xboole_0
% 31.83/4.50      | k1_xboole_0 = sK2
% 31.83/4.50      | k1_xboole_0 != k1_xboole_0 ),
% 31.83/4.50      inference(instantiation,[status(thm)],[c_524]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_135,plain,( X0 = X0 ),theory(equality) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_148,plain,
% 31.83/4.50      ( k1_xboole_0 = k1_xboole_0 ),
% 31.83/4.50      inference(instantiation,[status(thm)],[c_135]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(c_12,negated_conjecture,
% 31.83/4.50      ( k1_xboole_0 != sK2 ),
% 31.83/4.50      inference(cnf_transformation,[],[f44]) ).
% 31.83/4.50  
% 31.83/4.50  cnf(contradiction,plain,
% 31.83/4.50      ( $false ),
% 31.83/4.50      inference(minisat,[status(thm)],[c_140930,c_4253,c_525,c_148,c_12]) ).
% 31.83/4.50  
% 31.83/4.50  
% 31.83/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.83/4.50  
% 31.83/4.50  ------                               Statistics
% 31.83/4.50  
% 31.83/4.50  ------ Selected
% 31.83/4.50  
% 31.83/4.50  total_time:                             3.901
% 31.83/4.50  
%------------------------------------------------------------------------------
