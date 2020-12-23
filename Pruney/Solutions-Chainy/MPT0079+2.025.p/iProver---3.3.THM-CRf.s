%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:49 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  171 (7293 expanded)
%              Number of clauses        :  120 (2668 expanded)
%              Number of leaves         :   20 (1987 expanded)
%              Depth                    :   29
%              Number of atoms          :  240 (9995 expanded)
%              Number of equality atoms :  186 (8062 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK3 != sK4
      & r1_xboole_0(sK5,sK3)
      & r1_xboole_0(sK4,sK2)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK3 != sK4
    & r1_xboole_0(sK5,sK3)
    & r1_xboole_0(sK4,sK2)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f28])).

fof(f46,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f42,f42])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f43,f42,f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f26])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f47,plain,(
    r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_495,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_0,c_18])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_570,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_2094,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_495,c_570])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_241,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_12,c_10])).

cnf(c_754,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1,c_241])).

cnf(c_755,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_754,c_10])).

cnf(c_16926,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK5),sK3)) = k4_xboole_0(k4_xboole_0(sK5,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2094,c_755])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17230,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK5),sK3)) = k4_xboole_0(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_16926,c_5,c_10])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_239,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_108,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK2 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_109,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
    inference(unflattening,[status(thm)],[c_108])).

cnf(c_236,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_109])).

cnf(c_18320,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_239,c_236])).

cnf(c_764,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_495,c_11])).

cnf(c_559,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_241,c_241])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_240,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_9])).

cnf(c_560,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_559,c_240])).

cnf(c_496,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_561,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_560,c_496])).

cnf(c_1889,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_764,c_561])).

cnf(c_1934,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sK4,k4_xboole_0(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1889,c_496])).

cnf(c_2776,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)),X0)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))) ),
    inference(superposition,[status(thm)],[c_1934,c_241])).

cnf(c_2779,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))) = k4_xboole_0(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_2776,c_496,c_764])).

cnf(c_18637,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_18320,c_2779])).

cnf(c_18642,plain,
    ( k4_xboole_0(sK4,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_18637,c_9])).

cnf(c_2751,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) ),
    inference(superposition,[status(thm)],[c_1,c_1934])).

cnf(c_2757,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),X1)))) = k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_561,c_1934])).

cnf(c_2799,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),X1)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_2757,c_1934,c_2779])).

cnf(c_2772,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),X1)) = k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1934,c_10])).

cnf(c_2781,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),X1)) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_2772,c_10])).

cnf(c_2800,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,X1))) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_2799,c_2781])).

cnf(c_2808,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)),X0)) ),
    inference(demodulation,[status(thm)],[c_2751,c_2800])).

cnf(c_2809,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_2808,c_496,c_764])).

cnf(c_2109,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_570,c_561])).

cnf(c_2112,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2109,c_9])).

cnf(c_2984,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))),k4_xboole_0(sK4,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_2809,c_2112])).

cnf(c_19541,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK2))),sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_18642,c_2984])).

cnf(c_2273,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_2112])).

cnf(c_19572,plain,
    ( k4_xboole_0(sK2,sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_19541,c_10,c_2273])).

cnf(c_19615,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK4,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_19572,c_10])).

cnf(c_22003,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK5) ),
    inference(superposition,[status(thm)],[c_495,c_19615])).

cnf(c_22056,plain,
    ( k4_xboole_0(sK2,sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22003,c_570])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_99,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK5 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_100,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
    inference(unflattening,[status(thm)],[c_99])).

cnf(c_237,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_739,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1,c_237])).

cnf(c_18321,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_239,c_739])).

cnf(c_2322,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_2094,c_561])).

cnf(c_2339,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2322,c_496])).

cnf(c_4346,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)),X0)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) ),
    inference(superposition,[status(thm)],[c_2339,c_241])).

cnf(c_4354,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_4346,c_496,c_2094])).

cnf(c_4649,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(X0,k4_xboole_0(X0,sK5))) = k4_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1,c_4354])).

cnf(c_24033,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(sK5,sK3) ),
    inference(superposition,[status(thm)],[c_18321,c_4649])).

cnf(c_24106,plain,
    ( k4_xboole_0(sK5,sK3) = sK5 ),
    inference(demodulation,[status(thm)],[c_24033,c_9])).

cnf(c_25074,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK3)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_17230,c_17230,c_22056,c_24106])).

cnf(c_16949,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
    inference(superposition,[status(thm)],[c_495,c_755])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18481,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_16949,c_8])).

cnf(c_13,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2092,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_570])).

cnf(c_18471,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)),k4_xboole_0(X0,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16949,c_2092])).

cnf(c_18857,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)),k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)),X0),sK4)) = k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18471,c_241])).

cnf(c_18873,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK4),k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK4),X0)),sK4))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
    inference(demodulation,[status(thm)],[c_18857,c_5,c_10])).

cnf(c_1112,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_10,c_10])).

cnf(c_1136,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_1112,c_10])).

cnf(c_649,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_8])).

cnf(c_654,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_649,c_5])).

cnf(c_4014,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_654])).

cnf(c_2157,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2092,c_8])).

cnf(c_2177,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2157,c_5])).

cnf(c_3733,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_2177])).

cnf(c_2153,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_2092,c_10])).

cnf(c_1050,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_496,c_11])).

cnf(c_2179,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2153,c_10,c_1050])).

cnf(c_7923,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2179])).

cnf(c_13906,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3733,c_7923])).

cnf(c_13998,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13906,c_10])).

cnf(c_18874,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
    inference(demodulation,[status(thm)],[c_18873,c_496,c_1136,c_4014,c_13998])).

cnf(c_23208,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_18481,c_18481,c_18874])).

cnf(c_24497,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(sK4,sK5))) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_24106,c_23208])).

cnf(c_24526,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK4)) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_24497,c_495,c_2094])).

cnf(c_24527,plain,
    ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24526,c_5,c_11,c_496])).

cnf(c_24725,plain,
    ( k2_xboole_0(sK4,sK3) = k2_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_24527,c_8])).

cnf(c_24765,plain,
    ( k2_xboole_0(sK4,sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_24725,c_5])).

cnf(c_24810,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_24765,c_19615])).

cnf(c_24811,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_24810,c_19572])).

cnf(c_25075,plain,
    ( sK2 = sK5 ),
    inference(demodulation,[status(thm)],[c_25074,c_496,c_24811])).

cnf(c_25145,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25075,c_764])).

cnf(c_25350,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK4),sK3)) = k4_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_25145,c_755])).

cnf(c_25095,plain,
    ( k4_xboole_0(sK5,sK4) = sK5 ),
    inference(demodulation,[status(thm)],[c_25075,c_19572])).

cnf(c_25371,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK5,sK3)) = k4_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_25350,c_25095])).

cnf(c_25372,plain,
    ( k4_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25371,c_5,c_10,c_11])).

cnf(c_158,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_323,plain,
    ( X0 != X1
    | k4_xboole_0(sK4,sK3) != X1
    | k4_xboole_0(sK4,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_8363,plain,
    ( k4_xboole_0(sK4,sK3) != X0
    | k4_xboole_0(sK4,sK3) = k4_xboole_0(sK3,sK4)
    | k4_xboole_0(sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_8364,plain,
    ( k4_xboole_0(sK4,sK3) = k4_xboole_0(sK3,sK4)
    | k4_xboole_0(sK4,sK3) != k1_xboole_0
    | k4_xboole_0(sK3,sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8363])).

cnf(c_7,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_276,plain,
    ( k4_xboole_0(sK4,X0) != k4_xboole_0(X0,sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8329,plain,
    ( k4_xboole_0(sK4,sK3) != k4_xboole_0(sK3,sK4)
    | sK4 = sK3 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_157,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6683,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_861,plain,
    ( k4_xboole_0(sK3,X0) != k4_xboole_0(X0,sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4206,plain,
    ( k4_xboole_0(sK3,sK3) != k4_xboole_0(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_250,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_2193,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_15,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25372,c_24527,c_8364,c_8329,c_6683,c_4206,c_2193,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.94/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/1.50  
% 7.94/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.94/1.50  
% 7.94/1.50  ------  iProver source info
% 7.94/1.50  
% 7.94/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.94/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.94/1.50  git: non_committed_changes: false
% 7.94/1.50  git: last_make_outside_of_git: false
% 7.94/1.50  
% 7.94/1.50  ------ 
% 7.94/1.50  
% 7.94/1.50  ------ Input Options
% 7.94/1.50  
% 7.94/1.50  --out_options                           all
% 7.94/1.50  --tptp_safe_out                         true
% 7.94/1.50  --problem_path                          ""
% 7.94/1.50  --include_path                          ""
% 7.94/1.50  --clausifier                            res/vclausify_rel
% 7.94/1.50  --clausifier_options                    ""
% 7.94/1.50  --stdin                                 false
% 7.94/1.50  --stats_out                             all
% 7.94/1.50  
% 7.94/1.50  ------ General Options
% 7.94/1.50  
% 7.94/1.50  --fof                                   false
% 7.94/1.50  --time_out_real                         305.
% 7.94/1.50  --time_out_virtual                      -1.
% 7.94/1.50  --symbol_type_check                     false
% 7.94/1.50  --clausify_out                          false
% 7.94/1.50  --sig_cnt_out                           false
% 7.94/1.50  --trig_cnt_out                          false
% 7.94/1.50  --trig_cnt_out_tolerance                1.
% 7.94/1.50  --trig_cnt_out_sk_spl                   false
% 7.94/1.50  --abstr_cl_out                          false
% 7.94/1.50  
% 7.94/1.50  ------ Global Options
% 7.94/1.50  
% 7.94/1.50  --schedule                              default
% 7.94/1.50  --add_important_lit                     false
% 7.94/1.50  --prop_solver_per_cl                    1000
% 7.94/1.50  --min_unsat_core                        false
% 7.94/1.50  --soft_assumptions                      false
% 7.94/1.50  --soft_lemma_size                       3
% 7.94/1.50  --prop_impl_unit_size                   0
% 7.94/1.50  --prop_impl_unit                        []
% 7.94/1.50  --share_sel_clauses                     true
% 7.94/1.50  --reset_solvers                         false
% 7.94/1.50  --bc_imp_inh                            [conj_cone]
% 7.94/1.50  --conj_cone_tolerance                   3.
% 7.94/1.50  --extra_neg_conj                        none
% 7.94/1.50  --large_theory_mode                     true
% 7.94/1.50  --prolific_symb_bound                   200
% 7.94/1.50  --lt_threshold                          2000
% 7.94/1.50  --clause_weak_htbl                      true
% 7.94/1.50  --gc_record_bc_elim                     false
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing Options
% 7.94/1.50  
% 7.94/1.50  --preprocessing_flag                    true
% 7.94/1.50  --time_out_prep_mult                    0.1
% 7.94/1.50  --splitting_mode                        input
% 7.94/1.50  --splitting_grd                         true
% 7.94/1.50  --splitting_cvd                         false
% 7.94/1.50  --splitting_cvd_svl                     false
% 7.94/1.50  --splitting_nvd                         32
% 7.94/1.50  --sub_typing                            true
% 7.94/1.50  --prep_gs_sim                           true
% 7.94/1.50  --prep_unflatten                        true
% 7.94/1.50  --prep_res_sim                          true
% 7.94/1.50  --prep_upred                            true
% 7.94/1.50  --prep_sem_filter                       exhaustive
% 7.94/1.50  --prep_sem_filter_out                   false
% 7.94/1.50  --pred_elim                             true
% 7.94/1.50  --res_sim_input                         true
% 7.94/1.50  --eq_ax_congr_red                       true
% 7.94/1.50  --pure_diseq_elim                       true
% 7.94/1.50  --brand_transform                       false
% 7.94/1.50  --non_eq_to_eq                          false
% 7.94/1.50  --prep_def_merge                        true
% 7.94/1.50  --prep_def_merge_prop_impl              false
% 7.94/1.50  --prep_def_merge_mbd                    true
% 7.94/1.50  --prep_def_merge_tr_red                 false
% 7.94/1.50  --prep_def_merge_tr_cl                  false
% 7.94/1.50  --smt_preprocessing                     true
% 7.94/1.50  --smt_ac_axioms                         fast
% 7.94/1.50  --preprocessed_out                      false
% 7.94/1.50  --preprocessed_stats                    false
% 7.94/1.50  
% 7.94/1.50  ------ Abstraction refinement Options
% 7.94/1.50  
% 7.94/1.50  --abstr_ref                             []
% 7.94/1.50  --abstr_ref_prep                        false
% 7.94/1.50  --abstr_ref_until_sat                   false
% 7.94/1.50  --abstr_ref_sig_restrict                funpre
% 7.94/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.50  --abstr_ref_under                       []
% 7.94/1.50  
% 7.94/1.50  ------ SAT Options
% 7.94/1.50  
% 7.94/1.50  --sat_mode                              false
% 7.94/1.50  --sat_fm_restart_options                ""
% 7.94/1.50  --sat_gr_def                            false
% 7.94/1.50  --sat_epr_types                         true
% 7.94/1.50  --sat_non_cyclic_types                  false
% 7.94/1.50  --sat_finite_models                     false
% 7.94/1.50  --sat_fm_lemmas                         false
% 7.94/1.50  --sat_fm_prep                           false
% 7.94/1.50  --sat_fm_uc_incr                        true
% 7.94/1.50  --sat_out_model                         small
% 7.94/1.50  --sat_out_clauses                       false
% 7.94/1.50  
% 7.94/1.50  ------ QBF Options
% 7.94/1.50  
% 7.94/1.50  --qbf_mode                              false
% 7.94/1.50  --qbf_elim_univ                         false
% 7.94/1.50  --qbf_dom_inst                          none
% 7.94/1.50  --qbf_dom_pre_inst                      false
% 7.94/1.50  --qbf_sk_in                             false
% 7.94/1.50  --qbf_pred_elim                         true
% 7.94/1.50  --qbf_split                             512
% 7.94/1.50  
% 7.94/1.50  ------ BMC1 Options
% 7.94/1.50  
% 7.94/1.50  --bmc1_incremental                      false
% 7.94/1.50  --bmc1_axioms                           reachable_all
% 7.94/1.50  --bmc1_min_bound                        0
% 7.94/1.50  --bmc1_max_bound                        -1
% 7.94/1.50  --bmc1_max_bound_default                -1
% 7.94/1.50  --bmc1_symbol_reachability              true
% 7.94/1.50  --bmc1_property_lemmas                  false
% 7.94/1.50  --bmc1_k_induction                      false
% 7.94/1.50  --bmc1_non_equiv_states                 false
% 7.94/1.50  --bmc1_deadlock                         false
% 7.94/1.50  --bmc1_ucm                              false
% 7.94/1.50  --bmc1_add_unsat_core                   none
% 7.94/1.50  --bmc1_unsat_core_children              false
% 7.94/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.50  --bmc1_out_stat                         full
% 7.94/1.50  --bmc1_ground_init                      false
% 7.94/1.50  --bmc1_pre_inst_next_state              false
% 7.94/1.50  --bmc1_pre_inst_state                   false
% 7.94/1.50  --bmc1_pre_inst_reach_state             false
% 7.94/1.50  --bmc1_out_unsat_core                   false
% 7.94/1.50  --bmc1_aig_witness_out                  false
% 7.94/1.50  --bmc1_verbose                          false
% 7.94/1.50  --bmc1_dump_clauses_tptp                false
% 7.94/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.50  --bmc1_dump_file                        -
% 7.94/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.50  --bmc1_ucm_extend_mode                  1
% 7.94/1.50  --bmc1_ucm_init_mode                    2
% 7.94/1.50  --bmc1_ucm_cone_mode                    none
% 7.94/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.50  --bmc1_ucm_relax_model                  4
% 7.94/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.50  --bmc1_ucm_layered_model                none
% 7.94/1.50  --bmc1_ucm_max_lemma_size               10
% 7.94/1.50  
% 7.94/1.50  ------ AIG Options
% 7.94/1.50  
% 7.94/1.50  --aig_mode                              false
% 7.94/1.50  
% 7.94/1.50  ------ Instantiation Options
% 7.94/1.50  
% 7.94/1.50  --instantiation_flag                    true
% 7.94/1.50  --inst_sos_flag                         true
% 7.94/1.50  --inst_sos_phase                        true
% 7.94/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.50  --inst_lit_sel_side                     num_symb
% 7.94/1.50  --inst_solver_per_active                1400
% 7.94/1.50  --inst_solver_calls_frac                1.
% 7.94/1.50  --inst_passive_queue_type               priority_queues
% 7.94/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.50  --inst_passive_queues_freq              [25;2]
% 7.94/1.50  --inst_dismatching                      true
% 7.94/1.50  --inst_eager_unprocessed_to_passive     true
% 7.94/1.50  --inst_prop_sim_given                   true
% 7.94/1.50  --inst_prop_sim_new                     false
% 7.94/1.50  --inst_subs_new                         false
% 7.94/1.50  --inst_eq_res_simp                      false
% 7.94/1.50  --inst_subs_given                       false
% 7.94/1.50  --inst_orphan_elimination               true
% 7.94/1.50  --inst_learning_loop_flag               true
% 7.94/1.50  --inst_learning_start                   3000
% 7.94/1.50  --inst_learning_factor                  2
% 7.94/1.50  --inst_start_prop_sim_after_learn       3
% 7.94/1.50  --inst_sel_renew                        solver
% 7.94/1.50  --inst_lit_activity_flag                true
% 7.94/1.50  --inst_restr_to_given                   false
% 7.94/1.50  --inst_activity_threshold               500
% 7.94/1.50  --inst_out_proof                        true
% 7.94/1.50  
% 7.94/1.50  ------ Resolution Options
% 7.94/1.50  
% 7.94/1.50  --resolution_flag                       true
% 7.94/1.50  --res_lit_sel                           adaptive
% 7.94/1.50  --res_lit_sel_side                      none
% 7.94/1.50  --res_ordering                          kbo
% 7.94/1.50  --res_to_prop_solver                    active
% 7.94/1.50  --res_prop_simpl_new                    false
% 7.94/1.50  --res_prop_simpl_given                  true
% 7.94/1.50  --res_passive_queue_type                priority_queues
% 7.94/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.50  --res_passive_queues_freq               [15;5]
% 7.94/1.50  --res_forward_subs                      full
% 7.94/1.50  --res_backward_subs                     full
% 7.94/1.50  --res_forward_subs_resolution           true
% 7.94/1.50  --res_backward_subs_resolution          true
% 7.94/1.50  --res_orphan_elimination                true
% 7.94/1.50  --res_time_limit                        2.
% 7.94/1.50  --res_out_proof                         true
% 7.94/1.50  
% 7.94/1.50  ------ Superposition Options
% 7.94/1.50  
% 7.94/1.50  --superposition_flag                    true
% 7.94/1.50  --sup_passive_queue_type                priority_queues
% 7.94/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.94/1.50  --demod_completeness_check              fast
% 7.94/1.50  --demod_use_ground                      true
% 7.94/1.50  --sup_to_prop_solver                    passive
% 7.94/1.50  --sup_prop_simpl_new                    true
% 7.94/1.50  --sup_prop_simpl_given                  true
% 7.94/1.50  --sup_fun_splitting                     true
% 7.94/1.50  --sup_smt_interval                      50000
% 7.94/1.50  
% 7.94/1.50  ------ Superposition Simplification Setup
% 7.94/1.50  
% 7.94/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.94/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.94/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.94/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.94/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.94/1.50  --sup_immed_triv                        [TrivRules]
% 7.94/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.50  --sup_immed_bw_main                     []
% 7.94/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.94/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.50  --sup_input_bw                          []
% 7.94/1.50  
% 7.94/1.50  ------ Combination Options
% 7.94/1.50  
% 7.94/1.50  --comb_res_mult                         3
% 7.94/1.50  --comb_sup_mult                         2
% 7.94/1.50  --comb_inst_mult                        10
% 7.94/1.50  
% 7.94/1.50  ------ Debug Options
% 7.94/1.50  
% 7.94/1.50  --dbg_backtrace                         false
% 7.94/1.50  --dbg_dump_prop_clauses                 false
% 7.94/1.50  --dbg_dump_prop_clauses_file            -
% 7.94/1.50  --dbg_out_stat                          false
% 7.94/1.50  ------ Parsing...
% 7.94/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.50  ------ Proving...
% 7.94/1.50  ------ Problem Properties 
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  clauses                                 18
% 7.94/1.50  conjectures                             2
% 7.94/1.50  EPR                                     1
% 7.94/1.50  Horn                                    17
% 7.94/1.50  unary                                   15
% 7.94/1.50  binary                                  3
% 7.94/1.50  lits                                    21
% 7.94/1.50  lits eq                                 16
% 7.94/1.50  fd_pure                                 0
% 7.94/1.50  fd_pseudo                               0
% 7.94/1.50  fd_cond                                 1
% 7.94/1.50  fd_pseudo_cond                          1
% 7.94/1.50  AC symbols                              0
% 7.94/1.50  
% 7.94/1.50  ------ Schedule dynamic 5 is on 
% 7.94/1.50  
% 7.94/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  ------ 
% 7.94/1.50  Current options:
% 7.94/1.50  ------ 
% 7.94/1.50  
% 7.94/1.50  ------ Input Options
% 7.94/1.50  
% 7.94/1.50  --out_options                           all
% 7.94/1.50  --tptp_safe_out                         true
% 7.94/1.50  --problem_path                          ""
% 7.94/1.50  --include_path                          ""
% 7.94/1.50  --clausifier                            res/vclausify_rel
% 7.94/1.50  --clausifier_options                    ""
% 7.94/1.50  --stdin                                 false
% 7.94/1.50  --stats_out                             all
% 7.94/1.50  
% 7.94/1.50  ------ General Options
% 7.94/1.50  
% 7.94/1.50  --fof                                   false
% 7.94/1.50  --time_out_real                         305.
% 7.94/1.50  --time_out_virtual                      -1.
% 7.94/1.50  --symbol_type_check                     false
% 7.94/1.50  --clausify_out                          false
% 7.94/1.50  --sig_cnt_out                           false
% 7.94/1.50  --trig_cnt_out                          false
% 7.94/1.50  --trig_cnt_out_tolerance                1.
% 7.94/1.50  --trig_cnt_out_sk_spl                   false
% 7.94/1.50  --abstr_cl_out                          false
% 7.94/1.50  
% 7.94/1.50  ------ Global Options
% 7.94/1.50  
% 7.94/1.50  --schedule                              default
% 7.94/1.50  --add_important_lit                     false
% 7.94/1.50  --prop_solver_per_cl                    1000
% 7.94/1.50  --min_unsat_core                        false
% 7.94/1.50  --soft_assumptions                      false
% 7.94/1.50  --soft_lemma_size                       3
% 7.94/1.50  --prop_impl_unit_size                   0
% 7.94/1.50  --prop_impl_unit                        []
% 7.94/1.50  --share_sel_clauses                     true
% 7.94/1.50  --reset_solvers                         false
% 7.94/1.50  --bc_imp_inh                            [conj_cone]
% 7.94/1.50  --conj_cone_tolerance                   3.
% 7.94/1.50  --extra_neg_conj                        none
% 7.94/1.50  --large_theory_mode                     true
% 7.94/1.50  --prolific_symb_bound                   200
% 7.94/1.50  --lt_threshold                          2000
% 7.94/1.50  --clause_weak_htbl                      true
% 7.94/1.50  --gc_record_bc_elim                     false
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing Options
% 7.94/1.50  
% 7.94/1.50  --preprocessing_flag                    true
% 7.94/1.50  --time_out_prep_mult                    0.1
% 7.94/1.50  --splitting_mode                        input
% 7.94/1.50  --splitting_grd                         true
% 7.94/1.50  --splitting_cvd                         false
% 7.94/1.50  --splitting_cvd_svl                     false
% 7.94/1.50  --splitting_nvd                         32
% 7.94/1.50  --sub_typing                            true
% 7.94/1.50  --prep_gs_sim                           true
% 7.94/1.50  --prep_unflatten                        true
% 7.94/1.50  --prep_res_sim                          true
% 7.94/1.50  --prep_upred                            true
% 7.94/1.50  --prep_sem_filter                       exhaustive
% 7.94/1.50  --prep_sem_filter_out                   false
% 7.94/1.50  --pred_elim                             true
% 7.94/1.50  --res_sim_input                         true
% 7.94/1.50  --eq_ax_congr_red                       true
% 7.94/1.50  --pure_diseq_elim                       true
% 7.94/1.50  --brand_transform                       false
% 7.94/1.50  --non_eq_to_eq                          false
% 7.94/1.50  --prep_def_merge                        true
% 7.94/1.50  --prep_def_merge_prop_impl              false
% 7.94/1.50  --prep_def_merge_mbd                    true
% 7.94/1.50  --prep_def_merge_tr_red                 false
% 7.94/1.50  --prep_def_merge_tr_cl                  false
% 7.94/1.50  --smt_preprocessing                     true
% 7.94/1.50  --smt_ac_axioms                         fast
% 7.94/1.50  --preprocessed_out                      false
% 7.94/1.50  --preprocessed_stats                    false
% 7.94/1.50  
% 7.94/1.50  ------ Abstraction refinement Options
% 7.94/1.50  
% 7.94/1.50  --abstr_ref                             []
% 7.94/1.50  --abstr_ref_prep                        false
% 7.94/1.50  --abstr_ref_until_sat                   false
% 7.94/1.50  --abstr_ref_sig_restrict                funpre
% 7.94/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.50  --abstr_ref_under                       []
% 7.94/1.50  
% 7.94/1.50  ------ SAT Options
% 7.94/1.50  
% 7.94/1.50  --sat_mode                              false
% 7.94/1.50  --sat_fm_restart_options                ""
% 7.94/1.50  --sat_gr_def                            false
% 7.94/1.50  --sat_epr_types                         true
% 7.94/1.50  --sat_non_cyclic_types                  false
% 7.94/1.50  --sat_finite_models                     false
% 7.94/1.50  --sat_fm_lemmas                         false
% 7.94/1.50  --sat_fm_prep                           false
% 7.94/1.50  --sat_fm_uc_incr                        true
% 7.94/1.50  --sat_out_model                         small
% 7.94/1.50  --sat_out_clauses                       false
% 7.94/1.50  
% 7.94/1.50  ------ QBF Options
% 7.94/1.50  
% 7.94/1.50  --qbf_mode                              false
% 7.94/1.50  --qbf_elim_univ                         false
% 7.94/1.50  --qbf_dom_inst                          none
% 7.94/1.50  --qbf_dom_pre_inst                      false
% 7.94/1.50  --qbf_sk_in                             false
% 7.94/1.50  --qbf_pred_elim                         true
% 7.94/1.50  --qbf_split                             512
% 7.94/1.50  
% 7.94/1.50  ------ BMC1 Options
% 7.94/1.50  
% 7.94/1.50  --bmc1_incremental                      false
% 7.94/1.50  --bmc1_axioms                           reachable_all
% 7.94/1.50  --bmc1_min_bound                        0
% 7.94/1.50  --bmc1_max_bound                        -1
% 7.94/1.50  --bmc1_max_bound_default                -1
% 7.94/1.50  --bmc1_symbol_reachability              true
% 7.94/1.50  --bmc1_property_lemmas                  false
% 7.94/1.50  --bmc1_k_induction                      false
% 7.94/1.50  --bmc1_non_equiv_states                 false
% 7.94/1.50  --bmc1_deadlock                         false
% 7.94/1.50  --bmc1_ucm                              false
% 7.94/1.50  --bmc1_add_unsat_core                   none
% 7.94/1.50  --bmc1_unsat_core_children              false
% 7.94/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.50  --bmc1_out_stat                         full
% 7.94/1.50  --bmc1_ground_init                      false
% 7.94/1.50  --bmc1_pre_inst_next_state              false
% 7.94/1.50  --bmc1_pre_inst_state                   false
% 7.94/1.50  --bmc1_pre_inst_reach_state             false
% 7.94/1.50  --bmc1_out_unsat_core                   false
% 7.94/1.50  --bmc1_aig_witness_out                  false
% 7.94/1.50  --bmc1_verbose                          false
% 7.94/1.50  --bmc1_dump_clauses_tptp                false
% 7.94/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.50  --bmc1_dump_file                        -
% 7.94/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.50  --bmc1_ucm_extend_mode                  1
% 7.94/1.50  --bmc1_ucm_init_mode                    2
% 7.94/1.50  --bmc1_ucm_cone_mode                    none
% 7.94/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.50  --bmc1_ucm_relax_model                  4
% 7.94/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.50  --bmc1_ucm_layered_model                none
% 7.94/1.50  --bmc1_ucm_max_lemma_size               10
% 7.94/1.50  
% 7.94/1.50  ------ AIG Options
% 7.94/1.50  
% 7.94/1.50  --aig_mode                              false
% 7.94/1.50  
% 7.94/1.50  ------ Instantiation Options
% 7.94/1.50  
% 7.94/1.50  --instantiation_flag                    true
% 7.94/1.50  --inst_sos_flag                         true
% 7.94/1.50  --inst_sos_phase                        true
% 7.94/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.50  --inst_lit_sel_side                     none
% 7.94/1.50  --inst_solver_per_active                1400
% 7.94/1.50  --inst_solver_calls_frac                1.
% 7.94/1.50  --inst_passive_queue_type               priority_queues
% 7.94/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.50  --inst_passive_queues_freq              [25;2]
% 7.94/1.50  --inst_dismatching                      true
% 7.94/1.50  --inst_eager_unprocessed_to_passive     true
% 7.94/1.50  --inst_prop_sim_given                   true
% 7.94/1.50  --inst_prop_sim_new                     false
% 7.94/1.50  --inst_subs_new                         false
% 7.94/1.50  --inst_eq_res_simp                      false
% 7.94/1.50  --inst_subs_given                       false
% 7.94/1.50  --inst_orphan_elimination               true
% 7.94/1.50  --inst_learning_loop_flag               true
% 7.94/1.50  --inst_learning_start                   3000
% 7.94/1.50  --inst_learning_factor                  2
% 7.94/1.50  --inst_start_prop_sim_after_learn       3
% 7.94/1.50  --inst_sel_renew                        solver
% 7.94/1.50  --inst_lit_activity_flag                true
% 7.94/1.50  --inst_restr_to_given                   false
% 7.94/1.50  --inst_activity_threshold               500
% 7.94/1.50  --inst_out_proof                        true
% 7.94/1.50  
% 7.94/1.50  ------ Resolution Options
% 7.94/1.50  
% 7.94/1.50  --resolution_flag                       false
% 7.94/1.50  --res_lit_sel                           adaptive
% 7.94/1.50  --res_lit_sel_side                      none
% 7.94/1.50  --res_ordering                          kbo
% 7.94/1.50  --res_to_prop_solver                    active
% 7.94/1.50  --res_prop_simpl_new                    false
% 7.94/1.50  --res_prop_simpl_given                  true
% 7.94/1.50  --res_passive_queue_type                priority_queues
% 7.94/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.50  --res_passive_queues_freq               [15;5]
% 7.94/1.50  --res_forward_subs                      full
% 7.94/1.50  --res_backward_subs                     full
% 7.94/1.50  --res_forward_subs_resolution           true
% 7.94/1.50  --res_backward_subs_resolution          true
% 7.94/1.50  --res_orphan_elimination                true
% 7.94/1.50  --res_time_limit                        2.
% 7.94/1.50  --res_out_proof                         true
% 7.94/1.50  
% 7.94/1.50  ------ Superposition Options
% 7.94/1.50  
% 7.94/1.50  --superposition_flag                    true
% 7.94/1.50  --sup_passive_queue_type                priority_queues
% 7.94/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.94/1.50  --demod_completeness_check              fast
% 7.94/1.50  --demod_use_ground                      true
% 7.94/1.50  --sup_to_prop_solver                    passive
% 7.94/1.50  --sup_prop_simpl_new                    true
% 7.94/1.50  --sup_prop_simpl_given                  true
% 7.94/1.50  --sup_fun_splitting                     true
% 7.94/1.50  --sup_smt_interval                      50000
% 7.94/1.50  
% 7.94/1.50  ------ Superposition Simplification Setup
% 7.94/1.50  
% 7.94/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.94/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.94/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.94/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.94/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.94/1.50  --sup_immed_triv                        [TrivRules]
% 7.94/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.50  --sup_immed_bw_main                     []
% 7.94/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.94/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.50  --sup_input_bw                          []
% 7.94/1.50  
% 7.94/1.50  ------ Combination Options
% 7.94/1.50  
% 7.94/1.50  --comb_res_mult                         3
% 7.94/1.50  --comb_sup_mult                         2
% 7.94/1.50  --comb_inst_mult                        10
% 7.94/1.50  
% 7.94/1.50  ------ Debug Options
% 7.94/1.50  
% 7.94/1.50  --dbg_backtrace                         false
% 7.94/1.50  --dbg_dump_prop_clauses                 false
% 7.94/1.50  --dbg_dump_prop_clauses_file            -
% 7.94/1.50  --dbg_out_stat                          false
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  ------ Proving...
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  % SZS status Theorem for theBenchmark.p
% 7.94/1.50  
% 7.94/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.94/1.50  
% 7.94/1.50  fof(f1,axiom,(
% 7.94/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f30,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f1])).
% 7.94/1.50  
% 7.94/1.50  fof(f16,conjecture,(
% 7.94/1.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f17,negated_conjecture,(
% 7.94/1.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 7.94/1.50    inference(negated_conjecture,[],[f16])).
% 7.94/1.50  
% 7.94/1.50  fof(f22,plain,(
% 7.94/1.50    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 7.94/1.50    inference(ennf_transformation,[],[f17])).
% 7.94/1.50  
% 7.94/1.50  fof(f23,plain,(
% 7.94/1.50    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 7.94/1.50    inference(flattening,[],[f22])).
% 7.94/1.50  
% 7.94/1.50  fof(f28,plain,(
% 7.94/1.50    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5))),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f29,plain,(
% 7.94/1.50    sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 7.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f28])).
% 7.94/1.50  
% 7.94/1.50  fof(f46,plain,(
% 7.94/1.50    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 7.94/1.50    inference(cnf_transformation,[],[f29])).
% 7.94/1.50  
% 7.94/1.50  fof(f11,axiom,(
% 7.94/1.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f41,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.94/1.50    inference(cnf_transformation,[],[f11])).
% 7.94/1.50  
% 7.94/1.50  fof(f2,axiom,(
% 7.94/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f31,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f2])).
% 7.94/1.50  
% 7.94/1.50  fof(f12,axiom,(
% 7.94/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f42,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.94/1.50    inference(cnf_transformation,[],[f12])).
% 7.94/1.50  
% 7.94/1.50  fof(f50,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.94/1.50    inference(definition_unfolding,[],[f31,f42,f42])).
% 7.94/1.50  
% 7.94/1.50  fof(f13,axiom,(
% 7.94/1.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f43,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f13])).
% 7.94/1.50  
% 7.94/1.50  fof(f54,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.94/1.50    inference(definition_unfolding,[],[f43,f42,f42])).
% 7.94/1.50  
% 7.94/1.50  fof(f10,axiom,(
% 7.94/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f40,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f10])).
% 7.94/1.50  
% 7.94/1.50  fof(f5,axiom,(
% 7.94/1.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f35,plain,(
% 7.94/1.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.94/1.50    inference(cnf_transformation,[],[f5])).
% 7.94/1.50  
% 7.94/1.50  fof(f4,axiom,(
% 7.94/1.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f20,plain,(
% 7.94/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.94/1.50    inference(ennf_transformation,[],[f4])).
% 7.94/1.50  
% 7.94/1.50  fof(f26,plain,(
% 7.94/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f27,plain,(
% 7.94/1.50    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f26])).
% 7.94/1.50  
% 7.94/1.50  fof(f34,plain,(
% 7.94/1.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.94/1.50    inference(cnf_transformation,[],[f27])).
% 7.94/1.50  
% 7.94/1.50  fof(f3,axiom,(
% 7.94/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f18,plain,(
% 7.94/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.94/1.50    inference(rectify,[],[f3])).
% 7.94/1.50  
% 7.94/1.50  fof(f19,plain,(
% 7.94/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.94/1.50    inference(ennf_transformation,[],[f18])).
% 7.94/1.50  
% 7.94/1.50  fof(f24,plain,(
% 7.94/1.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f25,plain,(
% 7.94/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f24])).
% 7.94/1.50  
% 7.94/1.50  fof(f33,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.94/1.50    inference(cnf_transformation,[],[f25])).
% 7.94/1.50  
% 7.94/1.50  fof(f51,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.94/1.50    inference(definition_unfolding,[],[f33,f42])).
% 7.94/1.50  
% 7.94/1.50  fof(f47,plain,(
% 7.94/1.50    r1_xboole_0(sK4,sK2)),
% 7.94/1.50    inference(cnf_transformation,[],[f29])).
% 7.94/1.50  
% 7.94/1.50  fof(f6,axiom,(
% 7.94/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f36,plain,(
% 7.94/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.94/1.50    inference(cnf_transformation,[],[f6])).
% 7.94/1.50  
% 7.94/1.50  fof(f53,plain,(
% 7.94/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.94/1.50    inference(definition_unfolding,[],[f36,f42])).
% 7.94/1.50  
% 7.94/1.50  fof(f9,axiom,(
% 7.94/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f39,plain,(
% 7.94/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.94/1.50    inference(cnf_transformation,[],[f9])).
% 7.94/1.50  
% 7.94/1.50  fof(f48,plain,(
% 7.94/1.50    r1_xboole_0(sK5,sK3)),
% 7.94/1.50    inference(cnf_transformation,[],[f29])).
% 7.94/1.50  
% 7.94/1.50  fof(f8,axiom,(
% 7.94/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f38,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.94/1.50    inference(cnf_transformation,[],[f8])).
% 7.94/1.50  
% 7.94/1.50  fof(f14,axiom,(
% 7.94/1.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f44,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.94/1.50    inference(cnf_transformation,[],[f14])).
% 7.94/1.50  
% 7.94/1.50  fof(f55,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.94/1.50    inference(definition_unfolding,[],[f44,f42])).
% 7.94/1.50  
% 7.94/1.50  fof(f7,axiom,(
% 7.94/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f21,plain,(
% 7.94/1.50    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 7.94/1.50    inference(ennf_transformation,[],[f7])).
% 7.94/1.50  
% 7.94/1.50  fof(f37,plain,(
% 7.94/1.50    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f21])).
% 7.94/1.50  
% 7.94/1.50  fof(f49,plain,(
% 7.94/1.50    sK3 != sK4),
% 7.94/1.50    inference(cnf_transformation,[],[f29])).
% 7.94/1.50  
% 7.94/1.50  cnf(c_0,plain,
% 7.94/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.94/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18,negated_conjecture,
% 7.94/1.50      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
% 7.94/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_495,plain,
% 7.94/1.50      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_0,c_18]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_11,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_570,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2094,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_495,c_570]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.94/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_12,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.94/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_10,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.94/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_241,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_12,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_754,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_1,c_241]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_755,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_754,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_16926,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK5),sK3)) = k4_xboole_0(k4_xboole_0(sK5,sK3),k1_xboole_0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_2094,c_755]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_5,plain,
% 7.94/1.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_17230,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK5),sK3)) = k4_xboole_0(sK5,sK3) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_16926,c_5,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4,plain,
% 7.94/1.50      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_239,plain,
% 7.94/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2,plain,
% 7.94/1.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.94/1.50      | ~ r1_xboole_0(X1,X2) ),
% 7.94/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_17,negated_conjecture,
% 7.94/1.50      ( r1_xboole_0(sK4,sK2) ),
% 7.94/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_108,plain,
% 7.94/1.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.94/1.50      | sK2 != X2
% 7.94/1.50      | sK4 != X1 ),
% 7.94/1.50      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_109,plain,
% 7.94/1.50      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
% 7.94/1.50      inference(unflattening,[status(thm)],[c_108]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_236,plain,
% 7.94/1.50      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_109]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18320,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_239,c_236]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_764,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_495,c_11]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_559,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_241,c_241]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_6,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_9,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_240,plain,
% 7.94/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_6,c_9]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_560,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_559,c_240]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_496,plain,
% 7.94/1.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_561,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_560,c_496]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1889,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(k1_xboole_0,X0))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_764,c_561]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1934,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sK4,k4_xboole_0(sK4,X0)) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_1889,c_496]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2776,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)),X0)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_1934,c_241]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2779,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))) = k4_xboole_0(sK4,X0) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_2776,c_496,c_764]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18637,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK4,sK2) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_18320,c_2779]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18642,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,sK2) = sK4 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_18637,c_9]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2751,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_1,c_1934]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2757,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),X1)))) = k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(X0,X1))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_561,c_1934]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2799,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),X1)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,X1))) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_2757,c_1934,c_2779]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2772,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),X1)) = k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),X1) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_1934,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2781,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),X1)) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,X0),X1)) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_2772,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2800,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,X1))) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,X0),X1)) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_2799,c_2781]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2808,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)),X0)) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_2751,c_2800]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2809,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,X0) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_2808,c_496,c_764]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2109,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_570,c_561]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2112,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_2109,c_9]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2984,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))),k4_xboole_0(sK4,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_2809,c_2112]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_19541,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK2))),sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK2))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_18642,c_2984]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2273,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_10,c_2112]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_19572,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,sK4) = sK2 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_19541,c_10,c_2273]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_19615,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,k2_xboole_0(sK4,X0)) = k4_xboole_0(sK2,X0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_19572,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_22003,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK5) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_495,c_19615]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_22056,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,sK5) = k1_xboole_0 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_22003,c_570]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_16,negated_conjecture,
% 7.94/1.50      ( r1_xboole_0(sK5,sK3) ),
% 7.94/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_99,plain,
% 7.94/1.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.94/1.50      | sK5 != X1
% 7.94/1.50      | sK3 != X2 ),
% 7.94/1.50      inference(resolution_lifted,[status(thm)],[c_2,c_16]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_100,plain,
% 7.94/1.50      ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
% 7.94/1.50      inference(unflattening,[status(thm)],[c_99]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_237,plain,
% 7.94/1.50      ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_100]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_739,plain,
% 7.94/1.50      ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_1,c_237]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18321,plain,
% 7.94/1.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_239,c_739]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2322,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(k1_xboole_0,X0))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_2094,c_561]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2339,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_2322,c_496]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4346,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)),X0)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_2339,c_241]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4354,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK5,X0) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_4346,c_496,c_2094]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4649,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k4_xboole_0(X0,k4_xboole_0(X0,sK5))) = k4_xboole_0(sK5,X0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_1,c_4354]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24033,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(sK5,sK3) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_18321,c_4649]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24106,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,sK3) = sK5 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_24033,c_9]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_25074,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK3)) = sK5 ),
% 7.94/1.50      inference(light_normalisation,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_17230,c_17230,c_22056,c_24106]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_16949,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_495,c_755]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_8,plain,
% 7.94/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.94/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18481,plain,
% 7.94/1.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,sK4)) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_16949,c_8]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_13,plain,
% 7.94/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2092,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_13,c_570]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18471,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)),k4_xboole_0(X0,sK4)) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_16949,c_2092]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18857,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)),k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)),X0),sK4)) = k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)),k1_xboole_0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_18471,c_241]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18873,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK4),k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK4),X0)),sK4))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_18857,c_5,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1112,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_10,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1136,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_1112,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_649,plain,
% 7.94/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_11,c_8]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_654,plain,
% 7.94/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_649,c_5]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4014,plain,
% 7.94/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_0,c_654]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2157,plain,
% 7.94/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_2092,c_8]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2177,plain,
% 7.94/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_2157,c_5]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_3733,plain,
% 7.94/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_1,c_2177]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2153,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_2092,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1050,plain,
% 7.94/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_496,c_11]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2179,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_2153,c_10,c_1050]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_7923,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_0,c_2179]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_13906,plain,
% 7.94/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_3733,c_7923]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_13998,plain,
% 7.94/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X1)) = k1_xboole_0 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_13906,c_10]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18874,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
% 7.94/1.50      inference(demodulation,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_18873,c_496,c_1136,c_4014,c_13998]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_23208,plain,
% 7.94/1.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,sK4)) ),
% 7.94/1.50      inference(light_normalisation,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_18481,c_18481,c_18874]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24497,plain,
% 7.94/1.50      ( k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(sK4,sK5))) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK4)) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_24106,c_23208]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24526,plain,
% 7.94/1.50      ( k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK4)) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k1_xboole_0) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_24497,c_495,c_2094]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24527,plain,
% 7.94/1.50      ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_24526,c_5,c_11,c_496]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24725,plain,
% 7.94/1.50      ( k2_xboole_0(sK4,sK3) = k2_xboole_0(sK4,k1_xboole_0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_24527,c_8]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24765,plain,
% 7.94/1.50      ( k2_xboole_0(sK4,sK3) = sK4 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_24725,c_5]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24810,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK4) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_24765,c_19615]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24811,plain,
% 7.94/1.50      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_24810,c_19572]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_25075,plain,
% 7.94/1.50      ( sK2 = sK5 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_25074,c_496,c_24811]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_25145,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_25075,c_764]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_25350,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK4),sK3)) = k4_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_25145,c_755]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_25095,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,sK4) = sK5 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_25075,c_19572]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_25371,plain,
% 7.94/1.50      ( k4_xboole_0(sK5,k2_xboole_0(sK5,sK3)) = k4_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_25350,c_25095]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_25372,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 7.94/1.50      inference(demodulation,[status(thm)],[c_25371,c_5,c_10,c_11]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_158,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_323,plain,
% 7.94/1.50      ( X0 != X1
% 7.94/1.50      | k4_xboole_0(sK4,sK3) != X1
% 7.94/1.50      | k4_xboole_0(sK4,sK3) = X0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_158]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_8363,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,sK3) != X0
% 7.94/1.50      | k4_xboole_0(sK4,sK3) = k4_xboole_0(sK3,sK4)
% 7.94/1.50      | k4_xboole_0(sK3,sK4) != X0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_323]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_8364,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,sK3) = k4_xboole_0(sK3,sK4)
% 7.94/1.50      | k4_xboole_0(sK4,sK3) != k1_xboole_0
% 7.94/1.50      | k4_xboole_0(sK3,sK4) != k1_xboole_0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_8363]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_7,plain,
% 7.94/1.50      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 7.94/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_276,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,X0) != k4_xboole_0(X0,sK4) | sK4 = X0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_8329,plain,
% 7.94/1.50      ( k4_xboole_0(sK4,sK3) != k4_xboole_0(sK3,sK4) | sK4 = sK3 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_276]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_157,plain,( X0 = X0 ),theory(equality) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_6683,plain,
% 7.94/1.50      ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK3) ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_157]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_861,plain,
% 7.94/1.50      ( k4_xboole_0(sK3,X0) != k4_xboole_0(X0,sK3) | sK3 = X0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4206,plain,
% 7.94/1.50      ( k4_xboole_0(sK3,sK3) != k4_xboole_0(sK3,sK3) | sK3 = sK3 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_861]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_250,plain,
% 7.94/1.50      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_158]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2193,plain,
% 7.94/1.50      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_250]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_15,negated_conjecture,
% 7.94/1.50      ( sK3 != sK4 ),
% 7.94/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(contradiction,plain,
% 7.94/1.50      ( $false ),
% 7.94/1.50      inference(minisat,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_25372,c_24527,c_8364,c_8329,c_6683,c_4206,c_2193,c_15]) ).
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.94/1.50  
% 7.94/1.50  ------                               Statistics
% 7.94/1.50  
% 7.94/1.50  ------ General
% 7.94/1.50  
% 7.94/1.50  abstr_ref_over_cycles:                  0
% 7.94/1.50  abstr_ref_under_cycles:                 0
% 7.94/1.50  gc_basic_clause_elim:                   0
% 7.94/1.50  forced_gc_time:                         0
% 7.94/1.50  parsing_time:                           0.009
% 7.94/1.50  unif_index_cands_time:                  0.
% 7.94/1.50  unif_index_add_time:                    0.
% 7.94/1.50  orderings_time:                         0.
% 7.94/1.50  out_proof_time:                         0.01
% 7.94/1.50  total_time:                             0.914
% 7.94/1.50  num_of_symbols:                         42
% 7.94/1.50  num_of_terms:                           54373
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing
% 7.94/1.50  
% 7.94/1.50  num_of_splits:                          0
% 7.94/1.50  num_of_split_atoms:                     0
% 7.94/1.50  num_of_reused_defs:                     0
% 7.94/1.50  num_eq_ax_congr_red:                    9
% 7.94/1.50  num_of_sem_filtered_clauses:            1
% 7.94/1.50  num_of_subtypes:                        0
% 7.94/1.50  monotx_restored_types:                  0
% 7.94/1.50  sat_num_of_epr_types:                   0
% 7.94/1.50  sat_num_of_non_cyclic_types:            0
% 7.94/1.50  sat_guarded_non_collapsed_types:        0
% 7.94/1.50  num_pure_diseq_elim:                    0
% 7.94/1.50  simp_replaced_by:                       0
% 7.94/1.50  res_preprocessed:                       84
% 7.94/1.50  prep_upred:                             0
% 7.94/1.50  prep_unflattend:                        6
% 7.94/1.50  smt_new_axioms:                         0
% 7.94/1.50  pred_elim_cands:                        1
% 7.94/1.50  pred_elim:                              1
% 7.94/1.50  pred_elim_cl:                           1
% 7.94/1.50  pred_elim_cycles:                       3
% 7.94/1.50  merged_defs:                            0
% 7.94/1.50  merged_defs_ncl:                        0
% 7.94/1.50  bin_hyper_res:                          0
% 7.94/1.50  prep_cycles:                            4
% 7.94/1.50  pred_elim_time:                         0.001
% 7.94/1.50  splitting_time:                         0.
% 7.94/1.50  sem_filter_time:                        0.
% 7.94/1.50  monotx_time:                            0.001
% 7.94/1.50  subtype_inf_time:                       0.
% 7.94/1.50  
% 7.94/1.50  ------ Problem properties
% 7.94/1.50  
% 7.94/1.50  clauses:                                18
% 7.94/1.50  conjectures:                            2
% 7.94/1.50  epr:                                    1
% 7.94/1.50  horn:                                   17
% 7.94/1.50  ground:                                 2
% 7.94/1.50  unary:                                  15
% 7.94/1.50  binary:                                 3
% 7.94/1.50  lits:                                   21
% 7.94/1.50  lits_eq:                                16
% 7.94/1.50  fd_pure:                                0
% 7.94/1.50  fd_pseudo:                              0
% 7.94/1.50  fd_cond:                                1
% 7.94/1.50  fd_pseudo_cond:                         1
% 7.94/1.50  ac_symbols:                             0
% 7.94/1.50  
% 7.94/1.50  ------ Propositional Solver
% 7.94/1.50  
% 7.94/1.50  prop_solver_calls:                      30
% 7.94/1.50  prop_fast_solver_calls:                 423
% 7.94/1.50  smt_solver_calls:                       0
% 7.94/1.50  smt_fast_solver_calls:                  0
% 7.94/1.50  prop_num_of_clauses:                    6500
% 7.94/1.50  prop_preprocess_simplified:             7331
% 7.94/1.50  prop_fo_subsumed:                       0
% 7.94/1.50  prop_solver_time:                       0.
% 7.94/1.50  smt_solver_time:                        0.
% 7.94/1.50  smt_fast_solver_time:                   0.
% 7.94/1.50  prop_fast_solver_time:                  0.
% 7.94/1.50  prop_unsat_core_time:                   0.
% 7.94/1.50  
% 7.94/1.50  ------ QBF
% 7.94/1.50  
% 7.94/1.50  qbf_q_res:                              0
% 7.94/1.50  qbf_num_tautologies:                    0
% 7.94/1.50  qbf_prep_cycles:                        0
% 7.94/1.50  
% 7.94/1.50  ------ BMC1
% 7.94/1.50  
% 7.94/1.50  bmc1_current_bound:                     -1
% 7.94/1.50  bmc1_last_solved_bound:                 -1
% 7.94/1.50  bmc1_unsat_core_size:                   -1
% 7.94/1.50  bmc1_unsat_core_parents_size:           -1
% 7.94/1.50  bmc1_merge_next_fun:                    0
% 7.94/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.94/1.50  
% 7.94/1.50  ------ Instantiation
% 7.94/1.50  
% 7.94/1.50  inst_num_of_clauses:                    1598
% 7.94/1.50  inst_num_in_passive:                    936
% 7.94/1.50  inst_num_in_active:                     644
% 7.94/1.50  inst_num_in_unprocessed:                22
% 7.94/1.50  inst_num_of_loops:                      830
% 7.94/1.50  inst_num_of_learning_restarts:          0
% 7.94/1.50  inst_num_moves_active_passive:          186
% 7.94/1.50  inst_lit_activity:                      0
% 7.94/1.50  inst_lit_activity_moves:                0
% 7.94/1.50  inst_num_tautologies:                   0
% 7.94/1.50  inst_num_prop_implied:                  0
% 7.94/1.50  inst_num_existing_simplified:           0
% 7.94/1.50  inst_num_eq_res_simplified:             0
% 7.94/1.50  inst_num_child_elim:                    0
% 7.94/1.50  inst_num_of_dismatching_blockings:      2052
% 7.94/1.50  inst_num_of_non_proper_insts:           2249
% 7.94/1.50  inst_num_of_duplicates:                 0
% 7.94/1.50  inst_inst_num_from_inst_to_res:         0
% 7.94/1.50  inst_dismatching_checking_time:         0.
% 7.94/1.50  
% 7.94/1.50  ------ Resolution
% 7.94/1.50  
% 7.94/1.50  res_num_of_clauses:                     0
% 7.94/1.50  res_num_in_passive:                     0
% 7.94/1.50  res_num_in_active:                      0
% 7.94/1.50  res_num_of_loops:                       88
% 7.94/1.50  res_forward_subset_subsumed:            495
% 7.94/1.50  res_backward_subset_subsumed:           10
% 7.94/1.50  res_forward_subsumed:                   0
% 7.94/1.50  res_backward_subsumed:                  0
% 7.94/1.50  res_forward_subsumption_resolution:     0
% 7.94/1.50  res_backward_subsumption_resolution:    0
% 7.94/1.50  res_clause_to_clause_subsumption:       19601
% 7.94/1.50  res_orphan_elimination:                 0
% 7.94/1.50  res_tautology_del:                      205
% 7.94/1.50  res_num_eq_res_simplified:              0
% 7.94/1.50  res_num_sel_changes:                    0
% 7.94/1.50  res_moves_from_active_to_pass:          0
% 7.94/1.50  
% 7.94/1.50  ------ Superposition
% 7.94/1.50  
% 7.94/1.50  sup_time_total:                         0.
% 7.94/1.50  sup_time_generating:                    0.
% 7.94/1.50  sup_time_sim_full:                      0.
% 7.94/1.50  sup_time_sim_immed:                     0.
% 7.94/1.50  
% 7.94/1.50  sup_num_of_clauses:                     1935
% 7.94/1.50  sup_num_in_active:                      71
% 7.94/1.50  sup_num_in_passive:                     1864
% 7.94/1.50  sup_num_of_loops:                       164
% 7.94/1.50  sup_fw_superposition:                   4336
% 7.94/1.50  sup_bw_superposition:                   3882
% 7.94/1.50  sup_immediate_simplified:               5298
% 7.94/1.50  sup_given_eliminated:                   11
% 7.94/1.50  comparisons_done:                       0
% 7.94/1.50  comparisons_avoided:                    0
% 7.94/1.50  
% 7.94/1.50  ------ Simplifications
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  sim_fw_subset_subsumed:                 0
% 7.94/1.50  sim_bw_subset_subsumed:                 0
% 7.94/1.50  sim_fw_subsumed:                        804
% 7.94/1.50  sim_bw_subsumed:                        45
% 7.94/1.50  sim_fw_subsumption_res:                 0
% 7.94/1.50  sim_bw_subsumption_res:                 0
% 7.94/1.50  sim_tautology_del:                      34
% 7.94/1.50  sim_eq_tautology_del:                   2030
% 7.94/1.50  sim_eq_res_simp:                        0
% 7.94/1.50  sim_fw_demodulated:                     4560
% 7.94/1.50  sim_bw_demodulated:                     140
% 7.94/1.50  sim_light_normalised:                   1626
% 7.94/1.50  sim_joinable_taut:                      0
% 7.94/1.50  sim_joinable_simp:                      0
% 7.94/1.50  sim_ac_normalised:                      0
% 7.94/1.50  sim_smt_subsumption:                    0
% 7.94/1.50  
%------------------------------------------------------------------------------
