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
% DateTime   : Thu Dec  3 11:33:01 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 925 expanded)
%              Number of clauses        :   38 ( 146 expanded)
%              Number of leaves         :   16 ( 278 expanded)
%              Depth                    :   17
%              Number of atoms          :  138 (1126 expanded)
%              Number of equality atoms :   84 ( 914 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f42])).

fof(f71,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f62,f74,f74])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f59,f75,f75,f56])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f60,f56,f56,f75])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f61,f75])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f72,plain,(
    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f85,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(definition_unfolding,[],[f72,f75,f76])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_771,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_774,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_776,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2996,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_776])).

cnf(c_12512,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,X0),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_2996])).

cnf(c_13057,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_771,c_12512])).

cnf(c_17,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_14,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1492,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_8091,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_17,c_1492])).

cnf(c_13197,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)))) ),
    inference(superposition,[status(thm)],[c_13057,c_8091])).

cnf(c_13219,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
    inference(demodulation,[status(thm)],[c_13197,c_13057])).

cnf(c_12,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1428,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_17,c_12])).

cnf(c_1564,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1428,c_15])).

cnf(c_16,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_775,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1111,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_775,c_776])).

cnf(c_1566,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1428,c_1111])).

cnf(c_1568,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1564,c_1566])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_777,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1110,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_777,c_776])).

cnf(c_1569,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1568,c_1110])).

cnf(c_1934,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_1569,c_1569])).

cnf(c_1936,plain,
    ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1934])).

cnf(c_1563,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1428,c_14])).

cnf(c_1570,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1563,c_1428])).

cnf(c_2020,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1110,c_1570])).

cnf(c_2024,plain,
    ( sP0_iProver_split = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2020,c_1936])).

cnf(c_2025,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split)) = X0 ),
    inference(demodulation,[status(thm)],[c_2024,c_1570])).

cnf(c_13220,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_13219,c_1936,c_2025])).

cnf(c_21,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13220,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.71/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.01  
% 3.71/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.01  
% 3.71/1.01  ------  iProver source info
% 3.71/1.01  
% 3.71/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.01  git: non_committed_changes: false
% 3.71/1.01  git: last_make_outside_of_git: false
% 3.71/1.01  
% 3.71/1.01  ------ 
% 3.71/1.01  
% 3.71/1.01  ------ Input Options
% 3.71/1.01  
% 3.71/1.01  --out_options                           all
% 3.71/1.01  --tptp_safe_out                         true
% 3.71/1.01  --problem_path                          ""
% 3.71/1.01  --include_path                          ""
% 3.71/1.01  --clausifier                            res/vclausify_rel
% 3.71/1.01  --clausifier_options                    ""
% 3.71/1.01  --stdin                                 false
% 3.71/1.01  --stats_out                             all
% 3.71/1.01  
% 3.71/1.01  ------ General Options
% 3.71/1.01  
% 3.71/1.01  --fof                                   false
% 3.71/1.01  --time_out_real                         305.
% 3.71/1.01  --time_out_virtual                      -1.
% 3.71/1.01  --symbol_type_check                     false
% 3.71/1.01  --clausify_out                          false
% 3.71/1.01  --sig_cnt_out                           false
% 3.71/1.01  --trig_cnt_out                          false
% 3.71/1.01  --trig_cnt_out_tolerance                1.
% 3.71/1.01  --trig_cnt_out_sk_spl                   false
% 3.71/1.01  --abstr_cl_out                          false
% 3.71/1.01  
% 3.71/1.01  ------ Global Options
% 3.71/1.01  
% 3.71/1.01  --schedule                              default
% 3.71/1.01  --add_important_lit                     false
% 3.71/1.01  --prop_solver_per_cl                    1000
% 3.71/1.01  --min_unsat_core                        false
% 3.71/1.01  --soft_assumptions                      false
% 3.71/1.01  --soft_lemma_size                       3
% 3.71/1.01  --prop_impl_unit_size                   0
% 3.71/1.01  --prop_impl_unit                        []
% 3.71/1.01  --share_sel_clauses                     true
% 3.71/1.01  --reset_solvers                         false
% 3.71/1.01  --bc_imp_inh                            [conj_cone]
% 3.71/1.01  --conj_cone_tolerance                   3.
% 3.71/1.01  --extra_neg_conj                        none
% 3.71/1.01  --large_theory_mode                     true
% 3.71/1.01  --prolific_symb_bound                   200
% 3.71/1.01  --lt_threshold                          2000
% 3.71/1.01  --clause_weak_htbl                      true
% 3.71/1.01  --gc_record_bc_elim                     false
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing Options
% 3.71/1.01  
% 3.71/1.01  --preprocessing_flag                    true
% 3.71/1.01  --time_out_prep_mult                    0.1
% 3.71/1.01  --splitting_mode                        input
% 3.71/1.01  --splitting_grd                         true
% 3.71/1.01  --splitting_cvd                         false
% 3.71/1.01  --splitting_cvd_svl                     false
% 3.71/1.01  --splitting_nvd                         32
% 3.71/1.01  --sub_typing                            true
% 3.71/1.01  --prep_gs_sim                           true
% 3.71/1.01  --prep_unflatten                        true
% 3.71/1.01  --prep_res_sim                          true
% 3.71/1.01  --prep_upred                            true
% 3.71/1.01  --prep_sem_filter                       exhaustive
% 3.71/1.01  --prep_sem_filter_out                   false
% 3.71/1.01  --pred_elim                             true
% 3.71/1.01  --res_sim_input                         true
% 3.71/1.01  --eq_ax_congr_red                       true
% 3.71/1.01  --pure_diseq_elim                       true
% 3.71/1.01  --brand_transform                       false
% 3.71/1.01  --non_eq_to_eq                          false
% 3.71/1.01  --prep_def_merge                        true
% 3.71/1.01  --prep_def_merge_prop_impl              false
% 3.71/1.01  --prep_def_merge_mbd                    true
% 3.71/1.01  --prep_def_merge_tr_red                 false
% 3.71/1.01  --prep_def_merge_tr_cl                  false
% 3.71/1.01  --smt_preprocessing                     true
% 3.71/1.01  --smt_ac_axioms                         fast
% 3.71/1.01  --preprocessed_out                      false
% 3.71/1.01  --preprocessed_stats                    false
% 3.71/1.01  
% 3.71/1.01  ------ Abstraction refinement Options
% 3.71/1.01  
% 3.71/1.01  --abstr_ref                             []
% 3.71/1.01  --abstr_ref_prep                        false
% 3.71/1.01  --abstr_ref_until_sat                   false
% 3.71/1.01  --abstr_ref_sig_restrict                funpre
% 3.71/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.01  --abstr_ref_under                       []
% 3.71/1.01  
% 3.71/1.01  ------ SAT Options
% 3.71/1.01  
% 3.71/1.01  --sat_mode                              false
% 3.71/1.01  --sat_fm_restart_options                ""
% 3.71/1.01  --sat_gr_def                            false
% 3.71/1.01  --sat_epr_types                         true
% 3.71/1.01  --sat_non_cyclic_types                  false
% 3.71/1.01  --sat_finite_models                     false
% 3.71/1.01  --sat_fm_lemmas                         false
% 3.71/1.01  --sat_fm_prep                           false
% 3.71/1.01  --sat_fm_uc_incr                        true
% 3.71/1.01  --sat_out_model                         small
% 3.71/1.01  --sat_out_clauses                       false
% 3.71/1.01  
% 3.71/1.01  ------ QBF Options
% 3.71/1.01  
% 3.71/1.01  --qbf_mode                              false
% 3.71/1.01  --qbf_elim_univ                         false
% 3.71/1.01  --qbf_dom_inst                          none
% 3.71/1.01  --qbf_dom_pre_inst                      false
% 3.71/1.01  --qbf_sk_in                             false
% 3.71/1.01  --qbf_pred_elim                         true
% 3.71/1.01  --qbf_split                             512
% 3.71/1.01  
% 3.71/1.01  ------ BMC1 Options
% 3.71/1.01  
% 3.71/1.01  --bmc1_incremental                      false
% 3.71/1.01  --bmc1_axioms                           reachable_all
% 3.71/1.01  --bmc1_min_bound                        0
% 3.71/1.01  --bmc1_max_bound                        -1
% 3.71/1.01  --bmc1_max_bound_default                -1
% 3.71/1.01  --bmc1_symbol_reachability              true
% 3.71/1.01  --bmc1_property_lemmas                  false
% 3.71/1.01  --bmc1_k_induction                      false
% 3.71/1.01  --bmc1_non_equiv_states                 false
% 3.71/1.01  --bmc1_deadlock                         false
% 3.71/1.01  --bmc1_ucm                              false
% 3.71/1.01  --bmc1_add_unsat_core                   none
% 3.71/1.01  --bmc1_unsat_core_children              false
% 3.71/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.01  --bmc1_out_stat                         full
% 3.71/1.01  --bmc1_ground_init                      false
% 3.71/1.01  --bmc1_pre_inst_next_state              false
% 3.71/1.01  --bmc1_pre_inst_state                   false
% 3.71/1.01  --bmc1_pre_inst_reach_state             false
% 3.71/1.01  --bmc1_out_unsat_core                   false
% 3.71/1.01  --bmc1_aig_witness_out                  false
% 3.71/1.01  --bmc1_verbose                          false
% 3.71/1.01  --bmc1_dump_clauses_tptp                false
% 3.71/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.01  --bmc1_dump_file                        -
% 3.71/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.01  --bmc1_ucm_extend_mode                  1
% 3.71/1.01  --bmc1_ucm_init_mode                    2
% 3.71/1.01  --bmc1_ucm_cone_mode                    none
% 3.71/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.01  --bmc1_ucm_relax_model                  4
% 3.71/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.01  --bmc1_ucm_layered_model                none
% 3.71/1.01  --bmc1_ucm_max_lemma_size               10
% 3.71/1.01  
% 3.71/1.01  ------ AIG Options
% 3.71/1.01  
% 3.71/1.01  --aig_mode                              false
% 3.71/1.01  
% 3.71/1.01  ------ Instantiation Options
% 3.71/1.01  
% 3.71/1.01  --instantiation_flag                    true
% 3.71/1.01  --inst_sos_flag                         true
% 3.71/1.01  --inst_sos_phase                        true
% 3.71/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.01  --inst_lit_sel_side                     num_symb
% 3.71/1.01  --inst_solver_per_active                1400
% 3.71/1.01  --inst_solver_calls_frac                1.
% 3.71/1.01  --inst_passive_queue_type               priority_queues
% 3.71/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.01  --inst_passive_queues_freq              [25;2]
% 3.71/1.01  --inst_dismatching                      true
% 3.71/1.01  --inst_eager_unprocessed_to_passive     true
% 3.71/1.01  --inst_prop_sim_given                   true
% 3.71/1.01  --inst_prop_sim_new                     false
% 3.71/1.01  --inst_subs_new                         false
% 3.71/1.01  --inst_eq_res_simp                      false
% 3.71/1.01  --inst_subs_given                       false
% 3.71/1.01  --inst_orphan_elimination               true
% 3.71/1.01  --inst_learning_loop_flag               true
% 3.71/1.01  --inst_learning_start                   3000
% 3.71/1.01  --inst_learning_factor                  2
% 3.71/1.01  --inst_start_prop_sim_after_learn       3
% 3.71/1.01  --inst_sel_renew                        solver
% 3.71/1.01  --inst_lit_activity_flag                true
% 3.71/1.01  --inst_restr_to_given                   false
% 3.71/1.01  --inst_activity_threshold               500
% 3.71/1.01  --inst_out_proof                        true
% 3.71/1.01  
% 3.71/1.01  ------ Resolution Options
% 3.71/1.01  
% 3.71/1.01  --resolution_flag                       true
% 3.71/1.01  --res_lit_sel                           adaptive
% 3.71/1.01  --res_lit_sel_side                      none
% 3.71/1.01  --res_ordering                          kbo
% 3.71/1.01  --res_to_prop_solver                    active
% 3.71/1.01  --res_prop_simpl_new                    false
% 3.71/1.01  --res_prop_simpl_given                  true
% 3.71/1.01  --res_passive_queue_type                priority_queues
% 3.71/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.01  --res_passive_queues_freq               [15;5]
% 3.71/1.01  --res_forward_subs                      full
% 3.71/1.01  --res_backward_subs                     full
% 3.71/1.01  --res_forward_subs_resolution           true
% 3.71/1.01  --res_backward_subs_resolution          true
% 3.71/1.01  --res_orphan_elimination                true
% 3.71/1.01  --res_time_limit                        2.
% 3.71/1.01  --res_out_proof                         true
% 3.71/1.01  
% 3.71/1.01  ------ Superposition Options
% 3.71/1.01  
% 3.71/1.01  --superposition_flag                    true
% 3.71/1.01  --sup_passive_queue_type                priority_queues
% 3.71/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.01  --demod_completeness_check              fast
% 3.71/1.01  --demod_use_ground                      true
% 3.71/1.01  --sup_to_prop_solver                    passive
% 3.71/1.01  --sup_prop_simpl_new                    true
% 3.71/1.01  --sup_prop_simpl_given                  true
% 3.71/1.01  --sup_fun_splitting                     true
% 3.71/1.01  --sup_smt_interval                      50000
% 3.71/1.01  
% 3.71/1.01  ------ Superposition Simplification Setup
% 3.71/1.01  
% 3.71/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/1.01  --sup_immed_triv                        [TrivRules]
% 3.71/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.01  --sup_immed_bw_main                     []
% 3.71/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.01  --sup_input_bw                          []
% 3.71/1.01  
% 3.71/1.01  ------ Combination Options
% 3.71/1.01  
% 3.71/1.01  --comb_res_mult                         3
% 3.71/1.01  --comb_sup_mult                         2
% 3.71/1.01  --comb_inst_mult                        10
% 3.71/1.01  
% 3.71/1.01  ------ Debug Options
% 3.71/1.01  
% 3.71/1.01  --dbg_backtrace                         false
% 3.71/1.01  --dbg_dump_prop_clauses                 false
% 3.71/1.01  --dbg_dump_prop_clauses_file            -
% 3.71/1.01  --dbg_out_stat                          false
% 3.71/1.01  ------ Parsing...
% 3.71/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.01  ------ Proving...
% 3.71/1.01  ------ Problem Properties 
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  clauses                                 22
% 3.71/1.01  conjectures                             2
% 3.71/1.01  EPR                                     6
% 3.71/1.01  Horn                                    18
% 3.71/1.01  unary                                   8
% 3.71/1.01  binary                                  10
% 3.71/1.01  lits                                    40
% 3.71/1.01  lits eq                                 7
% 3.71/1.01  fd_pure                                 0
% 3.71/1.01  fd_pseudo                               0
% 3.71/1.01  fd_cond                                 0
% 3.71/1.01  fd_pseudo_cond                          1
% 3.71/1.01  AC symbols                              0
% 3.71/1.01  
% 3.71/1.01  ------ Schedule dynamic 5 is on 
% 3.71/1.01  
% 3.71/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ 
% 3.71/1.01  Current options:
% 3.71/1.01  ------ 
% 3.71/1.01  
% 3.71/1.01  ------ Input Options
% 3.71/1.01  
% 3.71/1.01  --out_options                           all
% 3.71/1.01  --tptp_safe_out                         true
% 3.71/1.01  --problem_path                          ""
% 3.71/1.01  --include_path                          ""
% 3.71/1.01  --clausifier                            res/vclausify_rel
% 3.71/1.01  --clausifier_options                    ""
% 3.71/1.01  --stdin                                 false
% 3.71/1.01  --stats_out                             all
% 3.71/1.01  
% 3.71/1.01  ------ General Options
% 3.71/1.01  
% 3.71/1.01  --fof                                   false
% 3.71/1.01  --time_out_real                         305.
% 3.71/1.01  --time_out_virtual                      -1.
% 3.71/1.01  --symbol_type_check                     false
% 3.71/1.01  --clausify_out                          false
% 3.71/1.01  --sig_cnt_out                           false
% 3.71/1.01  --trig_cnt_out                          false
% 3.71/1.01  --trig_cnt_out_tolerance                1.
% 3.71/1.01  --trig_cnt_out_sk_spl                   false
% 3.71/1.01  --abstr_cl_out                          false
% 3.71/1.01  
% 3.71/1.01  ------ Global Options
% 3.71/1.01  
% 3.71/1.01  --schedule                              default
% 3.71/1.01  --add_important_lit                     false
% 3.71/1.01  --prop_solver_per_cl                    1000
% 3.71/1.01  --min_unsat_core                        false
% 3.71/1.01  --soft_assumptions                      false
% 3.71/1.01  --soft_lemma_size                       3
% 3.71/1.01  --prop_impl_unit_size                   0
% 3.71/1.01  --prop_impl_unit                        []
% 3.71/1.01  --share_sel_clauses                     true
% 3.71/1.01  --reset_solvers                         false
% 3.71/1.01  --bc_imp_inh                            [conj_cone]
% 3.71/1.01  --conj_cone_tolerance                   3.
% 3.71/1.01  --extra_neg_conj                        none
% 3.71/1.01  --large_theory_mode                     true
% 3.71/1.01  --prolific_symb_bound                   200
% 3.71/1.01  --lt_threshold                          2000
% 3.71/1.01  --clause_weak_htbl                      true
% 3.71/1.01  --gc_record_bc_elim                     false
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing Options
% 3.71/1.01  
% 3.71/1.01  --preprocessing_flag                    true
% 3.71/1.01  --time_out_prep_mult                    0.1
% 3.71/1.01  --splitting_mode                        input
% 3.71/1.01  --splitting_grd                         true
% 3.71/1.01  --splitting_cvd                         false
% 3.71/1.01  --splitting_cvd_svl                     false
% 3.71/1.01  --splitting_nvd                         32
% 3.71/1.01  --sub_typing                            true
% 3.71/1.01  --prep_gs_sim                           true
% 3.71/1.01  --prep_unflatten                        true
% 3.71/1.01  --prep_res_sim                          true
% 3.71/1.01  --prep_upred                            true
% 3.71/1.01  --prep_sem_filter                       exhaustive
% 3.71/1.01  --prep_sem_filter_out                   false
% 3.71/1.01  --pred_elim                             true
% 3.71/1.01  --res_sim_input                         true
% 3.71/1.01  --eq_ax_congr_red                       true
% 3.71/1.01  --pure_diseq_elim                       true
% 3.71/1.01  --brand_transform                       false
% 3.71/1.01  --non_eq_to_eq                          false
% 3.71/1.01  --prep_def_merge                        true
% 3.71/1.01  --prep_def_merge_prop_impl              false
% 3.71/1.01  --prep_def_merge_mbd                    true
% 3.71/1.01  --prep_def_merge_tr_red                 false
% 3.71/1.01  --prep_def_merge_tr_cl                  false
% 3.71/1.01  --smt_preprocessing                     true
% 3.71/1.01  --smt_ac_axioms                         fast
% 3.71/1.01  --preprocessed_out                      false
% 3.71/1.01  --preprocessed_stats                    false
% 3.71/1.01  
% 3.71/1.01  ------ Abstraction refinement Options
% 3.71/1.01  
% 3.71/1.01  --abstr_ref                             []
% 3.71/1.01  --abstr_ref_prep                        false
% 3.71/1.01  --abstr_ref_until_sat                   false
% 3.71/1.01  --abstr_ref_sig_restrict                funpre
% 3.71/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.01  --abstr_ref_under                       []
% 3.71/1.01  
% 3.71/1.01  ------ SAT Options
% 3.71/1.01  
% 3.71/1.01  --sat_mode                              false
% 3.71/1.01  --sat_fm_restart_options                ""
% 3.71/1.01  --sat_gr_def                            false
% 3.71/1.01  --sat_epr_types                         true
% 3.71/1.01  --sat_non_cyclic_types                  false
% 3.71/1.01  --sat_finite_models                     false
% 3.71/1.01  --sat_fm_lemmas                         false
% 3.71/1.01  --sat_fm_prep                           false
% 3.71/1.01  --sat_fm_uc_incr                        true
% 3.71/1.01  --sat_out_model                         small
% 3.71/1.01  --sat_out_clauses                       false
% 3.71/1.01  
% 3.71/1.01  ------ QBF Options
% 3.71/1.01  
% 3.71/1.01  --qbf_mode                              false
% 3.71/1.01  --qbf_elim_univ                         false
% 3.71/1.01  --qbf_dom_inst                          none
% 3.71/1.01  --qbf_dom_pre_inst                      false
% 3.71/1.01  --qbf_sk_in                             false
% 3.71/1.01  --qbf_pred_elim                         true
% 3.71/1.01  --qbf_split                             512
% 3.71/1.01  
% 3.71/1.01  ------ BMC1 Options
% 3.71/1.01  
% 3.71/1.01  --bmc1_incremental                      false
% 3.71/1.01  --bmc1_axioms                           reachable_all
% 3.71/1.01  --bmc1_min_bound                        0
% 3.71/1.01  --bmc1_max_bound                        -1
% 3.71/1.01  --bmc1_max_bound_default                -1
% 3.71/1.01  --bmc1_symbol_reachability              true
% 3.71/1.01  --bmc1_property_lemmas                  false
% 3.71/1.01  --bmc1_k_induction                      false
% 3.71/1.01  --bmc1_non_equiv_states                 false
% 3.71/1.01  --bmc1_deadlock                         false
% 3.71/1.01  --bmc1_ucm                              false
% 3.71/1.01  --bmc1_add_unsat_core                   none
% 3.71/1.01  --bmc1_unsat_core_children              false
% 3.71/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.01  --bmc1_out_stat                         full
% 3.71/1.01  --bmc1_ground_init                      false
% 3.71/1.01  --bmc1_pre_inst_next_state              false
% 3.71/1.01  --bmc1_pre_inst_state                   false
% 3.71/1.01  --bmc1_pre_inst_reach_state             false
% 3.71/1.01  --bmc1_out_unsat_core                   false
% 3.71/1.01  --bmc1_aig_witness_out                  false
% 3.71/1.01  --bmc1_verbose                          false
% 3.71/1.01  --bmc1_dump_clauses_tptp                false
% 3.71/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.01  --bmc1_dump_file                        -
% 3.71/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.01  --bmc1_ucm_extend_mode                  1
% 3.71/1.01  --bmc1_ucm_init_mode                    2
% 3.71/1.01  --bmc1_ucm_cone_mode                    none
% 3.71/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.01  --bmc1_ucm_relax_model                  4
% 3.71/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.01  --bmc1_ucm_layered_model                none
% 3.71/1.01  --bmc1_ucm_max_lemma_size               10
% 3.71/1.01  
% 3.71/1.01  ------ AIG Options
% 3.71/1.01  
% 3.71/1.01  --aig_mode                              false
% 3.71/1.01  
% 3.71/1.01  ------ Instantiation Options
% 3.71/1.01  
% 3.71/1.01  --instantiation_flag                    true
% 3.71/1.01  --inst_sos_flag                         true
% 3.71/1.01  --inst_sos_phase                        true
% 3.71/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.01  --inst_lit_sel_side                     none
% 3.71/1.01  --inst_solver_per_active                1400
% 3.71/1.01  --inst_solver_calls_frac                1.
% 3.71/1.01  --inst_passive_queue_type               priority_queues
% 3.71/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.01  --inst_passive_queues_freq              [25;2]
% 3.71/1.01  --inst_dismatching                      true
% 3.71/1.01  --inst_eager_unprocessed_to_passive     true
% 3.71/1.01  --inst_prop_sim_given                   true
% 3.71/1.01  --inst_prop_sim_new                     false
% 3.71/1.01  --inst_subs_new                         false
% 3.71/1.01  --inst_eq_res_simp                      false
% 3.71/1.01  --inst_subs_given                       false
% 3.71/1.01  --inst_orphan_elimination               true
% 3.71/1.01  --inst_learning_loop_flag               true
% 3.71/1.01  --inst_learning_start                   3000
% 3.71/1.01  --inst_learning_factor                  2
% 3.71/1.01  --inst_start_prop_sim_after_learn       3
% 3.71/1.01  --inst_sel_renew                        solver
% 3.71/1.01  --inst_lit_activity_flag                true
% 3.71/1.01  --inst_restr_to_given                   false
% 3.71/1.01  --inst_activity_threshold               500
% 3.71/1.01  --inst_out_proof                        true
% 3.71/1.01  
% 3.71/1.01  ------ Resolution Options
% 3.71/1.01  
% 3.71/1.01  --resolution_flag                       false
% 3.71/1.01  --res_lit_sel                           adaptive
% 3.71/1.01  --res_lit_sel_side                      none
% 3.71/1.01  --res_ordering                          kbo
% 3.71/1.01  --res_to_prop_solver                    active
% 3.71/1.01  --res_prop_simpl_new                    false
% 3.71/1.01  --res_prop_simpl_given                  true
% 3.71/1.01  --res_passive_queue_type                priority_queues
% 3.71/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.01  --res_passive_queues_freq               [15;5]
% 3.71/1.01  --res_forward_subs                      full
% 3.71/1.01  --res_backward_subs                     full
% 3.71/1.01  --res_forward_subs_resolution           true
% 3.71/1.01  --res_backward_subs_resolution          true
% 3.71/1.01  --res_orphan_elimination                true
% 3.71/1.01  --res_time_limit                        2.
% 3.71/1.01  --res_out_proof                         true
% 3.71/1.01  
% 3.71/1.01  ------ Superposition Options
% 3.71/1.01  
% 3.71/1.01  --superposition_flag                    true
% 3.71/1.01  --sup_passive_queue_type                priority_queues
% 3.71/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.01  --demod_completeness_check              fast
% 3.71/1.01  --demod_use_ground                      true
% 3.71/1.01  --sup_to_prop_solver                    passive
% 3.71/1.01  --sup_prop_simpl_new                    true
% 3.71/1.01  --sup_prop_simpl_given                  true
% 3.71/1.01  --sup_fun_splitting                     true
% 3.71/1.01  --sup_smt_interval                      50000
% 3.71/1.01  
% 3.71/1.01  ------ Superposition Simplification Setup
% 3.71/1.01  
% 3.71/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/1.01  --sup_immed_triv                        [TrivRules]
% 3.71/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.01  --sup_immed_bw_main                     []
% 3.71/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.01  --sup_input_bw                          []
% 3.71/1.01  
% 3.71/1.01  ------ Combination Options
% 3.71/1.01  
% 3.71/1.01  --comb_res_mult                         3
% 3.71/1.01  --comb_sup_mult                         2
% 3.71/1.01  --comb_inst_mult                        10
% 3.71/1.01  
% 3.71/1.01  ------ Debug Options
% 3.71/1.01  
% 3.71/1.01  --dbg_backtrace                         false
% 3.71/1.01  --dbg_dump_prop_clauses                 false
% 3.71/1.01  --dbg_dump_prop_clauses_file            -
% 3.71/1.01  --dbg_out_stat                          false
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Proving...
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  % SZS status Theorem for theBenchmark.p
% 3.71/1.01  
% 3.71/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.01  
% 3.71/1.01  fof(f20,conjecture,(
% 3.71/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f21,negated_conjecture,(
% 3.71/1.01    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.71/1.01    inference(negated_conjecture,[],[f20])).
% 3.71/1.01  
% 3.71/1.01  fof(f29,plain,(
% 3.71/1.01    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.71/1.01    inference(ennf_transformation,[],[f21])).
% 3.71/1.01  
% 3.71/1.01  fof(f42,plain,(
% 3.71/1.01    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4))),
% 3.71/1.01    introduced(choice_axiom,[])).
% 3.71/1.01  
% 3.71/1.01  fof(f43,plain,(
% 3.71/1.01    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4)),
% 3.71/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f42])).
% 3.71/1.01  
% 3.71/1.01  fof(f71,plain,(
% 3.71/1.01    r2_hidden(sK3,sK4)),
% 3.71/1.01    inference(cnf_transformation,[],[f43])).
% 3.71/1.01  
% 3.71/1.01  fof(f19,axiom,(
% 3.71/1.01    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f40,plain,(
% 3.71/1.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.71/1.01    inference(nnf_transformation,[],[f19])).
% 3.71/1.01  
% 3.71/1.01  fof(f41,plain,(
% 3.71/1.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.71/1.01    inference(flattening,[],[f40])).
% 3.71/1.01  
% 3.71/1.01  fof(f70,plain,(
% 3.71/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f41])).
% 3.71/1.01  
% 3.71/1.01  fof(f15,axiom,(
% 3.71/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f64,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f15])).
% 3.71/1.01  
% 3.71/1.01  fof(f16,axiom,(
% 3.71/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f65,plain,(
% 3.71/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f16])).
% 3.71/1.01  
% 3.71/1.01  fof(f17,axiom,(
% 3.71/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f66,plain,(
% 3.71/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f17])).
% 3.71/1.01  
% 3.71/1.01  fof(f73,plain,(
% 3.71/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.71/1.01    inference(definition_unfolding,[],[f65,f66])).
% 3.71/1.01  
% 3.71/1.01  fof(f74,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.71/1.01    inference(definition_unfolding,[],[f64,f73])).
% 3.71/1.01  
% 3.71/1.01  fof(f82,plain,(
% 3.71/1.01    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.71/1.01    inference(definition_unfolding,[],[f70,f74])).
% 3.71/1.01  
% 3.71/1.01  fof(f9,axiom,(
% 3.71/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f28,plain,(
% 3.71/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.71/1.01    inference(ennf_transformation,[],[f9])).
% 3.71/1.01  
% 3.71/1.01  fof(f58,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f28])).
% 3.71/1.01  
% 3.71/1.01  fof(f13,axiom,(
% 3.71/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f62,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f13])).
% 3.71/1.01  
% 3.71/1.01  fof(f81,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.71/1.01    inference(definition_unfolding,[],[f62,f74,f74])).
% 3.71/1.01  
% 3.71/1.01  fof(f10,axiom,(
% 3.71/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f59,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.71/1.01    inference(cnf_transformation,[],[f10])).
% 3.71/1.01  
% 3.71/1.01  fof(f18,axiom,(
% 3.71/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f67,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.71/1.01    inference(cnf_transformation,[],[f18])).
% 3.71/1.01  
% 3.71/1.01  fof(f75,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.71/1.01    inference(definition_unfolding,[],[f67,f74])).
% 3.71/1.01  
% 3.71/1.01  fof(f7,axiom,(
% 3.71/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f56,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.71/1.01    inference(cnf_transformation,[],[f7])).
% 3.71/1.01  
% 3.71/1.01  fof(f78,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.71/1.01    inference(definition_unfolding,[],[f59,f75,f75,f56])).
% 3.71/1.01  
% 3.71/1.01  fof(f11,axiom,(
% 3.71/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f60,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f11])).
% 3.71/1.01  
% 3.71/1.01  fof(f79,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 3.71/1.01    inference(definition_unfolding,[],[f60,f56,f56,f75])).
% 3.71/1.01  
% 3.71/1.01  fof(f8,axiom,(
% 3.71/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f57,plain,(
% 3.71/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.71/1.01    inference(cnf_transformation,[],[f8])).
% 3.71/1.01  
% 3.71/1.01  fof(f77,plain,(
% 3.71/1.01    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.71/1.01    inference(definition_unfolding,[],[f57,f75])).
% 3.71/1.01  
% 3.71/1.01  fof(f12,axiom,(
% 3.71/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f61,plain,(
% 3.71/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.71/1.01    inference(cnf_transformation,[],[f12])).
% 3.71/1.01  
% 3.71/1.01  fof(f80,plain,(
% 3.71/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.71/1.01    inference(definition_unfolding,[],[f61,f75])).
% 3.71/1.01  
% 3.71/1.01  fof(f6,axiom,(
% 3.71/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f38,plain,(
% 3.71/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/1.01    inference(nnf_transformation,[],[f6])).
% 3.71/1.01  
% 3.71/1.01  fof(f39,plain,(
% 3.71/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/1.01    inference(flattening,[],[f38])).
% 3.71/1.01  
% 3.71/1.01  fof(f54,plain,(
% 3.71/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.71/1.01    inference(cnf_transformation,[],[f39])).
% 3.71/1.01  
% 3.71/1.01  fof(f86,plain,(
% 3.71/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.71/1.01    inference(equality_resolution,[],[f54])).
% 3.71/1.01  
% 3.71/1.01  fof(f72,plain,(
% 3.71/1.01    k2_xboole_0(k1_tarski(sK3),sK4) != sK4),
% 3.71/1.01    inference(cnf_transformation,[],[f43])).
% 3.71/1.01  
% 3.71/1.01  fof(f14,axiom,(
% 3.71/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f63,plain,(
% 3.71/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f14])).
% 3.71/1.01  
% 3.71/1.01  fof(f76,plain,(
% 3.71/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.71/1.01    inference(definition_unfolding,[],[f63,f74])).
% 3.71/1.01  
% 3.71/1.01  fof(f85,plain,(
% 3.71/1.01    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4),
% 3.71/1.01    inference(definition_unfolding,[],[f72,f75,f76])).
% 3.71/1.01  
% 3.71/1.01  cnf(c_22,negated_conjecture,
% 3.71/1.01      ( r2_hidden(sK3,sK4) ),
% 3.71/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_771,plain,
% 3.71/1.01      ( r2_hidden(sK3,sK4) = iProver_top ),
% 3.71/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_18,plain,
% 3.71/1.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 3.71/1.01      | ~ r2_hidden(X1,X2)
% 3.71/1.01      | ~ r2_hidden(X0,X2) ),
% 3.71/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_774,plain,
% 3.71/1.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
% 3.71/1.01      | r2_hidden(X0,X2) != iProver_top
% 3.71/1.01      | r2_hidden(X1,X2) != iProver_top ),
% 3.71/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_13,plain,
% 3.71/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.71/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_776,plain,
% 3.71/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.71/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_2996,plain,
% 3.71/1.01      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 3.71/1.01      | r2_hidden(X1,X2) != iProver_top
% 3.71/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_774,c_776]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_12512,plain,
% 3.71/1.01      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,X0),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,X0)
% 3.71/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_771,c_2996]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_13057,plain,
% 3.71/1.01      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_771,c_12512]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_17,plain,
% 3.71/1.01      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.71/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_14,plain,
% 3.71/1.01      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.71/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_15,plain,
% 3.71/1.01      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.71/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1492,plain,
% 3.71/1.01      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_8091,plain,
% 3.71/1.01      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_17,c_1492]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_13197,plain,
% 3.71/1.01      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)))) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_13057,c_8091]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_13219,plain,
% 3.71/1.01      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_13197,c_13057]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_12,plain,
% 3.71/1.01      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.71/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1428,plain,
% 3.71/1.01      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_17,c_12]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1564,plain,
% 3.71/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_1428,c_15]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_16,plain,
% 3.71/1.01      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 3.71/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_775,plain,
% 3.71/1.01      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 3.71/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1111,plain,
% 3.71/1.01      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_775,c_776]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1566,plain,
% 3.71/1.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_1428,c_1111]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1568,plain,
% 3.71/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_1564,c_1566]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_10,plain,
% 3.71/1.01      ( r1_tarski(X0,X0) ),
% 3.71/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_777,plain,
% 3.71/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.71/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1110,plain,
% 3.71/1.01      ( k3_xboole_0(X0,X0) = X0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_777,c_776]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1569,plain,
% 3.71/1.01      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.71/1.01      inference(light_normalisation,[status(thm)],[c_1568,c_1110]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1934,plain,
% 3.71/1.01      ( k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_1569,c_1569]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1936,plain,
% 3.71/1.01      ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
% 3.71/1.01      inference(splitting,
% 3.71/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.71/1.01                [c_1934]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1563,plain,
% 3.71/1.01      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_1428,c_14]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1570,plain,
% 3.71/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_1563,c_1428]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_2020,plain,
% 3.71/1.01      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_1110,c_1570]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_2024,plain,
% 3.71/1.01      ( sP0_iProver_split = k1_xboole_0 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_2020,c_1936]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_2025,plain,
% 3.71/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split)) = X0 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_2024,c_1570]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_13220,plain,
% 3.71/1.01      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) = sK4 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_13219,c_1936,c_2025]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_21,negated_conjecture,
% 3.71/1.01      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
% 3.71/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(contradiction,plain,
% 3.71/1.01      ( $false ),
% 3.71/1.01      inference(minisat,[status(thm)],[c_13220,c_21]) ).
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.01  
% 3.71/1.01  ------                               Statistics
% 3.71/1.01  
% 3.71/1.01  ------ General
% 3.71/1.01  
% 3.71/1.01  abstr_ref_over_cycles:                  0
% 3.71/1.01  abstr_ref_under_cycles:                 0
% 3.71/1.01  gc_basic_clause_elim:                   0
% 3.71/1.01  forced_gc_time:                         0
% 3.71/1.01  parsing_time:                           0.012
% 3.71/1.01  unif_index_cands_time:                  0.
% 3.71/1.01  unif_index_add_time:                    0.
% 3.71/1.01  orderings_time:                         0.
% 3.71/1.01  out_proof_time:                         0.009
% 3.71/1.01  total_time:                             0.426
% 3.71/1.01  num_of_symbols:                         45
% 3.71/1.01  num_of_terms:                           12897
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing
% 3.71/1.01  
% 3.71/1.01  num_of_splits:                          0
% 3.71/1.01  num_of_split_atoms:                     1
% 3.71/1.01  num_of_reused_defs:                     0
% 3.71/1.01  num_eq_ax_congr_red:                    27
% 3.71/1.01  num_of_sem_filtered_clauses:            1
% 3.71/1.01  num_of_subtypes:                        0
% 3.71/1.01  monotx_restored_types:                  0
% 3.71/1.01  sat_num_of_epr_types:                   0
% 3.71/1.01  sat_num_of_non_cyclic_types:            0
% 3.71/1.01  sat_guarded_non_collapsed_types:        0
% 3.71/1.01  num_pure_diseq_elim:                    0
% 3.71/1.01  simp_replaced_by:                       0
% 3.71/1.01  res_preprocessed:                       105
% 3.71/1.01  prep_upred:                             0
% 3.71/1.01  prep_unflattend:                        0
% 3.71/1.01  smt_new_axioms:                         0
% 3.71/1.01  pred_elim_cands:                        3
% 3.71/1.01  pred_elim:                              0
% 3.71/1.01  pred_elim_cl:                           0
% 3.71/1.01  pred_elim_cycles:                       2
% 3.71/1.01  merged_defs:                            0
% 3.71/1.01  merged_defs_ncl:                        0
% 3.71/1.01  bin_hyper_res:                          0
% 3.71/1.01  prep_cycles:                            4
% 3.71/1.01  pred_elim_time:                         0.002
% 3.71/1.01  splitting_time:                         0.
% 3.71/1.01  sem_filter_time:                        0.
% 3.71/1.01  monotx_time:                            0.001
% 3.71/1.01  subtype_inf_time:                       0.
% 3.71/1.01  
% 3.71/1.01  ------ Problem properties
% 3.71/1.01  
% 3.71/1.01  clauses:                                22
% 3.71/1.01  conjectures:                            2
% 3.71/1.01  epr:                                    6
% 3.71/1.01  horn:                                   18
% 3.71/1.01  ground:                                 2
% 3.71/1.01  unary:                                  8
% 3.71/1.01  binary:                                 10
% 3.71/1.01  lits:                                   40
% 3.71/1.01  lits_eq:                                7
% 3.71/1.01  fd_pure:                                0
% 3.71/1.01  fd_pseudo:                              0
% 3.71/1.01  fd_cond:                                0
% 3.71/1.01  fd_pseudo_cond:                         1
% 3.71/1.01  ac_symbols:                             0
% 3.71/1.01  
% 3.71/1.01  ------ Propositional Solver
% 3.71/1.01  
% 3.71/1.01  prop_solver_calls:                      30
% 3.71/1.01  prop_fast_solver_calls:                 653
% 3.71/1.01  smt_solver_calls:                       0
% 3.71/1.01  smt_fast_solver_calls:                  0
% 3.71/1.01  prop_num_of_clauses:                    5056
% 3.71/1.01  prop_preprocess_simplified:             14667
% 3.71/1.01  prop_fo_subsumed:                       0
% 3.71/1.01  prop_solver_time:                       0.
% 3.71/1.01  smt_solver_time:                        0.
% 3.71/1.01  smt_fast_solver_time:                   0.
% 3.71/1.01  prop_fast_solver_time:                  0.
% 3.71/1.01  prop_unsat_core_time:                   0.
% 3.71/1.01  
% 3.71/1.01  ------ QBF
% 3.71/1.01  
% 3.71/1.01  qbf_q_res:                              0
% 3.71/1.01  qbf_num_tautologies:                    0
% 3.71/1.01  qbf_prep_cycles:                        0
% 3.71/1.01  
% 3.71/1.01  ------ BMC1
% 3.71/1.01  
% 3.71/1.01  bmc1_current_bound:                     -1
% 3.71/1.01  bmc1_last_solved_bound:                 -1
% 3.71/1.01  bmc1_unsat_core_size:                   -1
% 3.71/1.01  bmc1_unsat_core_parents_size:           -1
% 3.71/1.01  bmc1_merge_next_fun:                    0
% 3.71/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.01  
% 3.71/1.01  ------ Instantiation
% 3.71/1.01  
% 3.71/1.01  inst_num_of_clauses:                    1528
% 3.71/1.01  inst_num_in_passive:                    831
% 3.71/1.01  inst_num_in_active:                     549
% 3.71/1.01  inst_num_in_unprocessed:                148
% 3.71/1.01  inst_num_of_loops:                      640
% 3.71/1.01  inst_num_of_learning_restarts:          0
% 3.71/1.01  inst_num_moves_active_passive:          91
% 3.71/1.01  inst_lit_activity:                      0
% 3.71/1.01  inst_lit_activity_moves:                0
% 3.71/1.01  inst_num_tautologies:                   0
% 3.71/1.01  inst_num_prop_implied:                  0
% 3.71/1.01  inst_num_existing_simplified:           0
% 3.71/1.01  inst_num_eq_res_simplified:             0
% 3.71/1.01  inst_num_child_elim:                    0
% 3.71/1.01  inst_num_of_dismatching_blockings:      791
% 3.71/1.01  inst_num_of_non_proper_insts:           1881
% 3.71/1.01  inst_num_of_duplicates:                 0
% 3.71/1.01  inst_inst_num_from_inst_to_res:         0
% 3.71/1.01  inst_dismatching_checking_time:         0.
% 3.71/1.01  
% 3.71/1.01  ------ Resolution
% 3.71/1.01  
% 3.71/1.01  res_num_of_clauses:                     0
% 3.71/1.01  res_num_in_passive:                     0
% 3.71/1.01  res_num_in_active:                      0
% 3.71/1.01  res_num_of_loops:                       109
% 3.71/1.01  res_forward_subset_subsumed:            175
% 3.71/1.01  res_backward_subset_subsumed:           4
% 3.71/1.01  res_forward_subsumed:                   0
% 3.71/1.01  res_backward_subsumed:                  0
% 3.71/1.01  res_forward_subsumption_resolution:     0
% 3.71/1.01  res_backward_subsumption_resolution:    0
% 3.71/1.01  res_clause_to_clause_subsumption:       2111
% 3.71/1.01  res_orphan_elimination:                 0
% 3.71/1.01  res_tautology_del:                      91
% 3.71/1.01  res_num_eq_res_simplified:              0
% 3.71/1.01  res_num_sel_changes:                    0
% 3.71/1.01  res_moves_from_active_to_pass:          0
% 3.71/1.01  
% 3.71/1.01  ------ Superposition
% 3.71/1.01  
% 3.71/1.01  sup_time_total:                         0.
% 3.71/1.01  sup_time_generating:                    0.
% 3.71/1.01  sup_time_sim_full:                      0.
% 3.71/1.01  sup_time_sim_immed:                     0.
% 3.71/1.01  
% 3.71/1.01  sup_num_of_clauses:                     266
% 3.71/1.01  sup_num_in_active:                      116
% 3.71/1.01  sup_num_in_passive:                     150
% 3.71/1.01  sup_num_of_loops:                       126
% 3.71/1.01  sup_fw_superposition:                   990
% 3.71/1.01  sup_bw_superposition:                   411
% 3.71/1.01  sup_immediate_simplified:               358
% 3.71/1.01  sup_given_eliminated:                   2
% 3.71/1.01  comparisons_done:                       0
% 3.71/1.01  comparisons_avoided:                    0
% 3.71/1.01  
% 3.71/1.01  ------ Simplifications
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  sim_fw_subset_subsumed:                 2
% 3.71/1.01  sim_bw_subset_subsumed:                 0
% 3.71/1.01  sim_fw_subsumed:                        93
% 3.71/1.01  sim_bw_subsumed:                        4
% 3.71/1.01  sim_fw_subsumption_res:                 0
% 3.71/1.01  sim_bw_subsumption_res:                 0
% 3.71/1.01  sim_tautology_del:                      14
% 3.71/1.01  sim_eq_tautology_del:                   60
% 3.71/1.01  sim_eq_res_simp:                        0
% 3.71/1.01  sim_fw_demodulated:                     216
% 3.71/1.01  sim_bw_demodulated:                     12
% 3.71/1.01  sim_light_normalised:                   195
% 3.71/1.01  sim_joinable_taut:                      0
% 3.71/1.01  sim_joinable_simp:                      0
% 3.71/1.01  sim_ac_normalised:                      0
% 3.71/1.01  sim_smt_subsumption:                    0
% 3.71/1.01  
%------------------------------------------------------------------------------
