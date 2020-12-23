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
% DateTime   : Thu Dec  3 11:33:02 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 558 expanded)
%              Number of clauses        :   34 (  72 expanded)
%              Number of leaves         :   16 ( 173 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 648 expanded)
%              Number of equality atoms :   77 ( 551 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

fof(f41,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f41])).

fof(f69,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f71])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f75,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f44,f73,f73])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f59,f73,f73,f56])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f60,f56,f56,f73])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f70,plain,(
    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(definition_unfolding,[],[f70,f73,f74])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_934,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_936,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_938,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2252,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_938])).

cnf(c_12122,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_934,c_2252])).

cnf(c_1,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1484,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_15,c_16])).

cnf(c_8920,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1,c_1484])).

cnf(c_13121,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)))) ),
    inference(superposition,[status(thm)],[c_12122,c_8920])).

cnf(c_13179,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_13121,c_12122])).

cnf(c_13,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1388,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_13])).

cnf(c_1618,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1388,c_15])).

cnf(c_1619,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1618,c_1388])).

cnf(c_1613,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1388,c_16])).

cnf(c_17,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_937,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1130,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_937,c_938])).

cnf(c_1616,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1388,c_1130])).

cnf(c_1626,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1613,c_1616])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_939,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1129,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_939,c_938])).

cnf(c_1628,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1626,c_1129])).

cnf(c_1837,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1129,c_1619])).

cnf(c_1960,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1628,c_1837])).

cnf(c_13181,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_13179,c_1619,c_1960])).

cnf(c_20,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f82])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13181,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.62/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/0.96  
% 3.62/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.96  
% 3.62/0.96  ------  iProver source info
% 3.62/0.96  
% 3.62/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.96  git: non_committed_changes: false
% 3.62/0.96  git: last_make_outside_of_git: false
% 3.62/0.96  
% 3.62/0.96  ------ 
% 3.62/0.96  
% 3.62/0.96  ------ Input Options
% 3.62/0.96  
% 3.62/0.96  --out_options                           all
% 3.62/0.96  --tptp_safe_out                         true
% 3.62/0.96  --problem_path                          ""
% 3.62/0.96  --include_path                          ""
% 3.62/0.96  --clausifier                            res/vclausify_rel
% 3.62/0.96  --clausifier_options                    --mode clausify
% 3.62/0.96  --stdin                                 false
% 3.62/0.96  --stats_out                             all
% 3.62/0.96  
% 3.62/0.96  ------ General Options
% 3.62/0.96  
% 3.62/0.96  --fof                                   false
% 3.62/0.96  --time_out_real                         305.
% 3.62/0.96  --time_out_virtual                      -1.
% 3.62/0.96  --symbol_type_check                     false
% 3.62/0.96  --clausify_out                          false
% 3.62/0.96  --sig_cnt_out                           false
% 3.62/0.96  --trig_cnt_out                          false
% 3.62/0.96  --trig_cnt_out_tolerance                1.
% 3.62/0.96  --trig_cnt_out_sk_spl                   false
% 3.62/0.96  --abstr_cl_out                          false
% 3.62/0.96  
% 3.62/0.96  ------ Global Options
% 3.62/0.96  
% 3.62/0.96  --schedule                              default
% 3.62/0.96  --add_important_lit                     false
% 3.62/0.96  --prop_solver_per_cl                    1000
% 3.62/0.96  --min_unsat_core                        false
% 3.62/0.96  --soft_assumptions                      false
% 3.62/0.96  --soft_lemma_size                       3
% 3.62/0.96  --prop_impl_unit_size                   0
% 3.62/0.96  --prop_impl_unit                        []
% 3.62/0.96  --share_sel_clauses                     true
% 3.62/0.96  --reset_solvers                         false
% 3.62/0.96  --bc_imp_inh                            [conj_cone]
% 3.62/0.96  --conj_cone_tolerance                   3.
% 3.62/0.96  --extra_neg_conj                        none
% 3.62/0.96  --large_theory_mode                     true
% 3.62/0.96  --prolific_symb_bound                   200
% 3.62/0.96  --lt_threshold                          2000
% 3.62/0.96  --clause_weak_htbl                      true
% 3.62/0.96  --gc_record_bc_elim                     false
% 3.62/0.96  
% 3.62/0.96  ------ Preprocessing Options
% 3.62/0.96  
% 3.62/0.96  --preprocessing_flag                    true
% 3.62/0.96  --time_out_prep_mult                    0.1
% 3.62/0.96  --splitting_mode                        input
% 3.62/0.96  --splitting_grd                         true
% 3.62/0.96  --splitting_cvd                         false
% 3.62/0.96  --splitting_cvd_svl                     false
% 3.62/0.96  --splitting_nvd                         32
% 3.62/0.96  --sub_typing                            true
% 3.62/0.96  --prep_gs_sim                           true
% 3.62/0.96  --prep_unflatten                        true
% 3.62/0.96  --prep_res_sim                          true
% 3.62/0.96  --prep_upred                            true
% 3.62/0.96  --prep_sem_filter                       exhaustive
% 3.62/0.96  --prep_sem_filter_out                   false
% 3.62/0.96  --pred_elim                             true
% 3.62/0.96  --res_sim_input                         true
% 3.62/0.96  --eq_ax_congr_red                       true
% 3.62/0.96  --pure_diseq_elim                       true
% 3.62/0.96  --brand_transform                       false
% 3.62/0.96  --non_eq_to_eq                          false
% 3.62/0.96  --prep_def_merge                        true
% 3.62/0.96  --prep_def_merge_prop_impl              false
% 3.62/0.96  --prep_def_merge_mbd                    true
% 3.62/0.96  --prep_def_merge_tr_red                 false
% 3.62/0.96  --prep_def_merge_tr_cl                  false
% 3.62/0.96  --smt_preprocessing                     true
% 3.62/0.96  --smt_ac_axioms                         fast
% 3.62/0.96  --preprocessed_out                      false
% 3.62/0.96  --preprocessed_stats                    false
% 3.62/0.96  
% 3.62/0.96  ------ Abstraction refinement Options
% 3.62/0.96  
% 3.62/0.96  --abstr_ref                             []
% 3.62/0.96  --abstr_ref_prep                        false
% 3.62/0.96  --abstr_ref_until_sat                   false
% 3.62/0.96  --abstr_ref_sig_restrict                funpre
% 3.62/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.96  --abstr_ref_under                       []
% 3.62/0.96  
% 3.62/0.96  ------ SAT Options
% 3.62/0.96  
% 3.62/0.96  --sat_mode                              false
% 3.62/0.96  --sat_fm_restart_options                ""
% 3.62/0.96  --sat_gr_def                            false
% 3.62/0.96  --sat_epr_types                         true
% 3.62/0.96  --sat_non_cyclic_types                  false
% 3.62/0.96  --sat_finite_models                     false
% 3.62/0.96  --sat_fm_lemmas                         false
% 3.62/0.96  --sat_fm_prep                           false
% 3.62/0.96  --sat_fm_uc_incr                        true
% 3.62/0.96  --sat_out_model                         small
% 3.62/0.96  --sat_out_clauses                       false
% 3.62/0.96  
% 3.62/0.96  ------ QBF Options
% 3.62/0.96  
% 3.62/0.96  --qbf_mode                              false
% 3.62/0.96  --qbf_elim_univ                         false
% 3.62/0.96  --qbf_dom_inst                          none
% 3.62/0.96  --qbf_dom_pre_inst                      false
% 3.62/0.96  --qbf_sk_in                             false
% 3.62/0.96  --qbf_pred_elim                         true
% 3.62/0.96  --qbf_split                             512
% 3.62/0.96  
% 3.62/0.96  ------ BMC1 Options
% 3.62/0.96  
% 3.62/0.96  --bmc1_incremental                      false
% 3.62/0.96  --bmc1_axioms                           reachable_all
% 3.62/0.96  --bmc1_min_bound                        0
% 3.62/0.96  --bmc1_max_bound                        -1
% 3.62/0.96  --bmc1_max_bound_default                -1
% 3.62/0.96  --bmc1_symbol_reachability              true
% 3.62/0.96  --bmc1_property_lemmas                  false
% 3.62/0.96  --bmc1_k_induction                      false
% 3.62/0.96  --bmc1_non_equiv_states                 false
% 3.62/0.96  --bmc1_deadlock                         false
% 3.62/0.96  --bmc1_ucm                              false
% 3.62/0.96  --bmc1_add_unsat_core                   none
% 3.62/0.96  --bmc1_unsat_core_children              false
% 3.62/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.96  --bmc1_out_stat                         full
% 3.62/0.96  --bmc1_ground_init                      false
% 3.62/0.96  --bmc1_pre_inst_next_state              false
% 3.62/0.96  --bmc1_pre_inst_state                   false
% 3.62/0.96  --bmc1_pre_inst_reach_state             false
% 3.62/0.96  --bmc1_out_unsat_core                   false
% 3.62/0.96  --bmc1_aig_witness_out                  false
% 3.62/0.96  --bmc1_verbose                          false
% 3.62/0.96  --bmc1_dump_clauses_tptp                false
% 3.62/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.96  --bmc1_dump_file                        -
% 3.62/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.96  --bmc1_ucm_extend_mode                  1
% 3.62/0.96  --bmc1_ucm_init_mode                    2
% 3.62/0.96  --bmc1_ucm_cone_mode                    none
% 3.62/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.96  --bmc1_ucm_relax_model                  4
% 3.62/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.96  --bmc1_ucm_layered_model                none
% 3.62/0.96  --bmc1_ucm_max_lemma_size               10
% 3.62/0.96  
% 3.62/0.96  ------ AIG Options
% 3.62/0.96  
% 3.62/0.96  --aig_mode                              false
% 3.62/0.96  
% 3.62/0.96  ------ Instantiation Options
% 3.62/0.96  
% 3.62/0.96  --instantiation_flag                    true
% 3.62/0.96  --inst_sos_flag                         false
% 3.62/0.96  --inst_sos_phase                        true
% 3.62/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.96  --inst_lit_sel_side                     num_symb
% 3.62/0.96  --inst_solver_per_active                1400
% 3.62/0.96  --inst_solver_calls_frac                1.
% 3.62/0.96  --inst_passive_queue_type               priority_queues
% 3.62/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.96  --inst_passive_queues_freq              [25;2]
% 3.62/0.96  --inst_dismatching                      true
% 3.62/0.96  --inst_eager_unprocessed_to_passive     true
% 3.62/0.96  --inst_prop_sim_given                   true
% 3.62/0.96  --inst_prop_sim_new                     false
% 3.62/0.96  --inst_subs_new                         false
% 3.62/0.96  --inst_eq_res_simp                      false
% 3.62/0.96  --inst_subs_given                       false
% 3.62/0.96  --inst_orphan_elimination               true
% 3.62/0.96  --inst_learning_loop_flag               true
% 3.62/0.96  --inst_learning_start                   3000
% 3.62/0.96  --inst_learning_factor                  2
% 3.62/0.96  --inst_start_prop_sim_after_learn       3
% 3.62/0.96  --inst_sel_renew                        solver
% 3.62/0.96  --inst_lit_activity_flag                true
% 3.62/0.96  --inst_restr_to_given                   false
% 3.62/0.96  --inst_activity_threshold               500
% 3.62/0.96  --inst_out_proof                        true
% 3.62/0.96  
% 3.62/0.96  ------ Resolution Options
% 3.62/0.96  
% 3.62/0.96  --resolution_flag                       true
% 3.62/0.96  --res_lit_sel                           adaptive
% 3.62/0.96  --res_lit_sel_side                      none
% 3.62/0.96  --res_ordering                          kbo
% 3.62/0.96  --res_to_prop_solver                    active
% 3.62/0.96  --res_prop_simpl_new                    false
% 3.62/0.96  --res_prop_simpl_given                  true
% 3.62/0.96  --res_passive_queue_type                priority_queues
% 3.62/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.96  --res_passive_queues_freq               [15;5]
% 3.62/0.96  --res_forward_subs                      full
% 3.62/0.96  --res_backward_subs                     full
% 3.62/0.96  --res_forward_subs_resolution           true
% 3.62/0.96  --res_backward_subs_resolution          true
% 3.62/0.96  --res_orphan_elimination                true
% 3.62/0.96  --res_time_limit                        2.
% 3.62/0.96  --res_out_proof                         true
% 3.62/0.96  
% 3.62/0.96  ------ Superposition Options
% 3.62/0.96  
% 3.62/0.96  --superposition_flag                    true
% 3.62/0.96  --sup_passive_queue_type                priority_queues
% 3.62/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.96  --demod_completeness_check              fast
% 3.62/0.96  --demod_use_ground                      true
% 3.62/0.96  --sup_to_prop_solver                    passive
% 3.62/0.96  --sup_prop_simpl_new                    true
% 3.62/0.96  --sup_prop_simpl_given                  true
% 3.62/0.96  --sup_fun_splitting                     false
% 3.62/0.96  --sup_smt_interval                      50000
% 3.62/0.96  
% 3.62/0.96  ------ Superposition Simplification Setup
% 3.62/0.96  
% 3.62/0.96  --sup_indices_passive                   []
% 3.62/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.96  --sup_full_bw                           [BwDemod]
% 3.62/0.96  --sup_immed_triv                        [TrivRules]
% 3.62/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.96  --sup_immed_bw_main                     []
% 3.62/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.96  
% 3.62/0.96  ------ Combination Options
% 3.62/0.96  
% 3.62/0.96  --comb_res_mult                         3
% 3.62/0.96  --comb_sup_mult                         2
% 3.62/0.96  --comb_inst_mult                        10
% 3.62/0.96  
% 3.62/0.96  ------ Debug Options
% 3.62/0.96  
% 3.62/0.96  --dbg_backtrace                         false
% 3.62/0.96  --dbg_dump_prop_clauses                 false
% 3.62/0.96  --dbg_dump_prop_clauses_file            -
% 3.62/0.96  --dbg_out_stat                          false
% 3.62/0.96  ------ Parsing...
% 3.62/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.96  
% 3.62/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.62/0.96  
% 3.62/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.96  
% 3.62/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.96  ------ Proving...
% 3.62/0.96  ------ Problem Properties 
% 3.62/0.96  
% 3.62/0.96  
% 3.62/0.96  clauses                                 21
% 3.62/0.96  conjectures                             2
% 3.62/0.96  EPR                                     6
% 3.62/0.96  Horn                                    17
% 3.62/0.96  unary                                   8
% 3.62/0.96  binary                                  10
% 3.62/0.96  lits                                    37
% 3.62/0.96  lits eq                                 7
% 3.62/0.96  fd_pure                                 0
% 3.62/0.96  fd_pseudo                               0
% 3.62/0.96  fd_cond                                 0
% 3.62/0.96  fd_pseudo_cond                          1
% 3.62/0.96  AC symbols                              0
% 3.62/0.96  
% 3.62/0.96  ------ Schedule dynamic 5 is on 
% 3.62/0.96  
% 3.62/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/0.96  
% 3.62/0.96  
% 3.62/0.96  ------ 
% 3.62/0.96  Current options:
% 3.62/0.96  ------ 
% 3.62/0.96  
% 3.62/0.96  ------ Input Options
% 3.62/0.96  
% 3.62/0.96  --out_options                           all
% 3.62/0.96  --tptp_safe_out                         true
% 3.62/0.96  --problem_path                          ""
% 3.62/0.96  --include_path                          ""
% 3.62/0.96  --clausifier                            res/vclausify_rel
% 3.62/0.96  --clausifier_options                    --mode clausify
% 3.62/0.96  --stdin                                 false
% 3.62/0.96  --stats_out                             all
% 3.62/0.96  
% 3.62/0.96  ------ General Options
% 3.62/0.96  
% 3.62/0.96  --fof                                   false
% 3.62/0.96  --time_out_real                         305.
% 3.62/0.96  --time_out_virtual                      -1.
% 3.62/0.96  --symbol_type_check                     false
% 3.62/0.96  --clausify_out                          false
% 3.62/0.96  --sig_cnt_out                           false
% 3.62/0.96  --trig_cnt_out                          false
% 3.62/0.96  --trig_cnt_out_tolerance                1.
% 3.62/0.96  --trig_cnt_out_sk_spl                   false
% 3.62/0.96  --abstr_cl_out                          false
% 3.62/0.96  
% 3.62/0.96  ------ Global Options
% 3.62/0.96  
% 3.62/0.96  --schedule                              default
% 3.62/0.96  --add_important_lit                     false
% 3.62/0.96  --prop_solver_per_cl                    1000
% 3.62/0.96  --min_unsat_core                        false
% 3.62/0.96  --soft_assumptions                      false
% 3.62/0.96  --soft_lemma_size                       3
% 3.62/0.96  --prop_impl_unit_size                   0
% 3.62/0.96  --prop_impl_unit                        []
% 3.62/0.96  --share_sel_clauses                     true
% 3.62/0.96  --reset_solvers                         false
% 3.62/0.96  --bc_imp_inh                            [conj_cone]
% 3.62/0.96  --conj_cone_tolerance                   3.
% 3.62/0.96  --extra_neg_conj                        none
% 3.62/0.96  --large_theory_mode                     true
% 3.62/0.96  --prolific_symb_bound                   200
% 3.62/0.96  --lt_threshold                          2000
% 3.62/0.96  --clause_weak_htbl                      true
% 3.62/0.96  --gc_record_bc_elim                     false
% 3.62/0.96  
% 3.62/0.96  ------ Preprocessing Options
% 3.62/0.96  
% 3.62/0.96  --preprocessing_flag                    true
% 3.62/0.96  --time_out_prep_mult                    0.1
% 3.62/0.96  --splitting_mode                        input
% 3.62/0.96  --splitting_grd                         true
% 3.62/0.96  --splitting_cvd                         false
% 3.62/0.96  --splitting_cvd_svl                     false
% 3.62/0.96  --splitting_nvd                         32
% 3.62/0.96  --sub_typing                            true
% 3.62/0.96  --prep_gs_sim                           true
% 3.62/0.96  --prep_unflatten                        true
% 3.62/0.96  --prep_res_sim                          true
% 3.62/0.96  --prep_upred                            true
% 3.62/0.96  --prep_sem_filter                       exhaustive
% 3.62/0.96  --prep_sem_filter_out                   false
% 3.62/0.96  --pred_elim                             true
% 3.62/0.96  --res_sim_input                         true
% 3.62/0.96  --eq_ax_congr_red                       true
% 3.62/0.96  --pure_diseq_elim                       true
% 3.62/0.96  --brand_transform                       false
% 3.62/0.96  --non_eq_to_eq                          false
% 3.62/0.96  --prep_def_merge                        true
% 3.62/0.96  --prep_def_merge_prop_impl              false
% 3.62/0.96  --prep_def_merge_mbd                    true
% 3.62/0.96  --prep_def_merge_tr_red                 false
% 3.62/0.96  --prep_def_merge_tr_cl                  false
% 3.62/0.96  --smt_preprocessing                     true
% 3.62/0.96  --smt_ac_axioms                         fast
% 3.62/0.96  --preprocessed_out                      false
% 3.62/0.96  --preprocessed_stats                    false
% 3.62/0.96  
% 3.62/0.96  ------ Abstraction refinement Options
% 3.62/0.96  
% 3.62/0.96  --abstr_ref                             []
% 3.62/0.96  --abstr_ref_prep                        false
% 3.62/0.96  --abstr_ref_until_sat                   false
% 3.62/0.96  --abstr_ref_sig_restrict                funpre
% 3.62/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.96  --abstr_ref_under                       []
% 3.62/0.96  
% 3.62/0.96  ------ SAT Options
% 3.62/0.96  
% 3.62/0.96  --sat_mode                              false
% 3.62/0.96  --sat_fm_restart_options                ""
% 3.62/0.96  --sat_gr_def                            false
% 3.62/0.96  --sat_epr_types                         true
% 3.62/0.96  --sat_non_cyclic_types                  false
% 3.62/0.96  --sat_finite_models                     false
% 3.62/0.96  --sat_fm_lemmas                         false
% 3.62/0.96  --sat_fm_prep                           false
% 3.62/0.96  --sat_fm_uc_incr                        true
% 3.62/0.96  --sat_out_model                         small
% 3.62/0.96  --sat_out_clauses                       false
% 3.62/0.96  
% 3.62/0.96  ------ QBF Options
% 3.62/0.96  
% 3.62/0.96  --qbf_mode                              false
% 3.62/0.96  --qbf_elim_univ                         false
% 3.62/0.96  --qbf_dom_inst                          none
% 3.62/0.96  --qbf_dom_pre_inst                      false
% 3.62/0.96  --qbf_sk_in                             false
% 3.62/0.96  --qbf_pred_elim                         true
% 3.62/0.96  --qbf_split                             512
% 3.62/0.96  
% 3.62/0.96  ------ BMC1 Options
% 3.62/0.96  
% 3.62/0.96  --bmc1_incremental                      false
% 3.62/0.96  --bmc1_axioms                           reachable_all
% 3.62/0.96  --bmc1_min_bound                        0
% 3.62/0.96  --bmc1_max_bound                        -1
% 3.62/0.96  --bmc1_max_bound_default                -1
% 3.62/0.96  --bmc1_symbol_reachability              true
% 3.62/0.96  --bmc1_property_lemmas                  false
% 3.62/0.96  --bmc1_k_induction                      false
% 3.62/0.96  --bmc1_non_equiv_states                 false
% 3.62/0.96  --bmc1_deadlock                         false
% 3.62/0.96  --bmc1_ucm                              false
% 3.62/0.96  --bmc1_add_unsat_core                   none
% 3.62/0.96  --bmc1_unsat_core_children              false
% 3.62/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.96  --bmc1_out_stat                         full
% 3.62/0.96  --bmc1_ground_init                      false
% 3.62/0.96  --bmc1_pre_inst_next_state              false
% 3.62/0.96  --bmc1_pre_inst_state                   false
% 3.62/0.96  --bmc1_pre_inst_reach_state             false
% 3.62/0.96  --bmc1_out_unsat_core                   false
% 3.62/0.96  --bmc1_aig_witness_out                  false
% 3.62/0.96  --bmc1_verbose                          false
% 3.62/0.96  --bmc1_dump_clauses_tptp                false
% 3.62/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.96  --bmc1_dump_file                        -
% 3.62/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.96  --bmc1_ucm_extend_mode                  1
% 3.62/0.96  --bmc1_ucm_init_mode                    2
% 3.62/0.96  --bmc1_ucm_cone_mode                    none
% 3.62/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.96  --bmc1_ucm_relax_model                  4
% 3.62/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.96  --bmc1_ucm_layered_model                none
% 3.62/0.96  --bmc1_ucm_max_lemma_size               10
% 3.62/0.96  
% 3.62/0.96  ------ AIG Options
% 3.62/0.96  
% 3.62/0.96  --aig_mode                              false
% 3.62/0.96  
% 3.62/0.96  ------ Instantiation Options
% 3.62/0.96  
% 3.62/0.96  --instantiation_flag                    true
% 3.62/0.96  --inst_sos_flag                         false
% 3.62/0.96  --inst_sos_phase                        true
% 3.62/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.96  --inst_lit_sel_side                     none
% 3.62/0.96  --inst_solver_per_active                1400
% 3.62/0.96  --inst_solver_calls_frac                1.
% 3.62/0.96  --inst_passive_queue_type               priority_queues
% 3.62/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.96  --inst_passive_queues_freq              [25;2]
% 3.62/0.96  --inst_dismatching                      true
% 3.62/0.96  --inst_eager_unprocessed_to_passive     true
% 3.62/0.96  --inst_prop_sim_given                   true
% 3.62/0.96  --inst_prop_sim_new                     false
% 3.62/0.96  --inst_subs_new                         false
% 3.62/0.96  --inst_eq_res_simp                      false
% 3.62/0.96  --inst_subs_given                       false
% 3.62/0.96  --inst_orphan_elimination               true
% 3.62/0.96  --inst_learning_loop_flag               true
% 3.62/0.96  --inst_learning_start                   3000
% 3.62/0.96  --inst_learning_factor                  2
% 3.62/0.96  --inst_start_prop_sim_after_learn       3
% 3.62/0.96  --inst_sel_renew                        solver
% 3.62/0.96  --inst_lit_activity_flag                true
% 3.62/0.96  --inst_restr_to_given                   false
% 3.62/0.96  --inst_activity_threshold               500
% 3.62/0.96  --inst_out_proof                        true
% 3.62/0.96  
% 3.62/0.96  ------ Resolution Options
% 3.62/0.96  
% 3.62/0.96  --resolution_flag                       false
% 3.62/0.96  --res_lit_sel                           adaptive
% 3.62/0.96  --res_lit_sel_side                      none
% 3.62/0.96  --res_ordering                          kbo
% 3.62/0.96  --res_to_prop_solver                    active
% 3.62/0.96  --res_prop_simpl_new                    false
% 3.62/0.96  --res_prop_simpl_given                  true
% 3.62/0.96  --res_passive_queue_type                priority_queues
% 3.62/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.96  --res_passive_queues_freq               [15;5]
% 3.62/0.96  --res_forward_subs                      full
% 3.62/0.96  --res_backward_subs                     full
% 3.62/0.96  --res_forward_subs_resolution           true
% 3.62/0.96  --res_backward_subs_resolution          true
% 3.62/0.96  --res_orphan_elimination                true
% 3.62/0.96  --res_time_limit                        2.
% 3.62/0.96  --res_out_proof                         true
% 3.62/0.96  
% 3.62/0.96  ------ Superposition Options
% 3.62/0.96  
% 3.62/0.96  --superposition_flag                    true
% 3.62/0.96  --sup_passive_queue_type                priority_queues
% 3.62/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.96  --demod_completeness_check              fast
% 3.62/0.96  --demod_use_ground                      true
% 3.62/0.96  --sup_to_prop_solver                    passive
% 3.62/0.96  --sup_prop_simpl_new                    true
% 3.62/0.96  --sup_prop_simpl_given                  true
% 3.62/0.96  --sup_fun_splitting                     false
% 3.62/0.96  --sup_smt_interval                      50000
% 3.62/0.96  
% 3.62/0.96  ------ Superposition Simplification Setup
% 3.62/0.96  
% 3.62/0.96  --sup_indices_passive                   []
% 3.62/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.96  --sup_full_bw                           [BwDemod]
% 3.62/0.96  --sup_immed_triv                        [TrivRules]
% 3.62/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.96  --sup_immed_bw_main                     []
% 3.62/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.96  
% 3.62/0.96  ------ Combination Options
% 3.62/0.96  
% 3.62/0.96  --comb_res_mult                         3
% 3.62/0.96  --comb_sup_mult                         2
% 3.62/0.96  --comb_inst_mult                        10
% 3.62/0.96  
% 3.62/0.96  ------ Debug Options
% 3.62/0.96  
% 3.62/0.96  --dbg_backtrace                         false
% 3.62/0.96  --dbg_dump_prop_clauses                 false
% 3.62/0.96  --dbg_dump_prop_clauses_file            -
% 3.62/0.96  --dbg_out_stat                          false
% 3.62/0.96  
% 3.62/0.96  
% 3.62/0.96  
% 3.62/0.96  
% 3.62/0.96  ------ Proving...
% 3.62/0.96  
% 3.62/0.96  
% 3.62/0.96  % SZS status Theorem for theBenchmark.p
% 3.62/0.96  
% 3.62/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.96  
% 3.62/0.96  fof(f20,conjecture,(
% 3.62/0.96    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f21,negated_conjecture,(
% 3.62/0.96    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.62/0.96    inference(negated_conjecture,[],[f20])).
% 3.62/0.96  
% 3.62/0.96  fof(f29,plain,(
% 3.62/0.96    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.62/0.96    inference(ennf_transformation,[],[f21])).
% 3.62/0.96  
% 3.62/0.96  fof(f41,plain,(
% 3.62/0.96    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4))),
% 3.62/0.96    introduced(choice_axiom,[])).
% 3.62/0.96  
% 3.62/0.96  fof(f42,plain,(
% 3.62/0.96    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4)),
% 3.62/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f41])).
% 3.62/0.96  
% 3.62/0.96  fof(f69,plain,(
% 3.62/0.96    r2_hidden(sK3,sK4)),
% 3.62/0.96    inference(cnf_transformation,[],[f42])).
% 3.62/0.96  
% 3.62/0.96  fof(f18,axiom,(
% 3.62/0.96    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f40,plain,(
% 3.62/0.96    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.62/0.96    inference(nnf_transformation,[],[f18])).
% 3.62/0.96  
% 3.62/0.96  fof(f67,plain,(
% 3.62/0.96    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.62/0.96    inference(cnf_transformation,[],[f40])).
% 3.62/0.96  
% 3.62/0.96  fof(f14,axiom,(
% 3.62/0.96    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f62,plain,(
% 3.62/0.96    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.62/0.96    inference(cnf_transformation,[],[f14])).
% 3.62/0.96  
% 3.62/0.96  fof(f15,axiom,(
% 3.62/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f63,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.62/0.96    inference(cnf_transformation,[],[f15])).
% 3.62/0.96  
% 3.62/0.96  fof(f16,axiom,(
% 3.62/0.96    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f64,plain,(
% 3.62/0.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.62/0.96    inference(cnf_transformation,[],[f16])).
% 3.62/0.96  
% 3.62/0.96  fof(f17,axiom,(
% 3.62/0.96    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f65,plain,(
% 3.62/0.96    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.62/0.96    inference(cnf_transformation,[],[f17])).
% 3.62/0.96  
% 3.62/0.96  fof(f71,plain,(
% 3.62/0.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.62/0.96    inference(definition_unfolding,[],[f64,f65])).
% 3.62/0.96  
% 3.62/0.96  fof(f72,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.62/0.96    inference(definition_unfolding,[],[f63,f71])).
% 3.62/0.96  
% 3.62/0.96  fof(f74,plain,(
% 3.62/0.96    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.62/0.96    inference(definition_unfolding,[],[f62,f72])).
% 3.62/0.96  
% 3.62/0.96  fof(f80,plain,(
% 3.62/0.96    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.62/0.96    inference(definition_unfolding,[],[f67,f74])).
% 3.62/0.96  
% 3.62/0.96  fof(f10,axiom,(
% 3.62/0.96    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f28,plain,(
% 3.62/0.96    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.62/0.96    inference(ennf_transformation,[],[f10])).
% 3.62/0.96  
% 3.62/0.96  fof(f58,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.62/0.96    inference(cnf_transformation,[],[f28])).
% 3.62/0.96  
% 3.62/0.96  fof(f2,axiom,(
% 3.62/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f44,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.62/0.96    inference(cnf_transformation,[],[f2])).
% 3.62/0.96  
% 3.62/0.96  fof(f19,axiom,(
% 3.62/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f68,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.62/0.96    inference(cnf_transformation,[],[f19])).
% 3.62/0.96  
% 3.62/0.96  fof(f73,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.62/0.96    inference(definition_unfolding,[],[f68,f72])).
% 3.62/0.96  
% 3.62/0.96  fof(f75,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 3.62/0.96    inference(definition_unfolding,[],[f44,f73,f73])).
% 3.62/0.96  
% 3.62/0.96  fof(f11,axiom,(
% 3.62/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f59,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.62/0.96    inference(cnf_transformation,[],[f11])).
% 3.62/0.96  
% 3.62/0.96  fof(f8,axiom,(
% 3.62/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f56,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.62/0.96    inference(cnf_transformation,[],[f8])).
% 3.62/0.96  
% 3.62/0.96  fof(f77,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.62/0.96    inference(definition_unfolding,[],[f59,f73,f73,f56])).
% 3.62/0.96  
% 3.62/0.96  fof(f12,axiom,(
% 3.62/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f60,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.62/0.96    inference(cnf_transformation,[],[f12])).
% 3.62/0.96  
% 3.62/0.96  fof(f78,plain,(
% 3.62/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 3.62/0.96    inference(definition_unfolding,[],[f60,f56,f56,f73])).
% 3.62/0.96  
% 3.62/0.96  fof(f9,axiom,(
% 3.62/0.96    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f57,plain,(
% 3.62/0.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.62/0.96    inference(cnf_transformation,[],[f9])).
% 3.62/0.96  
% 3.62/0.96  fof(f76,plain,(
% 3.62/0.96    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.62/0.96    inference(definition_unfolding,[],[f57,f73])).
% 3.62/0.96  
% 3.62/0.96  fof(f13,axiom,(
% 3.62/0.96    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f61,plain,(
% 3.62/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.62/0.96    inference(cnf_transformation,[],[f13])).
% 3.62/0.96  
% 3.62/0.96  fof(f79,plain,(
% 3.62/0.96    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.62/0.96    inference(definition_unfolding,[],[f61,f73])).
% 3.62/0.96  
% 3.62/0.96  fof(f7,axiom,(
% 3.62/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.62/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.96  
% 3.62/0.96  fof(f38,plain,(
% 3.62/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.96    inference(nnf_transformation,[],[f7])).
% 3.62/0.96  
% 3.62/0.96  fof(f39,plain,(
% 3.62/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.96    inference(flattening,[],[f38])).
% 3.62/0.96  
% 3.62/0.96  fof(f53,plain,(
% 3.62/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.62/0.96    inference(cnf_transformation,[],[f39])).
% 3.62/0.96  
% 3.62/0.96  fof(f84,plain,(
% 3.62/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.62/0.96    inference(equality_resolution,[],[f53])).
% 3.62/0.96  
% 3.62/0.96  fof(f70,plain,(
% 3.62/0.96    k2_xboole_0(k1_tarski(sK3),sK4) != sK4),
% 3.62/0.96    inference(cnf_transformation,[],[f42])).
% 3.62/0.96  
% 3.62/0.96  fof(f82,plain,(
% 3.62/0.96    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4),
% 3.62/0.96    inference(definition_unfolding,[],[f70,f73,f74])).
% 3.62/0.96  
% 3.62/0.96  cnf(c_21,negated_conjecture,
% 3.62/0.96      ( r2_hidden(sK3,sK4) ),
% 3.62/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_934,plain,
% 3.62/0.96      ( r2_hidden(sK3,sK4) = iProver_top ),
% 3.62/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_18,plain,
% 3.62/0.96      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.62/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_936,plain,
% 3.62/0.96      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
% 3.62/0.96      | r2_hidden(X0,X1) != iProver_top ),
% 3.62/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_14,plain,
% 3.62/0.96      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.62/0.96      inference(cnf_transformation,[],[f58]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_938,plain,
% 3.62/0.96      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.62/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_2252,plain,
% 3.62/0.96      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.62/0.96      | r2_hidden(X0,X1) != iProver_top ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_936,c_938]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_12122,plain,
% 3.62/0.96      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_934,c_2252]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1,plain,
% 3.62/0.96      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 3.62/0.96      inference(cnf_transformation,[],[f75]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_15,plain,
% 3.62/0.96      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.62/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_16,plain,
% 3.62/0.96      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.62/0.96      inference(cnf_transformation,[],[f78]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1484,plain,
% 3.62/0.96      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_15,c_16]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_8920,plain,
% 3.62/0.96      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_1,c_1484]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_13121,plain,
% 3.62/0.96      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)))) ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_12122,c_8920]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_13179,plain,
% 3.62/0.96      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
% 3.62/0.96      inference(light_normalisation,[status(thm)],[c_13121,c_12122]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_13,plain,
% 3.62/0.96      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.62/0.96      inference(cnf_transformation,[],[f76]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1388,plain,
% 3.62/0.96      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_1,c_13]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1618,plain,
% 3.62/0.96      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_1388,c_15]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1619,plain,
% 3.62/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.62/0.96      inference(light_normalisation,[status(thm)],[c_1618,c_1388]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1613,plain,
% 3.62/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_1388,c_16]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_17,plain,
% 3.62/0.96      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 3.62/0.96      inference(cnf_transformation,[],[f79]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_937,plain,
% 3.62/0.96      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 3.62/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1130,plain,
% 3.62/0.96      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_937,c_938]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1616,plain,
% 3.62/0.96      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_1388,c_1130]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1626,plain,
% 3.62/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.62/0.96      inference(light_normalisation,[status(thm)],[c_1613,c_1616]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_12,plain,
% 3.62/0.96      ( r1_tarski(X0,X0) ),
% 3.62/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_939,plain,
% 3.62/0.96      ( r1_tarski(X0,X0) = iProver_top ),
% 3.62/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1129,plain,
% 3.62/0.96      ( k3_xboole_0(X0,X0) = X0 ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_939,c_938]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1628,plain,
% 3.62/0.96      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.62/0.96      inference(light_normalisation,[status(thm)],[c_1626,c_1129]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1837,plain,
% 3.62/0.96      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.62/0.96      inference(superposition,[status(thm)],[c_1129,c_1619]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_1960,plain,
% 3.62/0.96      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.62/0.96      inference(light_normalisation,[status(thm)],[c_1628,c_1837]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_13181,plain,
% 3.62/0.96      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) = sK4 ),
% 3.62/0.96      inference(demodulation,[status(thm)],[c_13179,c_1619,c_1960]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(c_20,negated_conjecture,
% 3.62/0.96      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
% 3.62/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.62/0.96  
% 3.62/0.96  cnf(contradiction,plain,
% 3.62/0.96      ( $false ),
% 3.62/0.96      inference(minisat,[status(thm)],[c_13181,c_20]) ).
% 3.62/0.96  
% 3.62/0.96  
% 3.62/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.96  
% 3.62/0.96  ------                               Statistics
% 3.62/0.96  
% 3.62/0.96  ------ General
% 3.62/0.96  
% 3.62/0.96  abstr_ref_over_cycles:                  0
% 3.62/0.96  abstr_ref_under_cycles:                 0
% 3.62/0.96  gc_basic_clause_elim:                   0
% 3.62/0.96  forced_gc_time:                         0
% 3.62/0.96  parsing_time:                           0.009
% 3.62/0.96  unif_index_cands_time:                  0.
% 3.62/0.96  unif_index_add_time:                    0.
% 3.62/0.96  orderings_time:                         0.
% 3.62/0.96  out_proof_time:                         0.008
% 3.62/0.96  total_time:                             0.403
% 3.62/0.96  num_of_symbols:                         44
% 3.62/0.96  num_of_terms:                           14537
% 3.62/0.96  
% 3.62/0.96  ------ Preprocessing
% 3.62/0.96  
% 3.62/0.96  num_of_splits:                          0
% 3.62/0.96  num_of_split_atoms:                     0
% 3.62/0.96  num_of_reused_defs:                     0
% 3.62/0.96  num_eq_ax_congr_red:                    27
% 3.62/0.96  num_of_sem_filtered_clauses:            1
% 3.62/0.96  num_of_subtypes:                        0
% 3.62/0.96  monotx_restored_types:                  0
% 3.62/0.96  sat_num_of_epr_types:                   0
% 3.62/0.96  sat_num_of_non_cyclic_types:            0
% 3.62/0.96  sat_guarded_non_collapsed_types:        0
% 3.62/0.96  num_pure_diseq_elim:                    0
% 3.62/0.96  simp_replaced_by:                       0
% 3.62/0.96  res_preprocessed:                       101
% 3.62/0.96  prep_upred:                             0
% 3.62/0.96  prep_unflattend:                        0
% 3.62/0.96  smt_new_axioms:                         0
% 3.62/0.96  pred_elim_cands:                        3
% 3.62/0.96  pred_elim:                              0
% 3.62/0.96  pred_elim_cl:                           0
% 3.62/0.96  pred_elim_cycles:                       2
% 3.62/0.97  merged_defs:                            8
% 3.62/0.97  merged_defs_ncl:                        0
% 3.62/0.97  bin_hyper_res:                          8
% 3.62/0.97  prep_cycles:                            4
% 3.62/0.97  pred_elim_time:                         0.002
% 3.62/0.97  splitting_time:                         0.
% 3.62/0.97  sem_filter_time:                        0.
% 3.62/0.97  monotx_time:                            0.
% 3.62/0.97  subtype_inf_time:                       0.
% 3.62/0.97  
% 3.62/0.97  ------ Problem properties
% 3.62/0.97  
% 3.62/0.97  clauses:                                21
% 3.62/0.97  conjectures:                            2
% 3.62/0.97  epr:                                    6
% 3.62/0.97  horn:                                   17
% 3.62/0.97  ground:                                 2
% 3.62/0.97  unary:                                  8
% 3.62/0.97  binary:                                 10
% 3.62/0.97  lits:                                   37
% 3.62/0.97  lits_eq:                                7
% 3.62/0.97  fd_pure:                                0
% 3.62/0.97  fd_pseudo:                              0
% 3.62/0.97  fd_cond:                                0
% 3.62/0.97  fd_pseudo_cond:                         1
% 3.62/0.97  ac_symbols:                             0
% 3.62/0.97  
% 3.62/0.97  ------ Propositional Solver
% 3.62/0.97  
% 3.62/0.97  prop_solver_calls:                      29
% 3.62/0.97  prop_fast_solver_calls:                 612
% 3.62/0.97  smt_solver_calls:                       0
% 3.62/0.97  smt_fast_solver_calls:                  0
% 3.62/0.97  prop_num_of_clauses:                    5092
% 3.62/0.97  prop_preprocess_simplified:             11514
% 3.62/0.97  prop_fo_subsumed:                       0
% 3.62/0.97  prop_solver_time:                       0.
% 3.62/0.97  smt_solver_time:                        0.
% 3.62/0.97  smt_fast_solver_time:                   0.
% 3.62/0.97  prop_fast_solver_time:                  0.
% 3.62/0.97  prop_unsat_core_time:                   0.001
% 3.62/0.97  
% 3.62/0.97  ------ QBF
% 3.62/0.97  
% 3.62/0.97  qbf_q_res:                              0
% 3.62/0.97  qbf_num_tautologies:                    0
% 3.62/0.97  qbf_prep_cycles:                        0
% 3.62/0.97  
% 3.62/0.97  ------ BMC1
% 3.62/0.97  
% 3.62/0.97  bmc1_current_bound:                     -1
% 3.62/0.97  bmc1_last_solved_bound:                 -1
% 3.62/0.97  bmc1_unsat_core_size:                   -1
% 3.62/0.97  bmc1_unsat_core_parents_size:           -1
% 3.62/0.97  bmc1_merge_next_fun:                    0
% 3.62/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.62/0.97  
% 3.62/0.97  ------ Instantiation
% 3.62/0.97  
% 3.62/0.97  inst_num_of_clauses:                    1394
% 3.62/0.97  inst_num_in_passive:                    551
% 3.62/0.97  inst_num_in_active:                     532
% 3.62/0.97  inst_num_in_unprocessed:                314
% 3.62/0.97  inst_num_of_loops:                      570
% 3.62/0.97  inst_num_of_learning_restarts:          0
% 3.62/0.97  inst_num_moves_active_passive:          35
% 3.62/0.97  inst_lit_activity:                      0
% 3.62/0.97  inst_lit_activity_moves:                0
% 3.62/0.97  inst_num_tautologies:                   0
% 3.62/0.97  inst_num_prop_implied:                  0
% 3.62/0.97  inst_num_existing_simplified:           0
% 3.62/0.97  inst_num_eq_res_simplified:             0
% 3.62/0.97  inst_num_child_elim:                    0
% 3.62/0.97  inst_num_of_dismatching_blockings:      906
% 3.62/0.97  inst_num_of_non_proper_insts:           1366
% 3.62/0.97  inst_num_of_duplicates:                 0
% 3.62/0.97  inst_inst_num_from_inst_to_res:         0
% 3.62/0.97  inst_dismatching_checking_time:         0.
% 3.62/0.97  
% 3.62/0.97  ------ Resolution
% 3.62/0.97  
% 3.62/0.97  res_num_of_clauses:                     0
% 3.62/0.97  res_num_in_passive:                     0
% 3.62/0.97  res_num_in_active:                      0
% 3.62/0.97  res_num_of_loops:                       105
% 3.62/0.97  res_forward_subset_subsumed:            111
% 3.62/0.97  res_backward_subset_subsumed:           8
% 3.62/0.97  res_forward_subsumed:                   0
% 3.62/0.97  res_backward_subsumed:                  0
% 3.62/0.97  res_forward_subsumption_resolution:     0
% 3.62/0.97  res_backward_subsumption_resolution:    0
% 3.62/0.97  res_clause_to_clause_subsumption:       2576
% 3.62/0.97  res_orphan_elimination:                 0
% 3.62/0.97  res_tautology_del:                      70
% 3.62/0.97  res_num_eq_res_simplified:              0
% 3.62/0.97  res_num_sel_changes:                    0
% 3.62/0.97  res_moves_from_active_to_pass:          0
% 3.62/0.97  
% 3.62/0.97  ------ Superposition
% 3.62/0.97  
% 3.62/0.97  sup_time_total:                         0.
% 3.62/0.97  sup_time_generating:                    0.
% 3.62/0.97  sup_time_sim_full:                      0.
% 3.62/0.97  sup_time_sim_immed:                     0.
% 3.62/0.97  
% 3.62/0.97  sup_num_of_clauses:                     306
% 3.62/0.97  sup_num_in_active:                      112
% 3.62/0.97  sup_num_in_passive:                     194
% 3.62/0.97  sup_num_of_loops:                       112
% 3.62/0.97  sup_fw_superposition:                   816
% 3.62/0.97  sup_bw_superposition:                   405
% 3.62/0.97  sup_immediate_simplified:               406
% 3.62/0.97  sup_given_eliminated:                   0
% 3.62/0.97  comparisons_done:                       0
% 3.62/0.97  comparisons_avoided:                    0
% 3.62/0.97  
% 3.62/0.97  ------ Simplifications
% 3.62/0.97  
% 3.62/0.97  
% 3.62/0.97  sim_fw_subset_subsumed:                 5
% 3.62/0.97  sim_bw_subset_subsumed:                 0
% 3.62/0.97  sim_fw_subsumed:                        100
% 3.62/0.97  sim_bw_subsumed:                        0
% 3.62/0.97  sim_fw_subsumption_res:                 0
% 3.62/0.97  sim_bw_subsumption_res:                 0
% 3.62/0.97  sim_tautology_del:                      12
% 3.62/0.97  sim_eq_tautology_del:                   58
% 3.62/0.97  sim_eq_res_simp:                        0
% 3.62/0.97  sim_fw_demodulated:                     160
% 3.62/0.97  sim_bw_demodulated:                     2
% 3.62/0.97  sim_light_normalised:                   262
% 3.62/0.97  sim_joinable_taut:                      0
% 3.62/0.97  sim_joinable_simp:                      0
% 3.62/0.97  sim_ac_normalised:                      0
% 3.62/0.97  sim_smt_subsumption:                    0
% 3.62/0.97  
%------------------------------------------------------------------------------
