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
% DateTime   : Thu Dec  3 11:38:28 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 448 expanded)
%              Number of clauses        :   58 ( 116 expanded)
%              Number of leaves         :   17 ( 123 expanded)
%              Depth                    :   20
%              Number of atoms          :  158 ( 856 expanded)
%              Number of equality atoms :  118 ( 568 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
      & r2_hidden(sK4,sK1)
      & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
    & r2_hidden(sK4,sK1)
    & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f38])).

fof(f69,plain,(
    r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f52,f52])).

fof(f68,plain,(
    k3_xboole_0(sK2,sK3) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k2_tarski(sK4,sK4) ),
    inference(definition_unfolding,[],[f68,f52,f62])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f67,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f53,f52,f52])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f54,f52,f52,f52])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k2_tarski(sK4,sK4) ),
    inference(definition_unfolding,[],[f70,f52,f62])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_428,plain,
    ( r2_hidden(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k2_tarski(X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_432,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7048,plain,
    ( k2_xboole_0(k2_tarski(sK4,sK4),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_428,c_432])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8085,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_7048,c_8])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_9170,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_8085,c_0])).

cnf(c_27,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k2_tarski(sK4,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_228,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_28])).

cnf(c_229,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_12,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2581,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_229,c_12])).

cnf(c_7004,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_27,c_2581])).

cnf(c_9182,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_9170,c_7004])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7019,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2581,c_11])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_217,plain,
    ( X0 != X1
    | k2_xboole_0(X2,X1) = X1
    | k4_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_218,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_932,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_218,c_8])).

cnf(c_5732,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_932,c_12])).

cnf(c_13,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2733,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_27,c_13])).

cnf(c_2580,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) = k4_xboole_0(k2_tarski(sK4,sK4),X0) ),
    inference(superposition,[status(thm)],[c_27,c_12])).

cnf(c_3263,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(k2_tarski(sK4,sK4),X0) ),
    inference(light_normalisation,[status(thm)],[c_2733,c_2580])).

cnf(c_16787,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(X0,sK2)) = k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_5732,c_3263])).

cnf(c_632,plain,
    ( k2_xboole_0(k2_tarski(sK4,sK4),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_27,c_218])).

cnf(c_1252,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),sK2) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_632,c_8])).

cnf(c_4623,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_tarski(sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_1252,c_0])).

cnf(c_2305,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK4,sK4)) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_27,c_11])).

cnf(c_4632,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,sK2)) = k2_tarski(sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_4623,c_27,c_2305])).

cnf(c_16790,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(X0,sK2)) = k2_tarski(sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_16787,c_4632])).

cnf(c_17839,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k2_tarski(sK4,sK4))) = k4_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_16790,c_0])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_205,plain,
    ( X0 != X1
    | k2_xboole_0(X2,k4_xboole_0(X1,X2)) = X1
    | k4_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_6])).

cnf(c_206,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_767,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k2_tarski(sK4,sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_27,c_206])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1204,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK3),X0)) = k4_xboole_0(k2_tarski(sK4,sK4),X0) ),
    inference(superposition,[status(thm)],[c_27,c_9])).

cnf(c_1766,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK4,sK4)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_767,c_1204])).

cnf(c_17855,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k2_tarski(sK4,sK4))) = k4_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_17839,c_1766])).

cnf(c_17856,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK2,k2_tarski(sK4,sK4))))) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_17855,c_9])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4624,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,k2_tarski(sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_1252,c_7])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4629,plain,
    ( k2_xboole_0(sK2,k2_tarski(sK4,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4624,c_1,c_7])).

cnf(c_17857,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(X0,sK2))) = k4_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_17856,c_4629])).

cnf(c_5731,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_932,c_9])).

cnf(c_17858,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_17857,c_7,c_5731])).

cnf(c_18447,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(X0,X0)) = k2_tarski(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_17858,c_4632])).

cnf(c_28858,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_tarski(sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_9182,c_7019,c_18447])).

cnf(c_25,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k2_tarski(sK4,sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28860,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28858,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:37:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.48/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/1.52  
% 7.48/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.48/1.52  
% 7.48/1.52  ------  iProver source info
% 7.48/1.52  
% 7.48/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.48/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.48/1.52  git: non_committed_changes: false
% 7.48/1.52  git: last_make_outside_of_git: false
% 7.48/1.52  
% 7.48/1.52  ------ 
% 7.48/1.52  
% 7.48/1.52  ------ Input Options
% 7.48/1.52  
% 7.48/1.52  --out_options                           all
% 7.48/1.52  --tptp_safe_out                         true
% 7.48/1.52  --problem_path                          ""
% 7.48/1.52  --include_path                          ""
% 7.48/1.52  --clausifier                            res/vclausify_rel
% 7.48/1.52  --clausifier_options                    --mode clausify
% 7.48/1.52  --stdin                                 false
% 7.48/1.52  --stats_out                             all
% 7.48/1.52  
% 7.48/1.52  ------ General Options
% 7.48/1.52  
% 7.48/1.52  --fof                                   false
% 7.48/1.52  --time_out_real                         305.
% 7.48/1.52  --time_out_virtual                      -1.
% 7.48/1.52  --symbol_type_check                     false
% 7.48/1.52  --clausify_out                          false
% 7.48/1.52  --sig_cnt_out                           false
% 7.48/1.52  --trig_cnt_out                          false
% 7.48/1.52  --trig_cnt_out_tolerance                1.
% 7.48/1.52  --trig_cnt_out_sk_spl                   false
% 7.48/1.52  --abstr_cl_out                          false
% 7.48/1.52  
% 7.48/1.52  ------ Global Options
% 7.48/1.52  
% 7.48/1.52  --schedule                              default
% 7.48/1.52  --add_important_lit                     false
% 7.48/1.52  --prop_solver_per_cl                    1000
% 7.48/1.52  --min_unsat_core                        false
% 7.48/1.52  --soft_assumptions                      false
% 7.48/1.52  --soft_lemma_size                       3
% 7.48/1.52  --prop_impl_unit_size                   0
% 7.48/1.52  --prop_impl_unit                        []
% 7.48/1.52  --share_sel_clauses                     true
% 7.48/1.52  --reset_solvers                         false
% 7.48/1.52  --bc_imp_inh                            [conj_cone]
% 7.48/1.52  --conj_cone_tolerance                   3.
% 7.48/1.52  --extra_neg_conj                        none
% 7.48/1.52  --large_theory_mode                     true
% 7.48/1.52  --prolific_symb_bound                   200
% 7.48/1.52  --lt_threshold                          2000
% 7.48/1.52  --clause_weak_htbl                      true
% 7.48/1.52  --gc_record_bc_elim                     false
% 7.48/1.52  
% 7.48/1.52  ------ Preprocessing Options
% 7.48/1.52  
% 7.48/1.52  --preprocessing_flag                    true
% 7.48/1.52  --time_out_prep_mult                    0.1
% 7.48/1.52  --splitting_mode                        input
% 7.48/1.52  --splitting_grd                         true
% 7.48/1.52  --splitting_cvd                         false
% 7.48/1.52  --splitting_cvd_svl                     false
% 7.48/1.52  --splitting_nvd                         32
% 7.48/1.52  --sub_typing                            true
% 7.48/1.52  --prep_gs_sim                           true
% 7.48/1.52  --prep_unflatten                        true
% 7.48/1.52  --prep_res_sim                          true
% 7.48/1.52  --prep_upred                            true
% 7.48/1.52  --prep_sem_filter                       exhaustive
% 7.48/1.52  --prep_sem_filter_out                   false
% 7.48/1.52  --pred_elim                             true
% 7.48/1.52  --res_sim_input                         true
% 7.48/1.52  --eq_ax_congr_red                       true
% 7.48/1.52  --pure_diseq_elim                       true
% 7.48/1.52  --brand_transform                       false
% 7.48/1.52  --non_eq_to_eq                          false
% 7.48/1.52  --prep_def_merge                        true
% 7.48/1.52  --prep_def_merge_prop_impl              false
% 7.48/1.52  --prep_def_merge_mbd                    true
% 7.48/1.52  --prep_def_merge_tr_red                 false
% 7.48/1.52  --prep_def_merge_tr_cl                  false
% 7.48/1.52  --smt_preprocessing                     true
% 7.48/1.52  --smt_ac_axioms                         fast
% 7.48/1.52  --preprocessed_out                      false
% 7.48/1.52  --preprocessed_stats                    false
% 7.48/1.52  
% 7.48/1.52  ------ Abstraction refinement Options
% 7.48/1.52  
% 7.48/1.52  --abstr_ref                             []
% 7.48/1.52  --abstr_ref_prep                        false
% 7.48/1.52  --abstr_ref_until_sat                   false
% 7.48/1.52  --abstr_ref_sig_restrict                funpre
% 7.48/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.48/1.52  --abstr_ref_under                       []
% 7.48/1.52  
% 7.48/1.52  ------ SAT Options
% 7.48/1.52  
% 7.48/1.52  --sat_mode                              false
% 7.48/1.52  --sat_fm_restart_options                ""
% 7.48/1.52  --sat_gr_def                            false
% 7.48/1.52  --sat_epr_types                         true
% 7.48/1.52  --sat_non_cyclic_types                  false
% 7.48/1.52  --sat_finite_models                     false
% 7.48/1.52  --sat_fm_lemmas                         false
% 7.48/1.52  --sat_fm_prep                           false
% 7.48/1.52  --sat_fm_uc_incr                        true
% 7.48/1.52  --sat_out_model                         small
% 7.48/1.52  --sat_out_clauses                       false
% 7.48/1.52  
% 7.48/1.52  ------ QBF Options
% 7.48/1.52  
% 7.48/1.52  --qbf_mode                              false
% 7.48/1.52  --qbf_elim_univ                         false
% 7.48/1.52  --qbf_dom_inst                          none
% 7.48/1.52  --qbf_dom_pre_inst                      false
% 7.48/1.52  --qbf_sk_in                             false
% 7.48/1.52  --qbf_pred_elim                         true
% 7.48/1.52  --qbf_split                             512
% 7.48/1.52  
% 7.48/1.52  ------ BMC1 Options
% 7.48/1.52  
% 7.48/1.52  --bmc1_incremental                      false
% 7.48/1.52  --bmc1_axioms                           reachable_all
% 7.48/1.52  --bmc1_min_bound                        0
% 7.48/1.52  --bmc1_max_bound                        -1
% 7.48/1.52  --bmc1_max_bound_default                -1
% 7.48/1.52  --bmc1_symbol_reachability              true
% 7.48/1.52  --bmc1_property_lemmas                  false
% 7.48/1.52  --bmc1_k_induction                      false
% 7.48/1.52  --bmc1_non_equiv_states                 false
% 7.48/1.52  --bmc1_deadlock                         false
% 7.48/1.52  --bmc1_ucm                              false
% 7.48/1.52  --bmc1_add_unsat_core                   none
% 7.48/1.52  --bmc1_unsat_core_children              false
% 7.48/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.48/1.52  --bmc1_out_stat                         full
% 7.48/1.52  --bmc1_ground_init                      false
% 7.48/1.52  --bmc1_pre_inst_next_state              false
% 7.48/1.52  --bmc1_pre_inst_state                   false
% 7.48/1.52  --bmc1_pre_inst_reach_state             false
% 7.48/1.52  --bmc1_out_unsat_core                   false
% 7.48/1.52  --bmc1_aig_witness_out                  false
% 7.48/1.52  --bmc1_verbose                          false
% 7.48/1.52  --bmc1_dump_clauses_tptp                false
% 7.48/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.48/1.52  --bmc1_dump_file                        -
% 7.48/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.48/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.48/1.52  --bmc1_ucm_extend_mode                  1
% 7.48/1.52  --bmc1_ucm_init_mode                    2
% 7.48/1.52  --bmc1_ucm_cone_mode                    none
% 7.48/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.48/1.52  --bmc1_ucm_relax_model                  4
% 7.48/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.48/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.48/1.52  --bmc1_ucm_layered_model                none
% 7.48/1.52  --bmc1_ucm_max_lemma_size               10
% 7.48/1.52  
% 7.48/1.52  ------ AIG Options
% 7.48/1.52  
% 7.48/1.52  --aig_mode                              false
% 7.48/1.52  
% 7.48/1.52  ------ Instantiation Options
% 7.48/1.52  
% 7.48/1.52  --instantiation_flag                    true
% 7.48/1.52  --inst_sos_flag                         false
% 7.48/1.52  --inst_sos_phase                        true
% 7.48/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.48/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.48/1.52  --inst_lit_sel_side                     num_symb
% 7.48/1.52  --inst_solver_per_active                1400
% 7.48/1.52  --inst_solver_calls_frac                1.
% 7.48/1.52  --inst_passive_queue_type               priority_queues
% 7.48/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.48/1.52  --inst_passive_queues_freq              [25;2]
% 7.48/1.52  --inst_dismatching                      true
% 7.48/1.52  --inst_eager_unprocessed_to_passive     true
% 7.48/1.52  --inst_prop_sim_given                   true
% 7.48/1.52  --inst_prop_sim_new                     false
% 7.48/1.52  --inst_subs_new                         false
% 7.48/1.52  --inst_eq_res_simp                      false
% 7.48/1.52  --inst_subs_given                       false
% 7.48/1.52  --inst_orphan_elimination               true
% 7.48/1.52  --inst_learning_loop_flag               true
% 7.48/1.52  --inst_learning_start                   3000
% 7.48/1.52  --inst_learning_factor                  2
% 7.48/1.52  --inst_start_prop_sim_after_learn       3
% 7.48/1.52  --inst_sel_renew                        solver
% 7.48/1.52  --inst_lit_activity_flag                true
% 7.48/1.52  --inst_restr_to_given                   false
% 7.48/1.52  --inst_activity_threshold               500
% 7.48/1.52  --inst_out_proof                        true
% 7.48/1.52  
% 7.48/1.52  ------ Resolution Options
% 7.48/1.52  
% 7.48/1.52  --resolution_flag                       true
% 7.48/1.52  --res_lit_sel                           adaptive
% 7.48/1.52  --res_lit_sel_side                      none
% 7.48/1.52  --res_ordering                          kbo
% 7.48/1.52  --res_to_prop_solver                    active
% 7.48/1.52  --res_prop_simpl_new                    false
% 7.48/1.52  --res_prop_simpl_given                  true
% 7.48/1.52  --res_passive_queue_type                priority_queues
% 7.48/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.48/1.52  --res_passive_queues_freq               [15;5]
% 7.48/1.52  --res_forward_subs                      full
% 7.48/1.52  --res_backward_subs                     full
% 7.48/1.52  --res_forward_subs_resolution           true
% 7.48/1.52  --res_backward_subs_resolution          true
% 7.48/1.52  --res_orphan_elimination                true
% 7.48/1.52  --res_time_limit                        2.
% 7.48/1.52  --res_out_proof                         true
% 7.48/1.52  
% 7.48/1.52  ------ Superposition Options
% 7.48/1.52  
% 7.48/1.52  --superposition_flag                    true
% 7.48/1.52  --sup_passive_queue_type                priority_queues
% 7.48/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.48/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.48/1.52  --demod_completeness_check              fast
% 7.48/1.52  --demod_use_ground                      true
% 7.48/1.52  --sup_to_prop_solver                    passive
% 7.48/1.52  --sup_prop_simpl_new                    true
% 7.48/1.52  --sup_prop_simpl_given                  true
% 7.48/1.52  --sup_fun_splitting                     false
% 7.48/1.52  --sup_smt_interval                      50000
% 7.48/1.52  
% 7.48/1.52  ------ Superposition Simplification Setup
% 7.48/1.52  
% 7.48/1.52  --sup_indices_passive                   []
% 7.48/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.48/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.52  --sup_full_bw                           [BwDemod]
% 7.48/1.52  --sup_immed_triv                        [TrivRules]
% 7.48/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.48/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.52  --sup_immed_bw_main                     []
% 7.48/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.48/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.52  
% 7.48/1.52  ------ Combination Options
% 7.48/1.52  
% 7.48/1.52  --comb_res_mult                         3
% 7.48/1.52  --comb_sup_mult                         2
% 7.48/1.52  --comb_inst_mult                        10
% 7.48/1.52  
% 7.48/1.52  ------ Debug Options
% 7.48/1.52  
% 7.48/1.52  --dbg_backtrace                         false
% 7.48/1.52  --dbg_dump_prop_clauses                 false
% 7.48/1.52  --dbg_dump_prop_clauses_file            -
% 7.48/1.52  --dbg_out_stat                          false
% 7.48/1.52  ------ Parsing...
% 7.48/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.48/1.52  
% 7.48/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 7.48/1.52  
% 7.48/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.48/1.52  
% 7.48/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.48/1.52  ------ Proving...
% 7.48/1.52  ------ Problem Properties 
% 7.48/1.52  
% 7.48/1.52  
% 7.48/1.52  clauses                                 30
% 7.48/1.52  conjectures                             3
% 7.48/1.52  EPR                                     1
% 7.48/1.52  Horn                                    27
% 7.48/1.52  unary                                   22
% 7.48/1.52  binary                                  3
% 7.48/1.52  lits                                    44
% 7.48/1.52  lits eq                                 31
% 7.48/1.52  fd_pure                                 0
% 7.48/1.52  fd_pseudo                               0
% 7.48/1.52  fd_cond                                 0
% 7.48/1.52  fd_pseudo_cond                          5
% 7.48/1.52  AC symbols                              0
% 7.48/1.52  
% 7.48/1.52  ------ Schedule dynamic 5 is on 
% 7.48/1.52  
% 7.48/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.48/1.52  
% 7.48/1.52  
% 7.48/1.52  ------ 
% 7.48/1.52  Current options:
% 7.48/1.52  ------ 
% 7.48/1.52  
% 7.48/1.52  ------ Input Options
% 7.48/1.52  
% 7.48/1.52  --out_options                           all
% 7.48/1.52  --tptp_safe_out                         true
% 7.48/1.52  --problem_path                          ""
% 7.48/1.52  --include_path                          ""
% 7.48/1.52  --clausifier                            res/vclausify_rel
% 7.48/1.52  --clausifier_options                    --mode clausify
% 7.48/1.52  --stdin                                 false
% 7.48/1.52  --stats_out                             all
% 7.48/1.52  
% 7.48/1.52  ------ General Options
% 7.48/1.52  
% 7.48/1.52  --fof                                   false
% 7.48/1.52  --time_out_real                         305.
% 7.48/1.52  --time_out_virtual                      -1.
% 7.48/1.52  --symbol_type_check                     false
% 7.48/1.52  --clausify_out                          false
% 7.48/1.52  --sig_cnt_out                           false
% 7.48/1.52  --trig_cnt_out                          false
% 7.48/1.52  --trig_cnt_out_tolerance                1.
% 7.48/1.52  --trig_cnt_out_sk_spl                   false
% 7.48/1.52  --abstr_cl_out                          false
% 7.48/1.52  
% 7.48/1.52  ------ Global Options
% 7.48/1.52  
% 7.48/1.52  --schedule                              default
% 7.48/1.52  --add_important_lit                     false
% 7.48/1.52  --prop_solver_per_cl                    1000
% 7.48/1.52  --min_unsat_core                        false
% 7.48/1.52  --soft_assumptions                      false
% 7.48/1.52  --soft_lemma_size                       3
% 7.48/1.52  --prop_impl_unit_size                   0
% 7.48/1.52  --prop_impl_unit                        []
% 7.48/1.52  --share_sel_clauses                     true
% 7.48/1.52  --reset_solvers                         false
% 7.48/1.52  --bc_imp_inh                            [conj_cone]
% 7.48/1.52  --conj_cone_tolerance                   3.
% 7.48/1.52  --extra_neg_conj                        none
% 7.48/1.52  --large_theory_mode                     true
% 7.48/1.52  --prolific_symb_bound                   200
% 7.48/1.52  --lt_threshold                          2000
% 7.48/1.52  --clause_weak_htbl                      true
% 7.48/1.52  --gc_record_bc_elim                     false
% 7.48/1.52  
% 7.48/1.52  ------ Preprocessing Options
% 7.48/1.52  
% 7.48/1.52  --preprocessing_flag                    true
% 7.48/1.52  --time_out_prep_mult                    0.1
% 7.48/1.52  --splitting_mode                        input
% 7.48/1.52  --splitting_grd                         true
% 7.48/1.52  --splitting_cvd                         false
% 7.48/1.52  --splitting_cvd_svl                     false
% 7.48/1.52  --splitting_nvd                         32
% 7.48/1.52  --sub_typing                            true
% 7.48/1.52  --prep_gs_sim                           true
% 7.48/1.52  --prep_unflatten                        true
% 7.48/1.52  --prep_res_sim                          true
% 7.48/1.52  --prep_upred                            true
% 7.48/1.52  --prep_sem_filter                       exhaustive
% 7.48/1.52  --prep_sem_filter_out                   false
% 7.48/1.52  --pred_elim                             true
% 7.48/1.52  --res_sim_input                         true
% 7.48/1.52  --eq_ax_congr_red                       true
% 7.48/1.52  --pure_diseq_elim                       true
% 7.48/1.52  --brand_transform                       false
% 7.48/1.52  --non_eq_to_eq                          false
% 7.48/1.52  --prep_def_merge                        true
% 7.48/1.52  --prep_def_merge_prop_impl              false
% 7.48/1.52  --prep_def_merge_mbd                    true
% 7.48/1.52  --prep_def_merge_tr_red                 false
% 7.48/1.52  --prep_def_merge_tr_cl                  false
% 7.48/1.52  --smt_preprocessing                     true
% 7.48/1.52  --smt_ac_axioms                         fast
% 7.48/1.52  --preprocessed_out                      false
% 7.48/1.52  --preprocessed_stats                    false
% 7.48/1.52  
% 7.48/1.52  ------ Abstraction refinement Options
% 7.48/1.52  
% 7.48/1.52  --abstr_ref                             []
% 7.48/1.52  --abstr_ref_prep                        false
% 7.48/1.52  --abstr_ref_until_sat                   false
% 7.48/1.52  --abstr_ref_sig_restrict                funpre
% 7.48/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.48/1.52  --abstr_ref_under                       []
% 7.48/1.52  
% 7.48/1.52  ------ SAT Options
% 7.48/1.52  
% 7.48/1.52  --sat_mode                              false
% 7.48/1.52  --sat_fm_restart_options                ""
% 7.48/1.52  --sat_gr_def                            false
% 7.48/1.52  --sat_epr_types                         true
% 7.48/1.52  --sat_non_cyclic_types                  false
% 7.48/1.52  --sat_finite_models                     false
% 7.48/1.52  --sat_fm_lemmas                         false
% 7.48/1.52  --sat_fm_prep                           false
% 7.48/1.52  --sat_fm_uc_incr                        true
% 7.48/1.52  --sat_out_model                         small
% 7.48/1.52  --sat_out_clauses                       false
% 7.48/1.52  
% 7.48/1.52  ------ QBF Options
% 7.48/1.52  
% 7.48/1.52  --qbf_mode                              false
% 7.48/1.52  --qbf_elim_univ                         false
% 7.48/1.52  --qbf_dom_inst                          none
% 7.48/1.52  --qbf_dom_pre_inst                      false
% 7.48/1.52  --qbf_sk_in                             false
% 7.48/1.52  --qbf_pred_elim                         true
% 7.48/1.52  --qbf_split                             512
% 7.48/1.52  
% 7.48/1.52  ------ BMC1 Options
% 7.48/1.52  
% 7.48/1.52  --bmc1_incremental                      false
% 7.48/1.52  --bmc1_axioms                           reachable_all
% 7.48/1.52  --bmc1_min_bound                        0
% 7.48/1.52  --bmc1_max_bound                        -1
% 7.48/1.52  --bmc1_max_bound_default                -1
% 7.48/1.52  --bmc1_symbol_reachability              true
% 7.48/1.52  --bmc1_property_lemmas                  false
% 7.48/1.52  --bmc1_k_induction                      false
% 7.48/1.52  --bmc1_non_equiv_states                 false
% 7.48/1.52  --bmc1_deadlock                         false
% 7.48/1.52  --bmc1_ucm                              false
% 7.48/1.52  --bmc1_add_unsat_core                   none
% 7.48/1.52  --bmc1_unsat_core_children              false
% 7.48/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.48/1.52  --bmc1_out_stat                         full
% 7.48/1.52  --bmc1_ground_init                      false
% 7.48/1.52  --bmc1_pre_inst_next_state              false
% 7.48/1.52  --bmc1_pre_inst_state                   false
% 7.48/1.52  --bmc1_pre_inst_reach_state             false
% 7.48/1.52  --bmc1_out_unsat_core                   false
% 7.48/1.52  --bmc1_aig_witness_out                  false
% 7.48/1.52  --bmc1_verbose                          false
% 7.48/1.52  --bmc1_dump_clauses_tptp                false
% 7.48/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.48/1.52  --bmc1_dump_file                        -
% 7.48/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.48/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.48/1.52  --bmc1_ucm_extend_mode                  1
% 7.48/1.52  --bmc1_ucm_init_mode                    2
% 7.48/1.52  --bmc1_ucm_cone_mode                    none
% 7.48/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.48/1.52  --bmc1_ucm_relax_model                  4
% 7.48/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.48/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.48/1.52  --bmc1_ucm_layered_model                none
% 7.48/1.52  --bmc1_ucm_max_lemma_size               10
% 7.48/1.52  
% 7.48/1.52  ------ AIG Options
% 7.48/1.52  
% 7.48/1.52  --aig_mode                              false
% 7.48/1.52  
% 7.48/1.52  ------ Instantiation Options
% 7.48/1.52  
% 7.48/1.52  --instantiation_flag                    true
% 7.48/1.52  --inst_sos_flag                         false
% 7.48/1.52  --inst_sos_phase                        true
% 7.48/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.48/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.48/1.52  --inst_lit_sel_side                     none
% 7.48/1.52  --inst_solver_per_active                1400
% 7.48/1.52  --inst_solver_calls_frac                1.
% 7.48/1.52  --inst_passive_queue_type               priority_queues
% 7.48/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.48/1.52  --inst_passive_queues_freq              [25;2]
% 7.48/1.52  --inst_dismatching                      true
% 7.48/1.52  --inst_eager_unprocessed_to_passive     true
% 7.48/1.52  --inst_prop_sim_given                   true
% 7.48/1.52  --inst_prop_sim_new                     false
% 7.48/1.52  --inst_subs_new                         false
% 7.48/1.52  --inst_eq_res_simp                      false
% 7.48/1.52  --inst_subs_given                       false
% 7.48/1.52  --inst_orphan_elimination               true
% 7.48/1.52  --inst_learning_loop_flag               true
% 7.48/1.52  --inst_learning_start                   3000
% 7.48/1.52  --inst_learning_factor                  2
% 7.48/1.52  --inst_start_prop_sim_after_learn       3
% 7.48/1.52  --inst_sel_renew                        solver
% 7.48/1.52  --inst_lit_activity_flag                true
% 7.48/1.52  --inst_restr_to_given                   false
% 7.48/1.52  --inst_activity_threshold               500
% 7.48/1.52  --inst_out_proof                        true
% 7.48/1.52  
% 7.48/1.52  ------ Resolution Options
% 7.48/1.52  
% 7.48/1.52  --resolution_flag                       false
% 7.48/1.52  --res_lit_sel                           adaptive
% 7.48/1.52  --res_lit_sel_side                      none
% 7.48/1.52  --res_ordering                          kbo
% 7.48/1.52  --res_to_prop_solver                    active
% 7.48/1.52  --res_prop_simpl_new                    false
% 7.48/1.52  --res_prop_simpl_given                  true
% 7.48/1.52  --res_passive_queue_type                priority_queues
% 7.48/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.48/1.52  --res_passive_queues_freq               [15;5]
% 7.48/1.52  --res_forward_subs                      full
% 7.48/1.52  --res_backward_subs                     full
% 7.48/1.52  --res_forward_subs_resolution           true
% 7.48/1.52  --res_backward_subs_resolution          true
% 7.48/1.52  --res_orphan_elimination                true
% 7.48/1.52  --res_time_limit                        2.
% 7.48/1.52  --res_out_proof                         true
% 7.48/1.52  
% 7.48/1.52  ------ Superposition Options
% 7.48/1.52  
% 7.48/1.52  --superposition_flag                    true
% 7.48/1.52  --sup_passive_queue_type                priority_queues
% 7.48/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.48/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.48/1.52  --demod_completeness_check              fast
% 7.48/1.52  --demod_use_ground                      true
% 7.48/1.52  --sup_to_prop_solver                    passive
% 7.48/1.52  --sup_prop_simpl_new                    true
% 7.48/1.52  --sup_prop_simpl_given                  true
% 7.48/1.52  --sup_fun_splitting                     false
% 7.48/1.52  --sup_smt_interval                      50000
% 7.48/1.52  
% 7.48/1.52  ------ Superposition Simplification Setup
% 7.48/1.52  
% 7.48/1.52  --sup_indices_passive                   []
% 7.48/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.48/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.52  --sup_full_bw                           [BwDemod]
% 7.48/1.52  --sup_immed_triv                        [TrivRules]
% 7.48/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.48/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.52  --sup_immed_bw_main                     []
% 7.48/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.48/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.52  
% 7.48/1.52  ------ Combination Options
% 7.48/1.52  
% 7.48/1.52  --comb_res_mult                         3
% 7.48/1.52  --comb_sup_mult                         2
% 7.48/1.52  --comb_inst_mult                        10
% 7.48/1.52  
% 7.48/1.52  ------ Debug Options
% 7.48/1.52  
% 7.48/1.52  --dbg_backtrace                         false
% 7.48/1.52  --dbg_dump_prop_clauses                 false
% 7.48/1.52  --dbg_dump_prop_clauses_file            -
% 7.48/1.52  --dbg_out_stat                          false
% 7.48/1.52  
% 7.48/1.52  
% 7.48/1.52  
% 7.48/1.52  
% 7.48/1.52  ------ Proving...
% 7.48/1.52  
% 7.48/1.52  
% 7.48/1.52  % SZS status Theorem for theBenchmark.p
% 7.48/1.52  
% 7.48/1.52   Resolution empty clause
% 7.48/1.52  
% 7.48/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.48/1.52  
% 7.48/1.52  fof(f21,conjecture,(
% 7.48/1.52    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f22,negated_conjecture,(
% 7.48/1.52    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 7.48/1.52    inference(negated_conjecture,[],[f21])).
% 7.48/1.52  
% 7.48/1.52  fof(f29,plain,(
% 7.48/1.52    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 7.48/1.52    inference(ennf_transformation,[],[f22])).
% 7.48/1.52  
% 7.48/1.52  fof(f30,plain,(
% 7.48/1.52    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 7.48/1.52    inference(flattening,[],[f29])).
% 7.48/1.52  
% 7.48/1.52  fof(f38,plain,(
% 7.48/1.52    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2))),
% 7.48/1.52    introduced(choice_axiom,[])).
% 7.48/1.52  
% 7.48/1.52  fof(f39,plain,(
% 7.48/1.52    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2)),
% 7.48/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f38])).
% 7.48/1.52  
% 7.48/1.52  fof(f69,plain,(
% 7.48/1.52    r2_hidden(sK4,sK1)),
% 7.48/1.52    inference(cnf_transformation,[],[f39])).
% 7.48/1.52  
% 7.48/1.52  fof(f19,axiom,(
% 7.48/1.52    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f28,plain,(
% 7.48/1.52    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 7.48/1.52    inference(ennf_transformation,[],[f19])).
% 7.48/1.52  
% 7.48/1.52  fof(f63,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f28])).
% 7.48/1.52  
% 7.48/1.52  fof(f18,axiom,(
% 7.48/1.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f62,plain,(
% 7.48/1.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f18])).
% 7.48/1.52  
% 7.48/1.52  fof(f78,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 7.48/1.52    inference(definition_unfolding,[],[f63,f62])).
% 7.48/1.52  
% 7.48/1.52  fof(f9,axiom,(
% 7.48/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f48,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f9])).
% 7.48/1.52  
% 7.48/1.52  fof(f1,axiom,(
% 7.48/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f40,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f1])).
% 7.48/1.52  
% 7.48/1.52  fof(f13,axiom,(
% 7.48/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f52,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.48/1.52    inference(cnf_transformation,[],[f13])).
% 7.48/1.52  
% 7.48/1.52  fof(f71,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.48/1.52    inference(definition_unfolding,[],[f40,f52,f52])).
% 7.48/1.52  
% 7.48/1.52  fof(f68,plain,(
% 7.48/1.52    k3_xboole_0(sK2,sK3) = k1_tarski(sK4)),
% 7.48/1.52    inference(cnf_transformation,[],[f39])).
% 7.48/1.52  
% 7.48/1.52  fof(f83,plain,(
% 7.48/1.52    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k2_tarski(sK4,sK4)),
% 7.48/1.52    inference(definition_unfolding,[],[f68,f52,f62])).
% 7.48/1.52  
% 7.48/1.52  fof(f5,axiom,(
% 7.48/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f25,plain,(
% 7.48/1.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.48/1.52    inference(ennf_transformation,[],[f5])).
% 7.48/1.52  
% 7.48/1.52  fof(f44,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f25])).
% 7.48/1.52  
% 7.48/1.52  fof(f73,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.48/1.52    inference(definition_unfolding,[],[f44,f52])).
% 7.48/1.52  
% 7.48/1.52  fof(f67,plain,(
% 7.48/1.52    r1_tarski(sK1,sK2)),
% 7.48/1.52    inference(cnf_transformation,[],[f39])).
% 7.48/1.52  
% 7.48/1.52  fof(f14,axiom,(
% 7.48/1.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f53,plain,(
% 7.48/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f14])).
% 7.48/1.52  
% 7.48/1.52  fof(f75,plain,(
% 7.48/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.48/1.52    inference(definition_unfolding,[],[f53,f52,f52])).
% 7.48/1.52  
% 7.48/1.52  fof(f12,axiom,(
% 7.48/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f51,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.48/1.52    inference(cnf_transformation,[],[f12])).
% 7.48/1.52  
% 7.48/1.52  fof(f74,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.48/1.52    inference(definition_unfolding,[],[f51,f52])).
% 7.48/1.52  
% 7.48/1.52  fof(f4,axiom,(
% 7.48/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f24,plain,(
% 7.48/1.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.48/1.52    inference(ennf_transformation,[],[f4])).
% 7.48/1.52  
% 7.48/1.52  fof(f43,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f24])).
% 7.48/1.52  
% 7.48/1.52  fof(f7,axiom,(
% 7.48/1.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f46,plain,(
% 7.48/1.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f7])).
% 7.48/1.52  
% 7.48/1.52  fof(f15,axiom,(
% 7.48/1.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f54,plain,(
% 7.48/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.48/1.52    inference(cnf_transformation,[],[f15])).
% 7.48/1.52  
% 7.48/1.52  fof(f76,plain,(
% 7.48/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 7.48/1.52    inference(definition_unfolding,[],[f54,f52,f52,f52])).
% 7.48/1.52  
% 7.48/1.52  fof(f11,axiom,(
% 7.48/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f27,plain,(
% 7.48/1.52    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 7.48/1.52    inference(ennf_transformation,[],[f11])).
% 7.48/1.52  
% 7.48/1.52  fof(f50,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f27])).
% 7.48/1.52  
% 7.48/1.52  fof(f10,axiom,(
% 7.48/1.52    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f49,plain,(
% 7.48/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.48/1.52    inference(cnf_transformation,[],[f10])).
% 7.48/1.52  
% 7.48/1.52  fof(f8,axiom,(
% 7.48/1.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f47,plain,(
% 7.48/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.48/1.52    inference(cnf_transformation,[],[f8])).
% 7.48/1.52  
% 7.48/1.52  fof(f2,axiom,(
% 7.48/1.52    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.48/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.52  
% 7.48/1.52  fof(f23,plain,(
% 7.48/1.52    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.48/1.52    inference(rectify,[],[f2])).
% 7.48/1.52  
% 7.48/1.52  fof(f41,plain,(
% 7.48/1.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.48/1.52    inference(cnf_transformation,[],[f23])).
% 7.48/1.52  
% 7.48/1.52  fof(f70,plain,(
% 7.48/1.52    k3_xboole_0(sK1,sK3) != k1_tarski(sK4)),
% 7.48/1.52    inference(cnf_transformation,[],[f39])).
% 7.48/1.52  
% 7.48/1.52  fof(f82,plain,(
% 7.48/1.52    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k2_tarski(sK4,sK4)),
% 7.48/1.52    inference(definition_unfolding,[],[f70,f52,f62])).
% 7.48/1.52  
% 7.48/1.52  cnf(c_26,negated_conjecture,
% 7.48/1.52      ( r2_hidden(sK4,sK1) ),
% 7.48/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_428,plain,
% 7.48/1.52      ( r2_hidden(sK4,sK1) = iProver_top ),
% 7.48/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_21,plain,
% 7.48/1.52      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k2_tarski(X0,X0),X1) = X1 ),
% 7.48/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_432,plain,
% 7.48/1.52      ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
% 7.48/1.52      | r2_hidden(X0,X1) != iProver_top ),
% 7.48/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_7048,plain,
% 7.48/1.52      ( k2_xboole_0(k2_tarski(sK4,sK4),sK1) = sK1 ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_428,c_432]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_8,plain,
% 7.48/1.52      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.48/1.52      inference(cnf_transformation,[],[f48]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_8085,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),sK1) = k4_xboole_0(sK1,sK1) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_7048,c_8]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_0,plain,
% 7.48/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.48/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_9170,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK4,sK4))) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_8085,c_0]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_27,negated_conjecture,
% 7.48/1.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k2_tarski(sK4,sK4) ),
% 7.48/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_4,plain,
% 7.48/1.52      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.48/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_28,negated_conjecture,
% 7.48/1.52      ( r1_tarski(sK1,sK2) ),
% 7.48/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_228,plain,
% 7.48/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | sK2 != X1 | sK1 != X0 ),
% 7.48/1.52      inference(resolution_lifted,[status(thm)],[c_4,c_28]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_229,plain,
% 7.48/1.52      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK1 ),
% 7.48/1.52      inference(unflattening,[status(thm)],[c_228]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_12,plain,
% 7.48/1.52      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.48/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_2581,plain,
% 7.48/1.52      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK1,X0) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_229,c_12]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_7004,plain,
% 7.48/1.52      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_27,c_2581]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_9182,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
% 7.48/1.52      inference(light_normalisation,[status(thm)],[c_9170,c_7004]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_11,plain,
% 7.48/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.48/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_7019,plain,
% 7.48/1.52      ( k4_xboole_0(sK1,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_2581,c_11]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_3,plain,
% 7.48/1.52      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.48/1.52      inference(cnf_transformation,[],[f43]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_6,plain,
% 7.48/1.52      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.48/1.52      inference(cnf_transformation,[],[f46]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_217,plain,
% 7.48/1.52      ( X0 != X1 | k2_xboole_0(X2,X1) = X1 | k4_xboole_0(X0,X3) != X2 ),
% 7.48/1.52      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_218,plain,
% 7.48/1.52      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.48/1.52      inference(unflattening,[status(thm)],[c_217]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_932,plain,
% 7.48/1.52      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_218,c_8]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_5732,plain,
% 7.48/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_932,c_12]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_13,plain,
% 7.48/1.52      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.48/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_2733,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_27,c_13]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_2580,plain,
% 7.48/1.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) = k4_xboole_0(k2_tarski(sK4,sK4),X0) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_27,c_12]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_3263,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(k2_tarski(sK4,sK4),X0) ),
% 7.48/1.52      inference(light_normalisation,[status(thm)],[c_2733,c_2580]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_16787,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(X0,sK2)) = k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,sK2)) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_5732,c_3263]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_632,plain,
% 7.48/1.52      ( k2_xboole_0(k2_tarski(sK4,sK4),sK2) = sK2 ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_27,c_218]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_1252,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),sK2) = k4_xboole_0(sK2,sK2) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_632,c_8]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_4623,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_tarski(sK4,sK4))) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_1252,c_0]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_2305,plain,
% 7.48/1.52      ( k4_xboole_0(sK2,k2_tarski(sK4,sK4)) = k4_xboole_0(sK2,sK3) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_27,c_11]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_4632,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(sK2,sK2)) = k2_tarski(sK4,sK4) ),
% 7.48/1.52      inference(light_normalisation,[status(thm)],[c_4623,c_27,c_2305]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_16790,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(X0,sK2)) = k2_tarski(sK4,sK4) ),
% 7.48/1.52      inference(light_normalisation,[status(thm)],[c_16787,c_4632]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_17839,plain,
% 7.48/1.52      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k2_tarski(sK4,sK4))) = k4_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK4,sK4)) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_16790,c_0]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_10,plain,
% 7.48/1.52      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 7.48/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_205,plain,
% 7.48/1.52      ( X0 != X1
% 7.48/1.52      | k2_xboole_0(X2,k4_xboole_0(X1,X2)) = X1
% 7.48/1.52      | k4_xboole_0(X0,X3) != X2 ),
% 7.48/1.52      inference(resolution_lifted,[status(thm)],[c_10,c_6]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_206,plain,
% 7.48/1.52      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.48/1.52      inference(unflattening,[status(thm)],[c_205]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_767,plain,
% 7.48/1.52      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k2_tarski(sK4,sK4)) = sK2 ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_27,c_206]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_9,plain,
% 7.48/1.52      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.48/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_1204,plain,
% 7.48/1.52      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK3),X0)) = k4_xboole_0(k2_tarski(sK4,sK4),X0) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_27,c_9]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_1766,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK4,sK4)) = k4_xboole_0(sK2,sK2) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_767,c_1204]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_17855,plain,
% 7.48/1.52      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k2_tarski(sK4,sK4))) = k4_xboole_0(sK2,sK2) ),
% 7.48/1.52      inference(light_normalisation,[status(thm)],[c_17839,c_1766]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_17856,plain,
% 7.48/1.52      ( k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK2,k2_tarski(sK4,sK4))))) = k4_xboole_0(sK2,sK2) ),
% 7.48/1.52      inference(demodulation,[status(thm)],[c_17855,c_9]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_7,plain,
% 7.48/1.52      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.48/1.52      inference(cnf_transformation,[],[f47]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_4624,plain,
% 7.48/1.52      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,k2_tarski(sK4,sK4)) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_1252,c_7]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_1,plain,
% 7.48/1.52      ( k2_xboole_0(X0,X0) = X0 ),
% 7.48/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_4629,plain,
% 7.48/1.52      ( k2_xboole_0(sK2,k2_tarski(sK4,sK4)) = sK2 ),
% 7.48/1.52      inference(demodulation,[status(thm)],[c_4624,c_1,c_7]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_17857,plain,
% 7.48/1.52      ( k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(X0,sK2))) = k4_xboole_0(sK2,sK2) ),
% 7.48/1.52      inference(light_normalisation,[status(thm)],[c_17856,c_4629]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_5731,plain,
% 7.48/1.52      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_932,c_9]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_17858,plain,
% 7.48/1.52      ( k4_xboole_0(X0,X0) = k4_xboole_0(sK2,sK2) ),
% 7.48/1.52      inference(demodulation,[status(thm)],[c_17857,c_7,c_5731]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_18447,plain,
% 7.48/1.52      ( k4_xboole_0(k2_tarski(sK4,sK4),k4_xboole_0(X0,X0)) = k2_tarski(sK4,sK4) ),
% 7.48/1.52      inference(superposition,[status(thm)],[c_17858,c_4632]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_28858,plain,
% 7.48/1.52      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_tarski(sK4,sK4) ),
% 7.48/1.52      inference(demodulation,[status(thm)],[c_9182,c_7019,c_18447]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_25,negated_conjecture,
% 7.48/1.52      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k2_tarski(sK4,sK4) ),
% 7.48/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.48/1.52  
% 7.48/1.52  cnf(c_28860,plain,
% 7.48/1.52      ( $false ),
% 7.48/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_28858,c_25]) ).
% 7.48/1.52  
% 7.48/1.52  
% 7.48/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.48/1.52  
% 7.48/1.52  ------                               Statistics
% 7.48/1.52  
% 7.48/1.52  ------ General
% 7.48/1.52  
% 7.48/1.52  abstr_ref_over_cycles:                  0
% 7.48/1.52  abstr_ref_under_cycles:                 0
% 7.48/1.52  gc_basic_clause_elim:                   0
% 7.48/1.52  forced_gc_time:                         0
% 7.48/1.52  parsing_time:                           0.011
% 7.48/1.52  unif_index_cands_time:                  0.
% 7.48/1.52  unif_index_add_time:                    0.
% 7.48/1.52  orderings_time:                         0.
% 7.48/1.52  out_proof_time:                         0.007
% 7.48/1.52  total_time:                             0.951
% 7.48/1.52  num_of_symbols:                         41
% 7.48/1.52  num_of_terms:                           44171
% 7.48/1.52  
% 7.48/1.52  ------ Preprocessing
% 7.48/1.52  
% 7.48/1.52  num_of_splits:                          0
% 7.48/1.52  num_of_split_atoms:                     0
% 7.48/1.52  num_of_reused_defs:                     0
% 7.48/1.52  num_eq_ax_congr_red:                    6
% 7.48/1.52  num_of_sem_filtered_clauses:            1
% 7.48/1.52  num_of_subtypes:                        0
% 7.48/1.52  monotx_restored_types:                  0
% 7.48/1.52  sat_num_of_epr_types:                   0
% 7.48/1.52  sat_num_of_non_cyclic_types:            0
% 7.48/1.52  sat_guarded_non_collapsed_types:        0
% 7.48/1.52  num_pure_diseq_elim:                    0
% 7.48/1.52  simp_replaced_by:                       0
% 7.48/1.52  res_preprocessed:                       102
% 7.48/1.52  prep_upred:                             0
% 7.48/1.52  prep_unflattend:                        12
% 7.48/1.52  smt_new_axioms:                         0
% 7.48/1.52  pred_elim_cands:                        2
% 7.48/1.52  pred_elim:                              1
% 7.48/1.52  pred_elim_cl:                           -1
% 7.48/1.52  pred_elim_cycles:                       2
% 7.48/1.52  merged_defs:                            0
% 7.48/1.52  merged_defs_ncl:                        0
% 7.48/1.52  bin_hyper_res:                          0
% 7.48/1.52  prep_cycles:                            3
% 7.48/1.52  pred_elim_time:                         0.001
% 7.48/1.52  splitting_time:                         0.
% 7.48/1.52  sem_filter_time:                        0.
% 7.48/1.52  monotx_time:                            0.
% 7.48/1.52  subtype_inf_time:                       0.
% 7.48/1.52  
% 7.48/1.52  ------ Problem properties
% 7.48/1.52  
% 7.48/1.52  clauses:                                30
% 7.48/1.52  conjectures:                            3
% 7.48/1.52  epr:                                    1
% 7.48/1.52  horn:                                   27
% 7.48/1.52  ground:                                 6
% 7.48/1.52  unary:                                  22
% 7.48/1.52  binary:                                 3
% 7.48/1.52  lits:                                   44
% 7.48/1.52  lits_eq:                                31
% 7.48/1.52  fd_pure:                                0
% 7.48/1.52  fd_pseudo:                              0
% 7.48/1.52  fd_cond:                                0
% 7.48/1.52  fd_pseudo_cond:                         5
% 7.48/1.52  ac_symbols:                             0
% 7.48/1.52  
% 7.48/1.52  ------ Propositional Solver
% 7.48/1.52  
% 7.48/1.52  prop_solver_calls:                      24
% 7.48/1.52  prop_fast_solver_calls:                 525
% 7.48/1.52  smt_solver_calls:                       0
% 7.48/1.52  smt_fast_solver_calls:                  0
% 7.48/1.52  prop_num_of_clauses:                    9892
% 7.48/1.52  prop_preprocess_simplified:             14997
% 7.48/1.52  prop_fo_subsumed:                       0
% 7.48/1.52  prop_solver_time:                       0.
% 7.48/1.52  smt_solver_time:                        0.
% 7.48/1.52  smt_fast_solver_time:                   0.
% 7.48/1.52  prop_fast_solver_time:                  0.
% 7.48/1.52  prop_unsat_core_time:                   0.
% 7.48/1.52  
% 7.48/1.52  ------ QBF
% 7.48/1.52  
% 7.48/1.52  qbf_q_res:                              0
% 7.48/1.52  qbf_num_tautologies:                    0
% 7.48/1.52  qbf_prep_cycles:                        0
% 7.48/1.52  
% 7.48/1.52  ------ BMC1
% 7.48/1.52  
% 7.48/1.52  bmc1_current_bound:                     -1
% 7.48/1.52  bmc1_last_solved_bound:                 -1
% 7.48/1.52  bmc1_unsat_core_size:                   -1
% 7.48/1.52  bmc1_unsat_core_parents_size:           -1
% 7.48/1.52  bmc1_merge_next_fun:                    0
% 7.48/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.48/1.52  
% 7.48/1.52  ------ Instantiation
% 7.48/1.52  
% 7.48/1.52  inst_num_of_clauses:                    2350
% 7.48/1.52  inst_num_in_passive:                    751
% 7.48/1.52  inst_num_in_active:                     601
% 7.48/1.52  inst_num_in_unprocessed:                1000
% 7.48/1.52  inst_num_of_loops:                      770
% 7.48/1.52  inst_num_of_learning_restarts:          0
% 7.48/1.52  inst_num_moves_active_passive:          168
% 7.48/1.52  inst_lit_activity:                      0
% 7.48/1.52  inst_lit_activity_moves:                0
% 7.48/1.52  inst_num_tautologies:                   0
% 7.48/1.52  inst_num_prop_implied:                  0
% 7.48/1.52  inst_num_existing_simplified:           0
% 7.48/1.52  inst_num_eq_res_simplified:             0
% 7.48/1.52  inst_num_child_elim:                    0
% 7.48/1.52  inst_num_of_dismatching_blockings:      1261
% 7.48/1.52  inst_num_of_non_proper_insts:           1775
% 7.48/1.52  inst_num_of_duplicates:                 0
% 7.48/1.52  inst_inst_num_from_inst_to_res:         0
% 7.48/1.52  inst_dismatching_checking_time:         0.
% 7.48/1.52  
% 7.48/1.52  ------ Resolution
% 7.48/1.52  
% 7.48/1.52  res_num_of_clauses:                     0
% 7.48/1.52  res_num_in_passive:                     0
% 7.48/1.52  res_num_in_active:                      0
% 7.48/1.52  res_num_of_loops:                       105
% 7.48/1.52  res_forward_subset_subsumed:            289
% 7.48/1.52  res_backward_subset_subsumed:           6
% 7.48/1.52  res_forward_subsumed:                   0
% 7.48/1.52  res_backward_subsumed:                  0
% 7.48/1.52  res_forward_subsumption_resolution:     0
% 7.48/1.52  res_backward_subsumption_resolution:    0
% 7.48/1.52  res_clause_to_clause_subsumption:       18449
% 7.48/1.52  res_orphan_elimination:                 0
% 7.48/1.52  res_tautology_del:                      27
% 7.48/1.52  res_num_eq_res_simplified:              0
% 7.48/1.52  res_num_sel_changes:                    0
% 7.48/1.52  res_moves_from_active_to_pass:          0
% 7.48/1.52  
% 7.48/1.52  ------ Superposition
% 7.48/1.52  
% 7.48/1.52  sup_time_total:                         0.
% 7.48/1.52  sup_time_generating:                    0.
% 7.48/1.52  sup_time_sim_full:                      0.
% 7.48/1.52  sup_time_sim_immed:                     0.
% 7.48/1.52  
% 7.48/1.52  sup_num_of_clauses:                     1752
% 7.48/1.52  sup_num_in_active:                      100
% 7.48/1.52  sup_num_in_passive:                     1652
% 7.48/1.52  sup_num_of_loops:                       153
% 7.48/1.52  sup_fw_superposition:                   1596
% 7.48/1.52  sup_bw_superposition:                   2197
% 7.48/1.52  sup_immediate_simplified:               2753
% 7.48/1.52  sup_given_eliminated:                   15
% 7.48/1.52  comparisons_done:                       0
% 7.48/1.52  comparisons_avoided:                    3
% 7.48/1.52  
% 7.48/1.52  ------ Simplifications
% 7.48/1.52  
% 7.48/1.52  
% 7.48/1.52  sim_fw_subset_subsumed:                 3
% 7.48/1.52  sim_bw_subset_subsumed:                 0
% 7.48/1.52  sim_fw_subsumed:                        328
% 7.48/1.52  sim_bw_subsumed:                        40
% 7.48/1.52  sim_fw_subsumption_res:                 1
% 7.48/1.52  sim_bw_subsumption_res:                 3
% 7.48/1.52  sim_tautology_del:                      7
% 7.48/1.52  sim_eq_tautology_del:                   378
% 7.48/1.52  sim_eq_res_simp:                        0
% 7.48/1.52  sim_fw_demodulated:                     1774
% 7.48/1.52  sim_bw_demodulated:                     349
% 7.48/1.52  sim_light_normalised:                   1271
% 7.48/1.52  sim_joinable_taut:                      0
% 7.48/1.52  sim_joinable_simp:                      0
% 7.48/1.52  sim_ac_normalised:                      0
% 7.48/1.52  sim_smt_subsumption:                    0
% 7.48/1.52  
%------------------------------------------------------------------------------
