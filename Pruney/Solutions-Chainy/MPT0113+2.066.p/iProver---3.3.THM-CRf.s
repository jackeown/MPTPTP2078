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
% DateTime   : Thu Dec  3 11:25:53 EST 2020

% Result     : Theorem 43.60s
% Output     : CNFRefutation 43.60s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 759 expanded)
%              Number of clauses        :   46 ( 230 expanded)
%              Number of leaves         :   12 ( 227 expanded)
%              Depth                    :   17
%              Number of atoms          :  128 ( 839 expanded)
%              Number of equality atoms :   64 ( 720 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f28,f22,f22])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f27,f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f29,f22,f22,f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f33,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f33,f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f30,f22])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_235,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_718,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_235])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_236,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1896,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_718,c_236])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_716,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_240,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_3])).

cnf(c_733,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_716,c_3,c_240])).

cnf(c_961,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_733,c_0])).

cnf(c_981,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_961,c_3,c_240])).

cnf(c_6,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1108,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_981,c_6])).

cnf(c_161405,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X0) ),
    inference(superposition,[status(thm)],[c_1896,c_1108])).

cnf(c_717,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_965,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_733,c_8])).

cnf(c_1125,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_965,c_981])).

cnf(c_125045,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_717,c_1125])).

cnf(c_125516,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_125045,c_0])).

cnf(c_715,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2))))) = k3_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_125684,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)))) = k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(superposition,[status(thm)],[c_125516,c_715])).

cnf(c_125710,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_125684,c_0,c_240])).

cnf(c_161427,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_161405,c_125710])).

cnf(c_984,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_981,c_733])).

cnf(c_161428,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_161427,c_3,c_240,c_984])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_234,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1894,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_234,c_236])).

cnf(c_846,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X3)))) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_79500,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k3_xboole_0(X0,sK2)))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) ),
    inference(superposition,[status(thm)],[c_1894,c_846])).

cnf(c_81836,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),sK2))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK0) ),
    inference(superposition,[status(thm)],[c_981,c_79500])).

cnf(c_161703,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_161428,c_81836])).

cnf(c_161705,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_161703,c_161428])).

cnf(c_416,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_281,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_350,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_81,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_82,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_161705,c_416,c_350,c_82,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:06:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 43.60/6.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.60/6.01  
% 43.60/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.60/6.01  
% 43.60/6.01  ------  iProver source info
% 43.60/6.01  
% 43.60/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.60/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.60/6.01  git: non_committed_changes: false
% 43.60/6.01  git: last_make_outside_of_git: false
% 43.60/6.01  
% 43.60/6.01  ------ 
% 43.60/6.01  
% 43.60/6.01  ------ Input Options
% 43.60/6.01  
% 43.60/6.01  --out_options                           all
% 43.60/6.01  --tptp_safe_out                         true
% 43.60/6.01  --problem_path                          ""
% 43.60/6.01  --include_path                          ""
% 43.60/6.01  --clausifier                            res/vclausify_rel
% 43.60/6.01  --clausifier_options                    --mode clausify
% 43.60/6.01  --stdin                                 false
% 43.60/6.01  --stats_out                             all
% 43.60/6.01  
% 43.60/6.01  ------ General Options
% 43.60/6.01  
% 43.60/6.01  --fof                                   false
% 43.60/6.01  --time_out_real                         305.
% 43.60/6.01  --time_out_virtual                      -1.
% 43.60/6.01  --symbol_type_check                     false
% 43.60/6.01  --clausify_out                          false
% 43.60/6.01  --sig_cnt_out                           false
% 43.60/6.01  --trig_cnt_out                          false
% 43.60/6.01  --trig_cnt_out_tolerance                1.
% 43.60/6.01  --trig_cnt_out_sk_spl                   false
% 43.60/6.01  --abstr_cl_out                          false
% 43.60/6.01  
% 43.60/6.01  ------ Global Options
% 43.60/6.01  
% 43.60/6.01  --schedule                              default
% 43.60/6.01  --add_important_lit                     false
% 43.60/6.01  --prop_solver_per_cl                    1000
% 43.60/6.01  --min_unsat_core                        false
% 43.60/6.01  --soft_assumptions                      false
% 43.60/6.01  --soft_lemma_size                       3
% 43.60/6.01  --prop_impl_unit_size                   0
% 43.60/6.01  --prop_impl_unit                        []
% 43.60/6.01  --share_sel_clauses                     true
% 43.60/6.01  --reset_solvers                         false
% 43.60/6.01  --bc_imp_inh                            [conj_cone]
% 43.60/6.01  --conj_cone_tolerance                   3.
% 43.60/6.01  --extra_neg_conj                        none
% 43.60/6.01  --large_theory_mode                     true
% 43.60/6.01  --prolific_symb_bound                   200
% 43.60/6.01  --lt_threshold                          2000
% 43.60/6.01  --clause_weak_htbl                      true
% 43.60/6.01  --gc_record_bc_elim                     false
% 43.60/6.01  
% 43.60/6.01  ------ Preprocessing Options
% 43.60/6.01  
% 43.60/6.01  --preprocessing_flag                    true
% 43.60/6.01  --time_out_prep_mult                    0.1
% 43.60/6.01  --splitting_mode                        input
% 43.60/6.01  --splitting_grd                         true
% 43.60/6.01  --splitting_cvd                         false
% 43.60/6.01  --splitting_cvd_svl                     false
% 43.60/6.01  --splitting_nvd                         32
% 43.60/6.01  --sub_typing                            true
% 43.60/6.01  --prep_gs_sim                           true
% 43.60/6.01  --prep_unflatten                        true
% 43.60/6.01  --prep_res_sim                          true
% 43.60/6.01  --prep_upred                            true
% 43.60/6.01  --prep_sem_filter                       exhaustive
% 43.60/6.01  --prep_sem_filter_out                   false
% 43.60/6.01  --pred_elim                             true
% 43.60/6.01  --res_sim_input                         true
% 43.60/6.01  --eq_ax_congr_red                       true
% 43.60/6.01  --pure_diseq_elim                       true
% 43.60/6.01  --brand_transform                       false
% 43.60/6.01  --non_eq_to_eq                          false
% 43.60/6.01  --prep_def_merge                        true
% 43.60/6.01  --prep_def_merge_prop_impl              false
% 43.60/6.01  --prep_def_merge_mbd                    true
% 43.60/6.01  --prep_def_merge_tr_red                 false
% 43.60/6.01  --prep_def_merge_tr_cl                  false
% 43.60/6.01  --smt_preprocessing                     true
% 43.60/6.01  --smt_ac_axioms                         fast
% 43.60/6.01  --preprocessed_out                      false
% 43.60/6.01  --preprocessed_stats                    false
% 43.60/6.01  
% 43.60/6.01  ------ Abstraction refinement Options
% 43.60/6.01  
% 43.60/6.01  --abstr_ref                             []
% 43.60/6.01  --abstr_ref_prep                        false
% 43.60/6.01  --abstr_ref_until_sat                   false
% 43.60/6.01  --abstr_ref_sig_restrict                funpre
% 43.60/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.60/6.01  --abstr_ref_under                       []
% 43.60/6.01  
% 43.60/6.01  ------ SAT Options
% 43.60/6.01  
% 43.60/6.01  --sat_mode                              false
% 43.60/6.01  --sat_fm_restart_options                ""
% 43.60/6.01  --sat_gr_def                            false
% 43.60/6.01  --sat_epr_types                         true
% 43.60/6.01  --sat_non_cyclic_types                  false
% 43.60/6.01  --sat_finite_models                     false
% 43.60/6.01  --sat_fm_lemmas                         false
% 43.60/6.01  --sat_fm_prep                           false
% 43.60/6.01  --sat_fm_uc_incr                        true
% 43.60/6.01  --sat_out_model                         small
% 43.60/6.01  --sat_out_clauses                       false
% 43.60/6.01  
% 43.60/6.01  ------ QBF Options
% 43.60/6.01  
% 43.60/6.01  --qbf_mode                              false
% 43.60/6.01  --qbf_elim_univ                         false
% 43.60/6.01  --qbf_dom_inst                          none
% 43.60/6.01  --qbf_dom_pre_inst                      false
% 43.60/6.01  --qbf_sk_in                             false
% 43.60/6.01  --qbf_pred_elim                         true
% 43.60/6.01  --qbf_split                             512
% 43.60/6.01  
% 43.60/6.01  ------ BMC1 Options
% 43.60/6.01  
% 43.60/6.01  --bmc1_incremental                      false
% 43.60/6.01  --bmc1_axioms                           reachable_all
% 43.60/6.01  --bmc1_min_bound                        0
% 43.60/6.01  --bmc1_max_bound                        -1
% 43.60/6.01  --bmc1_max_bound_default                -1
% 43.60/6.01  --bmc1_symbol_reachability              true
% 43.60/6.01  --bmc1_property_lemmas                  false
% 43.60/6.01  --bmc1_k_induction                      false
% 43.60/6.01  --bmc1_non_equiv_states                 false
% 43.60/6.01  --bmc1_deadlock                         false
% 43.60/6.01  --bmc1_ucm                              false
% 43.60/6.01  --bmc1_add_unsat_core                   none
% 43.60/6.01  --bmc1_unsat_core_children              false
% 43.60/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.60/6.01  --bmc1_out_stat                         full
% 43.60/6.01  --bmc1_ground_init                      false
% 43.60/6.01  --bmc1_pre_inst_next_state              false
% 43.60/6.01  --bmc1_pre_inst_state                   false
% 43.60/6.01  --bmc1_pre_inst_reach_state             false
% 43.60/6.01  --bmc1_out_unsat_core                   false
% 43.60/6.01  --bmc1_aig_witness_out                  false
% 43.60/6.01  --bmc1_verbose                          false
% 43.60/6.01  --bmc1_dump_clauses_tptp                false
% 43.60/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.60/6.01  --bmc1_dump_file                        -
% 43.60/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.60/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.60/6.01  --bmc1_ucm_extend_mode                  1
% 43.60/6.01  --bmc1_ucm_init_mode                    2
% 43.60/6.01  --bmc1_ucm_cone_mode                    none
% 43.60/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.60/6.01  --bmc1_ucm_relax_model                  4
% 43.60/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.60/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.60/6.01  --bmc1_ucm_layered_model                none
% 43.60/6.01  --bmc1_ucm_max_lemma_size               10
% 43.60/6.01  
% 43.60/6.01  ------ AIG Options
% 43.60/6.01  
% 43.60/6.01  --aig_mode                              false
% 43.60/6.01  
% 43.60/6.01  ------ Instantiation Options
% 43.60/6.01  
% 43.60/6.01  --instantiation_flag                    true
% 43.60/6.01  --inst_sos_flag                         false
% 43.60/6.01  --inst_sos_phase                        true
% 43.60/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.60/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.60/6.01  --inst_lit_sel_side                     num_symb
% 43.60/6.01  --inst_solver_per_active                1400
% 43.60/6.01  --inst_solver_calls_frac                1.
% 43.60/6.01  --inst_passive_queue_type               priority_queues
% 43.60/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.60/6.01  --inst_passive_queues_freq              [25;2]
% 43.60/6.01  --inst_dismatching                      true
% 43.60/6.01  --inst_eager_unprocessed_to_passive     true
% 43.60/6.01  --inst_prop_sim_given                   true
% 43.60/6.01  --inst_prop_sim_new                     false
% 43.60/6.01  --inst_subs_new                         false
% 43.60/6.01  --inst_eq_res_simp                      false
% 43.60/6.01  --inst_subs_given                       false
% 43.60/6.01  --inst_orphan_elimination               true
% 43.60/6.01  --inst_learning_loop_flag               true
% 43.60/6.01  --inst_learning_start                   3000
% 43.60/6.01  --inst_learning_factor                  2
% 43.60/6.01  --inst_start_prop_sim_after_learn       3
% 43.60/6.01  --inst_sel_renew                        solver
% 43.60/6.01  --inst_lit_activity_flag                true
% 43.60/6.01  --inst_restr_to_given                   false
% 43.60/6.01  --inst_activity_threshold               500
% 43.60/6.01  --inst_out_proof                        true
% 43.60/6.01  
% 43.60/6.01  ------ Resolution Options
% 43.60/6.01  
% 43.60/6.01  --resolution_flag                       true
% 43.60/6.01  --res_lit_sel                           adaptive
% 43.60/6.01  --res_lit_sel_side                      none
% 43.60/6.01  --res_ordering                          kbo
% 43.60/6.01  --res_to_prop_solver                    active
% 43.60/6.01  --res_prop_simpl_new                    false
% 43.60/6.01  --res_prop_simpl_given                  true
% 43.60/6.01  --res_passive_queue_type                priority_queues
% 43.60/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.60/6.01  --res_passive_queues_freq               [15;5]
% 43.60/6.01  --res_forward_subs                      full
% 43.60/6.01  --res_backward_subs                     full
% 43.60/6.01  --res_forward_subs_resolution           true
% 43.60/6.01  --res_backward_subs_resolution          true
% 43.60/6.01  --res_orphan_elimination                true
% 43.60/6.01  --res_time_limit                        2.
% 43.60/6.01  --res_out_proof                         true
% 43.60/6.01  
% 43.60/6.01  ------ Superposition Options
% 43.60/6.01  
% 43.60/6.01  --superposition_flag                    true
% 43.60/6.01  --sup_passive_queue_type                priority_queues
% 43.60/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.60/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.60/6.01  --demod_completeness_check              fast
% 43.60/6.01  --demod_use_ground                      true
% 43.60/6.01  --sup_to_prop_solver                    passive
% 43.60/6.01  --sup_prop_simpl_new                    true
% 43.60/6.01  --sup_prop_simpl_given                  true
% 43.60/6.01  --sup_fun_splitting                     false
% 43.60/6.01  --sup_smt_interval                      50000
% 43.60/6.01  
% 43.60/6.01  ------ Superposition Simplification Setup
% 43.60/6.01  
% 43.60/6.01  --sup_indices_passive                   []
% 43.60/6.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.60/6.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.60/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.60/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.60/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.60/6.01  --sup_full_bw                           [BwDemod]
% 43.60/6.01  --sup_immed_triv                        [TrivRules]
% 43.60/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.60/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.60/6.01  --sup_immed_bw_main                     []
% 43.60/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.60/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.60/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.60/6.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.60/6.01  
% 43.60/6.01  ------ Combination Options
% 43.60/6.01  
% 43.60/6.01  --comb_res_mult                         3
% 43.60/6.01  --comb_sup_mult                         2
% 43.60/6.01  --comb_inst_mult                        10
% 43.60/6.01  
% 43.60/6.01  ------ Debug Options
% 43.60/6.01  
% 43.60/6.01  --dbg_backtrace                         false
% 43.60/6.01  --dbg_dump_prop_clauses                 false
% 43.60/6.01  --dbg_dump_prop_clauses_file            -
% 43.60/6.01  --dbg_out_stat                          false
% 43.60/6.01  ------ Parsing...
% 43.60/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.60/6.01  
% 43.60/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 43.60/6.01  
% 43.60/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.60/6.01  
% 43.60/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.60/6.01  ------ Proving...
% 43.60/6.01  ------ Problem Properties 
% 43.60/6.01  
% 43.60/6.01  
% 43.60/6.01  clauses                                 11
% 43.60/6.01  conjectures                             1
% 43.60/6.01  EPR                                     1
% 43.60/6.01  Horn                                    11
% 43.60/6.01  unary                                   8
% 43.60/6.01  binary                                  2
% 43.60/6.01  lits                                    15
% 43.60/6.01  lits eq                                 8
% 43.60/6.01  fd_pure                                 0
% 43.60/6.01  fd_pseudo                               0
% 43.60/6.01  fd_cond                                 0
% 43.60/6.01  fd_pseudo_cond                          0
% 43.60/6.01  AC symbols                              0
% 43.60/6.01  
% 43.60/6.01  ------ Schedule dynamic 5 is on 
% 43.60/6.01  
% 43.60/6.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.60/6.01  
% 43.60/6.01  
% 43.60/6.01  ------ 
% 43.60/6.01  Current options:
% 43.60/6.01  ------ 
% 43.60/6.01  
% 43.60/6.01  ------ Input Options
% 43.60/6.01  
% 43.60/6.01  --out_options                           all
% 43.60/6.01  --tptp_safe_out                         true
% 43.60/6.01  --problem_path                          ""
% 43.60/6.01  --include_path                          ""
% 43.60/6.01  --clausifier                            res/vclausify_rel
% 43.60/6.01  --clausifier_options                    --mode clausify
% 43.60/6.01  --stdin                                 false
% 43.60/6.01  --stats_out                             all
% 43.60/6.01  
% 43.60/6.01  ------ General Options
% 43.60/6.01  
% 43.60/6.01  --fof                                   false
% 43.60/6.01  --time_out_real                         305.
% 43.60/6.01  --time_out_virtual                      -1.
% 43.60/6.01  --symbol_type_check                     false
% 43.60/6.01  --clausify_out                          false
% 43.60/6.01  --sig_cnt_out                           false
% 43.60/6.01  --trig_cnt_out                          false
% 43.60/6.01  --trig_cnt_out_tolerance                1.
% 43.60/6.01  --trig_cnt_out_sk_spl                   false
% 43.60/6.01  --abstr_cl_out                          false
% 43.60/6.01  
% 43.60/6.01  ------ Global Options
% 43.60/6.01  
% 43.60/6.01  --schedule                              default
% 43.60/6.01  --add_important_lit                     false
% 43.60/6.01  --prop_solver_per_cl                    1000
% 43.60/6.01  --min_unsat_core                        false
% 43.60/6.01  --soft_assumptions                      false
% 43.60/6.01  --soft_lemma_size                       3
% 43.60/6.01  --prop_impl_unit_size                   0
% 43.60/6.01  --prop_impl_unit                        []
% 43.60/6.01  --share_sel_clauses                     true
% 43.60/6.01  --reset_solvers                         false
% 43.60/6.01  --bc_imp_inh                            [conj_cone]
% 43.60/6.01  --conj_cone_tolerance                   3.
% 43.60/6.01  --extra_neg_conj                        none
% 43.60/6.01  --large_theory_mode                     true
% 43.60/6.01  --prolific_symb_bound                   200
% 43.60/6.01  --lt_threshold                          2000
% 43.60/6.01  --clause_weak_htbl                      true
% 43.60/6.01  --gc_record_bc_elim                     false
% 43.60/6.01  
% 43.60/6.01  ------ Preprocessing Options
% 43.60/6.01  
% 43.60/6.01  --preprocessing_flag                    true
% 43.60/6.01  --time_out_prep_mult                    0.1
% 43.60/6.01  --splitting_mode                        input
% 43.60/6.01  --splitting_grd                         true
% 43.60/6.01  --splitting_cvd                         false
% 43.60/6.01  --splitting_cvd_svl                     false
% 43.60/6.01  --splitting_nvd                         32
% 43.60/6.01  --sub_typing                            true
% 43.60/6.01  --prep_gs_sim                           true
% 43.60/6.01  --prep_unflatten                        true
% 43.60/6.01  --prep_res_sim                          true
% 43.60/6.01  --prep_upred                            true
% 43.60/6.01  --prep_sem_filter                       exhaustive
% 43.60/6.01  --prep_sem_filter_out                   false
% 43.60/6.01  --pred_elim                             true
% 43.60/6.01  --res_sim_input                         true
% 43.60/6.01  --eq_ax_congr_red                       true
% 43.60/6.01  --pure_diseq_elim                       true
% 43.60/6.01  --brand_transform                       false
% 43.60/6.01  --non_eq_to_eq                          false
% 43.60/6.01  --prep_def_merge                        true
% 43.60/6.01  --prep_def_merge_prop_impl              false
% 43.60/6.01  --prep_def_merge_mbd                    true
% 43.60/6.01  --prep_def_merge_tr_red                 false
% 43.60/6.01  --prep_def_merge_tr_cl                  false
% 43.60/6.01  --smt_preprocessing                     true
% 43.60/6.01  --smt_ac_axioms                         fast
% 43.60/6.01  --preprocessed_out                      false
% 43.60/6.01  --preprocessed_stats                    false
% 43.60/6.01  
% 43.60/6.01  ------ Abstraction refinement Options
% 43.60/6.01  
% 43.60/6.01  --abstr_ref                             []
% 43.60/6.01  --abstr_ref_prep                        false
% 43.60/6.01  --abstr_ref_until_sat                   false
% 43.60/6.01  --abstr_ref_sig_restrict                funpre
% 43.60/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.60/6.01  --abstr_ref_under                       []
% 43.60/6.01  
% 43.60/6.01  ------ SAT Options
% 43.60/6.01  
% 43.60/6.01  --sat_mode                              false
% 43.60/6.01  --sat_fm_restart_options                ""
% 43.60/6.01  --sat_gr_def                            false
% 43.60/6.01  --sat_epr_types                         true
% 43.60/6.01  --sat_non_cyclic_types                  false
% 43.60/6.01  --sat_finite_models                     false
% 43.60/6.01  --sat_fm_lemmas                         false
% 43.60/6.01  --sat_fm_prep                           false
% 43.60/6.01  --sat_fm_uc_incr                        true
% 43.60/6.01  --sat_out_model                         small
% 43.60/6.01  --sat_out_clauses                       false
% 43.60/6.01  
% 43.60/6.01  ------ QBF Options
% 43.60/6.01  
% 43.60/6.01  --qbf_mode                              false
% 43.60/6.01  --qbf_elim_univ                         false
% 43.60/6.01  --qbf_dom_inst                          none
% 43.60/6.01  --qbf_dom_pre_inst                      false
% 43.60/6.01  --qbf_sk_in                             false
% 43.60/6.01  --qbf_pred_elim                         true
% 43.60/6.01  --qbf_split                             512
% 43.60/6.01  
% 43.60/6.01  ------ BMC1 Options
% 43.60/6.01  
% 43.60/6.01  --bmc1_incremental                      false
% 43.60/6.01  --bmc1_axioms                           reachable_all
% 43.60/6.01  --bmc1_min_bound                        0
% 43.60/6.01  --bmc1_max_bound                        -1
% 43.60/6.01  --bmc1_max_bound_default                -1
% 43.60/6.01  --bmc1_symbol_reachability              true
% 43.60/6.01  --bmc1_property_lemmas                  false
% 43.60/6.01  --bmc1_k_induction                      false
% 43.60/6.01  --bmc1_non_equiv_states                 false
% 43.60/6.01  --bmc1_deadlock                         false
% 43.60/6.01  --bmc1_ucm                              false
% 43.60/6.01  --bmc1_add_unsat_core                   none
% 43.60/6.01  --bmc1_unsat_core_children              false
% 43.60/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.60/6.01  --bmc1_out_stat                         full
% 43.60/6.01  --bmc1_ground_init                      false
% 43.60/6.01  --bmc1_pre_inst_next_state              false
% 43.60/6.01  --bmc1_pre_inst_state                   false
% 43.60/6.01  --bmc1_pre_inst_reach_state             false
% 43.60/6.01  --bmc1_out_unsat_core                   false
% 43.60/6.01  --bmc1_aig_witness_out                  false
% 43.60/6.01  --bmc1_verbose                          false
% 43.60/6.01  --bmc1_dump_clauses_tptp                false
% 43.60/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.60/6.01  --bmc1_dump_file                        -
% 43.60/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.60/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.60/6.01  --bmc1_ucm_extend_mode                  1
% 43.60/6.01  --bmc1_ucm_init_mode                    2
% 43.60/6.01  --bmc1_ucm_cone_mode                    none
% 43.60/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.60/6.01  --bmc1_ucm_relax_model                  4
% 43.60/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.60/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.60/6.01  --bmc1_ucm_layered_model                none
% 43.60/6.01  --bmc1_ucm_max_lemma_size               10
% 43.60/6.01  
% 43.60/6.01  ------ AIG Options
% 43.60/6.01  
% 43.60/6.01  --aig_mode                              false
% 43.60/6.01  
% 43.60/6.01  ------ Instantiation Options
% 43.60/6.01  
% 43.60/6.01  --instantiation_flag                    true
% 43.60/6.01  --inst_sos_flag                         false
% 43.60/6.01  --inst_sos_phase                        true
% 43.60/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.60/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.60/6.01  --inst_lit_sel_side                     none
% 43.60/6.01  --inst_solver_per_active                1400
% 43.60/6.01  --inst_solver_calls_frac                1.
% 43.60/6.01  --inst_passive_queue_type               priority_queues
% 43.60/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.60/6.01  --inst_passive_queues_freq              [25;2]
% 43.60/6.01  --inst_dismatching                      true
% 43.60/6.01  --inst_eager_unprocessed_to_passive     true
% 43.60/6.01  --inst_prop_sim_given                   true
% 43.60/6.01  --inst_prop_sim_new                     false
% 43.60/6.01  --inst_subs_new                         false
% 43.60/6.01  --inst_eq_res_simp                      false
% 43.60/6.01  --inst_subs_given                       false
% 43.60/6.01  --inst_orphan_elimination               true
% 43.60/6.01  --inst_learning_loop_flag               true
% 43.60/6.01  --inst_learning_start                   3000
% 43.60/6.01  --inst_learning_factor                  2
% 43.60/6.01  --inst_start_prop_sim_after_learn       3
% 43.60/6.01  --inst_sel_renew                        solver
% 43.60/6.01  --inst_lit_activity_flag                true
% 43.60/6.01  --inst_restr_to_given                   false
% 43.60/6.01  --inst_activity_threshold               500
% 43.60/6.01  --inst_out_proof                        true
% 43.60/6.01  
% 43.60/6.01  ------ Resolution Options
% 43.60/6.01  
% 43.60/6.01  --resolution_flag                       false
% 43.60/6.01  --res_lit_sel                           adaptive
% 43.60/6.01  --res_lit_sel_side                      none
% 43.60/6.01  --res_ordering                          kbo
% 43.60/6.01  --res_to_prop_solver                    active
% 43.60/6.01  --res_prop_simpl_new                    false
% 43.60/6.01  --res_prop_simpl_given                  true
% 43.60/6.01  --res_passive_queue_type                priority_queues
% 43.60/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.60/6.01  --res_passive_queues_freq               [15;5]
% 43.60/6.01  --res_forward_subs                      full
% 43.60/6.01  --res_backward_subs                     full
% 43.60/6.01  --res_forward_subs_resolution           true
% 43.60/6.01  --res_backward_subs_resolution          true
% 43.60/6.01  --res_orphan_elimination                true
% 43.60/6.01  --res_time_limit                        2.
% 43.60/6.01  --res_out_proof                         true
% 43.60/6.01  
% 43.60/6.01  ------ Superposition Options
% 43.60/6.01  
% 43.60/6.01  --superposition_flag                    true
% 43.60/6.01  --sup_passive_queue_type                priority_queues
% 43.60/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.60/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.60/6.01  --demod_completeness_check              fast
% 43.60/6.01  --demod_use_ground                      true
% 43.60/6.01  --sup_to_prop_solver                    passive
% 43.60/6.01  --sup_prop_simpl_new                    true
% 43.60/6.01  --sup_prop_simpl_given                  true
% 43.60/6.01  --sup_fun_splitting                     false
% 43.60/6.01  --sup_smt_interval                      50000
% 43.60/6.01  
% 43.60/6.01  ------ Superposition Simplification Setup
% 43.60/6.01  
% 43.60/6.01  --sup_indices_passive                   []
% 43.60/6.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.60/6.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.60/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.60/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.60/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.60/6.01  --sup_full_bw                           [BwDemod]
% 43.60/6.01  --sup_immed_triv                        [TrivRules]
% 43.60/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.60/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.60/6.01  --sup_immed_bw_main                     []
% 43.60/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.60/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.60/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.60/6.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.60/6.01  
% 43.60/6.01  ------ Combination Options
% 43.60/6.01  
% 43.60/6.01  --comb_res_mult                         3
% 43.60/6.01  --comb_sup_mult                         2
% 43.60/6.01  --comb_inst_mult                        10
% 43.60/6.01  
% 43.60/6.01  ------ Debug Options
% 43.60/6.01  
% 43.60/6.01  --dbg_backtrace                         false
% 43.60/6.01  --dbg_dump_prop_clauses                 false
% 43.60/6.01  --dbg_dump_prop_clauses_file            -
% 43.60/6.01  --dbg_out_stat                          false
% 43.60/6.01  
% 43.60/6.01  
% 43.60/6.01  
% 43.60/6.01  
% 43.60/6.01  ------ Proving...
% 43.60/6.01  
% 43.60/6.01  
% 43.60/6.01  % SZS status Theorem for theBenchmark.p
% 43.60/6.01  
% 43.60/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.60/6.01  
% 43.60/6.01  fof(f7,axiom,(
% 43.60/6.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f28,plain,(
% 43.60/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 43.60/6.01    inference(cnf_transformation,[],[f7])).
% 43.60/6.01  
% 43.60/6.01  fof(f1,axiom,(
% 43.60/6.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f22,plain,(
% 43.60/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.60/6.01    inference(cnf_transformation,[],[f1])).
% 43.60/6.01  
% 43.60/6.01  fof(f35,plain,(
% 43.60/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 43.60/6.01    inference(definition_unfolding,[],[f28,f22,f22])).
% 43.60/6.01  
% 43.60/6.01  fof(f5,axiom,(
% 43.60/6.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f26,plain,(
% 43.60/6.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 43.60/6.01    inference(cnf_transformation,[],[f5])).
% 43.60/6.01  
% 43.60/6.01  fof(f36,plain,(
% 43.60/6.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 43.60/6.01    inference(definition_unfolding,[],[f26,f22])).
% 43.60/6.01  
% 43.60/6.01  fof(f3,axiom,(
% 43.60/6.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f17,plain,(
% 43.60/6.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 43.60/6.01    inference(ennf_transformation,[],[f3])).
% 43.60/6.01  
% 43.60/6.01  fof(f24,plain,(
% 43.60/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 43.60/6.01    inference(cnf_transformation,[],[f17])).
% 43.60/6.01  
% 43.60/6.01  fof(f4,axiom,(
% 43.60/6.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f25,plain,(
% 43.60/6.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 43.60/6.01    inference(cnf_transformation,[],[f4])).
% 43.60/6.01  
% 43.60/6.01  fof(f6,axiom,(
% 43.60/6.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f27,plain,(
% 43.60/6.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.60/6.01    inference(cnf_transformation,[],[f6])).
% 43.60/6.01  
% 43.60/6.01  fof(f37,plain,(
% 43.60/6.01    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 43.60/6.01    inference(definition_unfolding,[],[f27,f22])).
% 43.60/6.01  
% 43.60/6.01  fof(f8,axiom,(
% 43.60/6.01    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f29,plain,(
% 43.60/6.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 43.60/6.01    inference(cnf_transformation,[],[f8])).
% 43.60/6.01  
% 43.60/6.01  fof(f38,plain,(
% 43.60/6.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2))) )),
% 43.60/6.01    inference(definition_unfolding,[],[f29,f22,f22,f22])).
% 43.60/6.01  
% 43.60/6.01  fof(f10,axiom,(
% 43.60/6.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f31,plain,(
% 43.60/6.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 43.60/6.01    inference(cnf_transformation,[],[f10])).
% 43.60/6.01  
% 43.60/6.01  fof(f12,conjecture,(
% 43.60/6.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f13,negated_conjecture,(
% 43.60/6.01    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 43.60/6.01    inference(negated_conjecture,[],[f12])).
% 43.60/6.01  
% 43.60/6.01  fof(f19,plain,(
% 43.60/6.01    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 43.60/6.01    inference(ennf_transformation,[],[f13])).
% 43.60/6.01  
% 43.60/6.01  fof(f20,plain,(
% 43.60/6.01    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 43.60/6.01    introduced(choice_axiom,[])).
% 43.60/6.01  
% 43.60/6.01  fof(f21,plain,(
% 43.60/6.01    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 43.60/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 43.60/6.01  
% 43.60/6.01  fof(f33,plain,(
% 43.60/6.01    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 43.60/6.01    inference(cnf_transformation,[],[f21])).
% 43.60/6.01  
% 43.60/6.01  fof(f40,plain,(
% 43.60/6.01    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 43.60/6.01    inference(definition_unfolding,[],[f33,f22])).
% 43.60/6.01  
% 43.60/6.01  fof(f2,axiom,(
% 43.60/6.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f15,plain,(
% 43.60/6.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 43.60/6.01    inference(ennf_transformation,[],[f2])).
% 43.60/6.01  
% 43.60/6.01  fof(f16,plain,(
% 43.60/6.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 43.60/6.01    inference(flattening,[],[f15])).
% 43.60/6.01  
% 43.60/6.01  fof(f23,plain,(
% 43.60/6.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 43.60/6.01    inference(cnf_transformation,[],[f16])).
% 43.60/6.01  
% 43.60/6.01  fof(f9,axiom,(
% 43.60/6.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 43.60/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.60/6.01  
% 43.60/6.01  fof(f14,plain,(
% 43.60/6.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 43.60/6.01    inference(unused_predicate_definition_removal,[],[f9])).
% 43.60/6.01  
% 43.60/6.01  fof(f18,plain,(
% 43.60/6.01    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 43.60/6.01    inference(ennf_transformation,[],[f14])).
% 43.60/6.01  
% 43.60/6.01  fof(f30,plain,(
% 43.60/6.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 43.60/6.01    inference(cnf_transformation,[],[f18])).
% 43.60/6.01  
% 43.60/6.01  fof(f39,plain,(
% 43.60/6.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 43.60/6.01    inference(definition_unfolding,[],[f30,f22])).
% 43.60/6.01  
% 43.60/6.01  fof(f34,plain,(
% 43.60/6.01    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 43.60/6.01    inference(cnf_transformation,[],[f21])).
% 43.60/6.01  
% 43.60/6.01  cnf(c_0,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 43.60/6.01      inference(cnf_transformation,[],[f35]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_4,plain,
% 43.60/6.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 43.60/6.01      inference(cnf_transformation,[],[f36]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_235,plain,
% 43.60/6.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 43.60/6.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_718,plain,
% 43.60/6.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_0,c_235]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_2,plain,
% 43.60/6.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 43.60/6.01      inference(cnf_transformation,[],[f24]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_236,plain,
% 43.60/6.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 43.60/6.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_1896,plain,
% 43.60/6.01      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_718,c_236]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_3,plain,
% 43.60/6.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 43.60/6.01      inference(cnf_transformation,[],[f25]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_716,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_5,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 43.60/6.01      inference(cnf_transformation,[],[f37]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_240,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.60/6.01      inference(light_normalisation,[status(thm)],[c_5,c_3]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_733,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 43.60/6.01      inference(light_normalisation,[status(thm)],[c_716,c_3,c_240]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_961,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_733,c_0]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_981,plain,
% 43.60/6.01      ( k3_xboole_0(X0,X0) = X0 ),
% 43.60/6.01      inference(light_normalisation,[status(thm)],[c_961,c_3,c_240]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_6,plain,
% 43.60/6.01      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
% 43.60/6.01      inference(cnf_transformation,[],[f38]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_1108,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_981,c_6]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_161405,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X0) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_1896,c_1108]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_717,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_8,plain,
% 43.60/6.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 43.60/6.01      inference(cnf_transformation,[],[f31]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_965,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_733,c_8]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_1125,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 43.60/6.01      inference(light_normalisation,[status(thm)],[c_965,c_981]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_125045,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_717,c_1125]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_125516,plain,
% 43.60/6.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 43.60/6.01      inference(light_normalisation,[status(thm)],[c_125045,c_0]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_715,plain,
% 43.60/6.01      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2))))) = k3_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_125684,plain,
% 43.60/6.01      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)))) = k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_125516,c_715]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_125710,plain,
% 43.60/6.01      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 43.60/6.01      inference(light_normalisation,[status(thm)],[c_125684,c_0,c_240]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_161427,plain,
% 43.60/6.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 43.60/6.01      inference(light_normalisation,[status(thm)],[c_161405,c_125710]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_984,plain,
% 43.60/6.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 43.60/6.01      inference(demodulation,[status(thm)],[c_981,c_733]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_161428,plain,
% 43.60/6.01      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = X0 ),
% 43.60/6.01      inference(demodulation,[status(thm)],[c_161427,c_3,c_240,c_984]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_11,negated_conjecture,
% 43.60/6.01      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 43.60/6.01      inference(cnf_transformation,[],[f40]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_234,plain,
% 43.60/6.01      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 43.60/6.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_1894,plain,
% 43.60/6.01      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_234,c_236]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_846,plain,
% 43.60/6.01      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X3)))) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_79500,plain,
% 43.60/6.01      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k3_xboole_0(X0,sK2)))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_1894,c_846]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_81836,plain,
% 43.60/6.01      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),sK2))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK0) ),
% 43.60/6.01      inference(superposition,[status(thm)],[c_981,c_79500]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_161703,plain,
% 43.60/6.01      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 43.60/6.01      inference(demodulation,[status(thm)],[c_161428,c_81836]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_161705,plain,
% 43.60/6.01      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = sK0 ),
% 43.60/6.01      inference(demodulation,[status(thm)],[c_161703,c_161428]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_416,plain,
% 43.60/6.01      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 43.60/6.01      inference(instantiation,[status(thm)],[c_4]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_1,plain,
% 43.60/6.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 43.60/6.01      inference(cnf_transformation,[],[f23]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_281,plain,
% 43.60/6.01      ( r1_tarski(X0,X1)
% 43.60/6.01      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 43.60/6.01      | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
% 43.60/6.01      inference(instantiation,[status(thm)],[c_1]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_350,plain,
% 43.60/6.01      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
% 43.60/6.01      | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
% 43.60/6.01      | r1_tarski(sK0,sK1) ),
% 43.60/6.01      inference(instantiation,[status(thm)],[c_281]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_7,plain,
% 43.60/6.01      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 43.60/6.01      inference(cnf_transformation,[],[f39]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_10,negated_conjecture,
% 43.60/6.01      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 43.60/6.01      inference(cnf_transformation,[],[f34]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_81,plain,
% 43.60/6.01      ( ~ r1_tarski(sK0,sK1)
% 43.60/6.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
% 43.60/6.01      | sK2 != X1
% 43.60/6.01      | sK0 != X0 ),
% 43.60/6.01      inference(resolution_lifted,[status(thm)],[c_7,c_10]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(c_82,plain,
% 43.60/6.01      ( ~ r1_tarski(sK0,sK1)
% 43.60/6.01      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != sK0 ),
% 43.60/6.01      inference(unflattening,[status(thm)],[c_81]) ).
% 43.60/6.01  
% 43.60/6.01  cnf(contradiction,plain,
% 43.60/6.01      ( $false ),
% 43.60/6.01      inference(minisat,[status(thm)],[c_161705,c_416,c_350,c_82,c_11]) ).
% 43.60/6.01  
% 43.60/6.01  
% 43.60/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.60/6.01  
% 43.60/6.01  ------                               Statistics
% 43.60/6.01  
% 43.60/6.01  ------ General
% 43.60/6.01  
% 43.60/6.01  abstr_ref_over_cycles:                  0
% 43.60/6.01  abstr_ref_under_cycles:                 0
% 43.60/6.01  gc_basic_clause_elim:                   0
% 43.60/6.01  forced_gc_time:                         0
% 43.60/6.01  parsing_time:                           0.011
% 43.60/6.01  unif_index_cands_time:                  0.
% 43.60/6.01  unif_index_add_time:                    0.
% 43.60/6.01  orderings_time:                         0.
% 43.60/6.01  out_proof_time:                         0.014
% 43.60/6.01  total_time:                             5.333
% 43.60/6.01  num_of_symbols:                         40
% 43.60/6.01  num_of_terms:                           209490
% 43.60/6.01  
% 43.60/6.01  ------ Preprocessing
% 43.60/6.01  
% 43.60/6.01  num_of_splits:                          0
% 43.60/6.01  num_of_split_atoms:                     0
% 43.60/6.01  num_of_reused_defs:                     0
% 43.60/6.01  num_eq_ax_congr_red:                    0
% 43.60/6.01  num_of_sem_filtered_clauses:            1
% 43.60/6.01  num_of_subtypes:                        0
% 43.60/6.01  monotx_restored_types:                  0
% 43.60/6.01  sat_num_of_epr_types:                   0
% 43.60/6.01  sat_num_of_non_cyclic_types:            0
% 43.60/6.01  sat_guarded_non_collapsed_types:        0
% 43.60/6.01  num_pure_diseq_elim:                    0
% 43.60/6.01  simp_replaced_by:                       0
% 43.60/6.01  res_preprocessed:                       58
% 43.60/6.01  prep_upred:                             0
% 43.60/6.01  prep_unflattend:                        2
% 43.60/6.01  smt_new_axioms:                         0
% 43.60/6.01  pred_elim_cands:                        1
% 43.60/6.01  pred_elim:                              1
% 43.60/6.01  pred_elim_cl:                           1
% 43.60/6.01  pred_elim_cycles:                       3
% 43.60/6.01  merged_defs:                            0
% 43.60/6.01  merged_defs_ncl:                        0
% 43.60/6.01  bin_hyper_res:                          0
% 43.60/6.01  prep_cycles:                            4
% 43.60/6.01  pred_elim_time:                         0.
% 43.60/6.01  splitting_time:                         0.
% 43.60/6.01  sem_filter_time:                        0.
% 43.60/6.01  monotx_time:                            0.
% 43.60/6.01  subtype_inf_time:                       0.
% 43.60/6.01  
% 43.60/6.01  ------ Problem properties
% 43.60/6.01  
% 43.60/6.01  clauses:                                11
% 43.60/6.01  conjectures:                            1
% 43.60/6.01  epr:                                    1
% 43.60/6.01  horn:                                   11
% 43.60/6.01  ground:                                 2
% 43.60/6.01  unary:                                  8
% 43.60/6.01  binary:                                 2
% 43.60/6.01  lits:                                   15
% 43.60/6.01  lits_eq:                                8
% 43.60/6.01  fd_pure:                                0
% 43.60/6.01  fd_pseudo:                              0
% 43.60/6.01  fd_cond:                                0
% 43.60/6.01  fd_pseudo_cond:                         0
% 43.60/6.01  ac_symbols:                             0
% 43.60/6.01  
% 43.60/6.01  ------ Propositional Solver
% 43.60/6.01  
% 43.60/6.01  prop_solver_calls:                      44
% 43.60/6.01  prop_fast_solver_calls:                 705
% 43.60/6.01  smt_solver_calls:                       0
% 43.60/6.01  smt_fast_solver_calls:                  0
% 43.60/6.01  prop_num_of_clauses:                    43020
% 43.60/6.01  prop_preprocess_simplified:             46436
% 43.60/6.01  prop_fo_subsumed:                       6
% 43.60/6.01  prop_solver_time:                       0.
% 43.60/6.01  smt_solver_time:                        0.
% 43.60/6.01  smt_fast_solver_time:                   0.
% 43.60/6.01  prop_fast_solver_time:                  0.
% 43.60/6.01  prop_unsat_core_time:                   0.005
% 43.60/6.01  
% 43.60/6.01  ------ QBF
% 43.60/6.01  
% 43.60/6.01  qbf_q_res:                              0
% 43.60/6.01  qbf_num_tautologies:                    0
% 43.60/6.01  qbf_prep_cycles:                        0
% 43.60/6.01  
% 43.60/6.01  ------ BMC1
% 43.60/6.01  
% 43.60/6.01  bmc1_current_bound:                     -1
% 43.60/6.01  bmc1_last_solved_bound:                 -1
% 43.60/6.01  bmc1_unsat_core_size:                   -1
% 43.60/6.01  bmc1_unsat_core_parents_size:           -1
% 43.60/6.01  bmc1_merge_next_fun:                    0
% 43.60/6.01  bmc1_unsat_core_clauses_time:           0.
% 43.60/6.01  
% 43.60/6.01  ------ Instantiation
% 43.60/6.01  
% 43.60/6.01  inst_num_of_clauses:                    6753
% 43.60/6.01  inst_num_in_passive:                    5040
% 43.60/6.01  inst_num_in_active:                     1406
% 43.60/6.01  inst_num_in_unprocessed:                308
% 43.60/6.01  inst_num_of_loops:                      2150
% 43.60/6.01  inst_num_of_learning_restarts:          0
% 43.60/6.01  inst_num_moves_active_passive:          741
% 43.60/6.01  inst_lit_activity:                      0
% 43.60/6.01  inst_lit_activity_moves:                2
% 43.60/6.01  inst_num_tautologies:                   0
% 43.60/6.01  inst_num_prop_implied:                  0
% 43.60/6.01  inst_num_existing_simplified:           0
% 43.60/6.01  inst_num_eq_res_simplified:             0
% 43.60/6.01  inst_num_child_elim:                    0
% 43.60/6.01  inst_num_of_dismatching_blockings:      9926
% 43.60/6.01  inst_num_of_non_proper_insts:           9412
% 43.60/6.01  inst_num_of_duplicates:                 0
% 43.60/6.01  inst_inst_num_from_inst_to_res:         0
% 43.60/6.01  inst_dismatching_checking_time:         0.
% 43.60/6.01  
% 43.60/6.01  ------ Resolution
% 43.60/6.01  
% 43.60/6.01  res_num_of_clauses:                     0
% 43.60/6.01  res_num_in_passive:                     0
% 43.60/6.01  res_num_in_active:                      0
% 43.60/6.01  res_num_of_loops:                       62
% 43.60/6.01  res_forward_subset_subsumed:            1279
% 43.60/6.01  res_backward_subset_subsumed:           8
% 43.60/6.01  res_forward_subsumed:                   0
% 43.60/6.01  res_backward_subsumed:                  0
% 43.60/6.01  res_forward_subsumption_resolution:     0
% 43.60/6.01  res_backward_subsumption_resolution:    0
% 43.60/6.01  res_clause_to_clause_subsumption:       63979
% 43.60/6.01  res_orphan_elimination:                 0
% 43.60/6.01  res_tautology_del:                      553
% 43.60/6.01  res_num_eq_res_simplified:              0
% 43.60/6.01  res_num_sel_changes:                    0
% 43.60/6.01  res_moves_from_active_to_pass:          0
% 43.60/6.01  
% 43.60/6.01  ------ Superposition
% 43.60/6.01  
% 43.60/6.01  sup_time_total:                         0.
% 43.60/6.01  sup_time_generating:                    0.
% 43.60/6.01  sup_time_sim_full:                      0.
% 43.60/6.01  sup_time_sim_immed:                     0.
% 43.60/6.01  
% 43.60/6.01  sup_num_of_clauses:                     10350
% 43.60/6.01  sup_num_in_active:                      188
% 43.60/6.01  sup_num_in_passive:                     10162
% 43.60/6.01  sup_num_of_loops:                       429
% 43.60/6.01  sup_fw_superposition:                   14022
% 43.60/6.01  sup_bw_superposition:                   13637
% 43.60/6.01  sup_immediate_simplified:               17851
% 43.60/6.01  sup_given_eliminated:                   56
% 43.60/6.01  comparisons_done:                       0
% 43.60/6.01  comparisons_avoided:                    0
% 43.60/6.01  
% 43.60/6.01  ------ Simplifications
% 43.60/6.01  
% 43.60/6.01  
% 43.60/6.01  sim_fw_subset_subsumed:                 52
% 43.60/6.01  sim_bw_subset_subsumed:                 13
% 43.60/6.01  sim_fw_subsumed:                        2952
% 43.60/6.01  sim_bw_subsumed:                        688
% 43.60/6.01  sim_fw_subsumption_res:                 0
% 43.60/6.01  sim_bw_subsumption_res:                 1
% 43.60/6.01  sim_tautology_del:                      5
% 43.60/6.01  sim_eq_tautology_del:                   2472
% 43.60/6.01  sim_eq_res_simp:                        0
% 43.60/6.01  sim_fw_demodulated:                     10398
% 43.60/6.01  sim_bw_demodulated:                     1374
% 43.60/6.01  sim_light_normalised:                   8326
% 43.60/6.01  sim_joinable_taut:                      0
% 43.60/6.01  sim_joinable_simp:                      0
% 43.60/6.01  sim_ac_normalised:                      0
% 43.60/6.01  sim_smt_subsumption:                    0
% 43.60/6.01  
%------------------------------------------------------------------------------
