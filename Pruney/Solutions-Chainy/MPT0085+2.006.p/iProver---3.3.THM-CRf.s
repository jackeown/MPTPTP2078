%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:21 EST 2020

% Result     : Theorem 11.87s
% Output     : CNFRefutation 11.87s
% Verified   : 
% Statistics : Number of formulae       :  169 (9736 expanded)
%              Number of clauses        :  141 (4239 expanded)
%              Number of leaves         :   12 (2075 expanded)
%              Depth                    :   39
%              Number of atoms          :  241 (16213 expanded)
%              Number of equality atoms :  210 (10219 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   13 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f25,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f26,f23,f23])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_98,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_99,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_98])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_55,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_104,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k2_xboole_0(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_55,c_4])).

cnf(c_351,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_99,c_104])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_113,plain,
    ( X0 != X1
    | k2_xboole_0(X0,X2) != X3
    | k2_xboole_0(X1,X3) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_114,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_113])).

cnf(c_291,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_114])).

cnf(c_298,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_114,c_291])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_57,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_119,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) = k1_xboole_0
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_57,c_6])).

cnf(c_120,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_119])).

cnf(c_240,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_120])).

cnf(c_294,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_114,c_240])).

cnf(c_786,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_294,c_104])).

cnf(c_1460,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_298,c_786])).

cnf(c_1464,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1460])).

cnf(c_1618,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1464,c_1460])).

cnf(c_1634,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1618,c_1464])).

cnf(c_52909,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[status(thm)],[c_351,c_1634])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_353,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_240,c_104])).

cnf(c_359,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_240,c_5])).

cnf(c_358,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_120,c_5])).

cnf(c_446,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_358,c_240])).

cnf(c_489,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_359,c_446])).

cnf(c_491,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_489])).

cnf(c_357,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_99,c_5])).

cnf(c_804,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_491,c_357])).

cnf(c_980,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)) = k2_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_804,c_104])).

cnf(c_362,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_120])).

cnf(c_1694,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_980,c_362])).

cnf(c_1867,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1694,c_5])).

cnf(c_1868,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1867,c_5])).

cnf(c_7221,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK0,k1_xboole_0)),sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_353,c_1868])).

cnf(c_424,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_357,c_240])).

cnf(c_577,plain,
    ( k2_xboole_0(k1_xboole_0,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_424,c_104])).

cnf(c_1471,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_577,c_1460])).

cnf(c_1492,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1471,c_577])).

cnf(c_7291,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK0),sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7221,c_1492])).

cnf(c_10471,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sK0)),sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_7291])).

cnf(c_361,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0
    | k2_xboole_0(k4_xboole_0(X0,X1),X2) = X2 ),
    inference(superposition,[status(thm)],[c_5,c_104])).

cnf(c_30682,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,sK0))),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_10471,c_361])).

cnf(c_30692,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,sK0)))),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_30682,c_5])).

cnf(c_418,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_357])).

cnf(c_643,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_418,c_418,c_446])).

cnf(c_5254,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_643,c_361])).

cnf(c_1862,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_1694])).

cnf(c_7110,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),k2_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_294,c_1862])).

cnf(c_7160,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7110,c_577])).

cnf(c_650,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(X0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_643,c_104])).

cnf(c_1963,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_650,c_362])).

cnf(c_8237,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7160,c_1963])).

cnf(c_651,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_643,c_357])).

cnf(c_657,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_651,c_104])).

cnf(c_8238,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8237,c_657])).

cnf(c_8521,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8238,c_5])).

cnf(c_10958,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5254,c_8521])).

cnf(c_5289,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK0,sK1)) != k1_xboole_0
    | k2_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_351,c_361])).

cnf(c_13533,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_10958,c_5289])).

cnf(c_13622,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13533,c_8521])).

cnf(c_15153,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_13622,c_5289])).

cnf(c_15243,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15153,c_8521])).

cnf(c_17977,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_15243,c_5289])).

cnf(c_18078,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17977,c_8521])).

cnf(c_21689,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_18078,c_5289])).

cnf(c_646,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_643])).

cnf(c_887,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_646,c_104])).

cnf(c_5172,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_887])).

cnf(c_22218,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0)) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_21689,c_5172])).

cnf(c_22239,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0)) = k4_xboole_0(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_22218,c_351])).

cnf(c_500,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_489,c_104])).

cnf(c_22342,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0)),X1) ),
    inference(superposition,[status(thm)],[c_22239,c_500])).

cnf(c_22384,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X1) ),
    inference(demodulation,[status(thm)],[c_22342,c_22239])).

cnf(c_22777,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X1),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_22384,c_0])).

cnf(c_798,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_291,c_491])).

cnf(c_41587,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X2),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22777,c_798])).

cnf(c_1948,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k2_xboole_0(X0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_0,c_650])).

cnf(c_360,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_364,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_360,c_5])).

cnf(c_7783,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(sK0,sK1)),X2)) ),
    inference(superposition,[status(thm)],[c_1948,c_364])).

cnf(c_886,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_646,c_5])).

cnf(c_422,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_357,c_5])).

cnf(c_425,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_422,c_5,c_364])).

cnf(c_888,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_886,c_425,c_446])).

cnf(c_1891,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1) ),
    inference(superposition,[status(thm)],[c_888,c_104])).

cnf(c_6684,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X4))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))) ),
    inference(superposition,[status(thm)],[c_364,c_5])).

cnf(c_6718,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))) ),
    inference(demodulation,[status(thm)],[c_6684,c_5])).

cnf(c_7812,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK0,sK1),X2))) ),
    inference(demodulation,[status(thm)],[c_7783,c_364,c_1891,c_6718])).

cnf(c_520,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[status(thm)],[c_351,c_291])).

cnf(c_521,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_351,c_240])).

cnf(c_582,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_521,c_104])).

cnf(c_698,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_520,c_582])).

cnf(c_6665,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,X1))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) ),
    inference(superposition,[status(thm)],[c_698,c_364])).

cnf(c_443,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3) ),
    inference(superposition,[status(thm)],[c_358,c_5])).

cnf(c_506,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_443,c_5,c_364,c_446])).

cnf(c_2093,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X2),X3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_506])).

cnf(c_2333,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1492,c_2093])).

cnf(c_5275,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(sK0,X1)) = k2_xboole_0(sK0,X1) ),
    inference(superposition,[status(thm)],[c_2333,c_361])).

cnf(c_6736,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) = k4_xboole_0(X0,k2_xboole_0(sK0,X1)) ),
    inference(demodulation,[status(thm)],[c_6665,c_5275])).

cnf(c_7813,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK0,sK1),X2))) = k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_7812,c_6736])).

cnf(c_41780,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK0,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_41587,c_491,c_7813,c_22384])).

cnf(c_43727,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK0),k2_xboole_0(sK0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30692,c_41780])).

cnf(c_990,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_577,c_240])).

cnf(c_1458,plain,
    ( k2_xboole_0(sK0,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_990,c_104])).

cnf(c_43774,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_43727,c_698,c_1458])).

cnf(c_44263,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_43774,c_104])).

cnf(c_53166,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_52909,c_351,c_44263])).

cnf(c_136,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_341,plain,
    ( X0 != sK2
    | X1 != sK0
    | k4_xboole_0(X1,X0) = k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_484,plain,
    ( X0 != sK0
    | k4_xboole_0(X0,sK2) = k4_xboole_0(sK0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_3457,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,sK1) != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_134,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_152,plain,
    ( X0 != X1
    | k4_xboole_0(sK0,sK2) != X1
    | k4_xboole_0(sK0,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_178,plain,
    ( X0 != k4_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,sK2) = X0
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_229,plain,
    ( k4_xboole_0(X0,X1) != k4_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(X0,X1)
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_616,plain,
    ( k4_xboole_0(X0,sK2) != k4_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(X0,sK2)
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_1787,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_1644,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_142,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X0
    | k4_xboole_0(sK0,sK2) != X0
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_153,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_328,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(X0,sK2)
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(X0,sK2)
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_1421,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_378,plain,
    ( k4_xboole_0(X0,sK2) != X1
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_550,plain,
    ( k4_xboole_0(X0,sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(X0,sK2)
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_973,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_133,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_717,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_218,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_167,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_141,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_138,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_7,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53166,c_3457,c_1787,c_1644,c_1421,c_973,c_717,c_218,c_167,c_141,c_138,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.87/2.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.87/2.02  
% 11.87/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.87/2.02  
% 11.87/2.02  ------  iProver source info
% 11.87/2.02  
% 11.87/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.87/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.87/2.02  git: non_committed_changes: false
% 11.87/2.02  git: last_make_outside_of_git: false
% 11.87/2.02  
% 11.87/2.02  ------ 
% 11.87/2.02  
% 11.87/2.02  ------ Input Options
% 11.87/2.02  
% 11.87/2.02  --out_options                           all
% 11.87/2.02  --tptp_safe_out                         true
% 11.87/2.02  --problem_path                          ""
% 11.87/2.02  --include_path                          ""
% 11.87/2.02  --clausifier                            res/vclausify_rel
% 11.87/2.02  --clausifier_options                    ""
% 11.87/2.02  --stdin                                 false
% 11.87/2.02  --stats_out                             all
% 11.87/2.02  
% 11.87/2.02  ------ General Options
% 11.87/2.02  
% 11.87/2.02  --fof                                   false
% 11.87/2.02  --time_out_real                         305.
% 11.87/2.02  --time_out_virtual                      -1.
% 11.87/2.02  --symbol_type_check                     false
% 11.87/2.02  --clausify_out                          false
% 11.87/2.02  --sig_cnt_out                           false
% 11.87/2.02  --trig_cnt_out                          false
% 11.87/2.02  --trig_cnt_out_tolerance                1.
% 11.87/2.02  --trig_cnt_out_sk_spl                   false
% 11.87/2.02  --abstr_cl_out                          false
% 11.87/2.02  
% 11.87/2.02  ------ Global Options
% 11.87/2.02  
% 11.87/2.02  --schedule                              default
% 11.87/2.02  --add_important_lit                     false
% 11.87/2.02  --prop_solver_per_cl                    1000
% 11.87/2.02  --min_unsat_core                        false
% 11.87/2.02  --soft_assumptions                      false
% 11.87/2.02  --soft_lemma_size                       3
% 11.87/2.02  --prop_impl_unit_size                   0
% 11.87/2.02  --prop_impl_unit                        []
% 11.87/2.02  --share_sel_clauses                     true
% 11.87/2.02  --reset_solvers                         false
% 11.87/2.02  --bc_imp_inh                            [conj_cone]
% 11.87/2.02  --conj_cone_tolerance                   3.
% 11.87/2.02  --extra_neg_conj                        none
% 11.87/2.02  --large_theory_mode                     true
% 11.87/2.02  --prolific_symb_bound                   200
% 11.87/2.02  --lt_threshold                          2000
% 11.87/2.02  --clause_weak_htbl                      true
% 11.87/2.02  --gc_record_bc_elim                     false
% 11.87/2.02  
% 11.87/2.02  ------ Preprocessing Options
% 11.87/2.02  
% 11.87/2.02  --preprocessing_flag                    true
% 11.87/2.02  --time_out_prep_mult                    0.1
% 11.87/2.02  --splitting_mode                        input
% 11.87/2.02  --splitting_grd                         true
% 11.87/2.02  --splitting_cvd                         false
% 11.87/2.02  --splitting_cvd_svl                     false
% 11.87/2.02  --splitting_nvd                         32
% 11.87/2.02  --sub_typing                            true
% 11.87/2.02  --prep_gs_sim                           true
% 11.87/2.02  --prep_unflatten                        true
% 11.87/2.02  --prep_res_sim                          true
% 11.87/2.02  --prep_upred                            true
% 11.87/2.02  --prep_sem_filter                       exhaustive
% 11.87/2.02  --prep_sem_filter_out                   false
% 11.87/2.02  --pred_elim                             true
% 11.87/2.02  --res_sim_input                         true
% 11.87/2.02  --eq_ax_congr_red                       true
% 11.87/2.02  --pure_diseq_elim                       true
% 11.87/2.02  --brand_transform                       false
% 11.87/2.02  --non_eq_to_eq                          false
% 11.87/2.02  --prep_def_merge                        true
% 11.87/2.02  --prep_def_merge_prop_impl              false
% 11.87/2.02  --prep_def_merge_mbd                    true
% 11.87/2.02  --prep_def_merge_tr_red                 false
% 11.87/2.02  --prep_def_merge_tr_cl                  false
% 11.87/2.02  --smt_preprocessing                     true
% 11.87/2.02  --smt_ac_axioms                         fast
% 11.87/2.02  --preprocessed_out                      false
% 11.87/2.02  --preprocessed_stats                    false
% 11.87/2.02  
% 11.87/2.02  ------ Abstraction refinement Options
% 11.87/2.02  
% 11.87/2.02  --abstr_ref                             []
% 11.87/2.02  --abstr_ref_prep                        false
% 11.87/2.02  --abstr_ref_until_sat                   false
% 11.87/2.02  --abstr_ref_sig_restrict                funpre
% 11.87/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.87/2.02  --abstr_ref_under                       []
% 11.87/2.02  
% 11.87/2.02  ------ SAT Options
% 11.87/2.02  
% 11.87/2.02  --sat_mode                              false
% 11.87/2.02  --sat_fm_restart_options                ""
% 11.87/2.02  --sat_gr_def                            false
% 11.87/2.02  --sat_epr_types                         true
% 11.87/2.02  --sat_non_cyclic_types                  false
% 11.87/2.02  --sat_finite_models                     false
% 11.87/2.02  --sat_fm_lemmas                         false
% 11.87/2.02  --sat_fm_prep                           false
% 11.87/2.02  --sat_fm_uc_incr                        true
% 11.87/2.02  --sat_out_model                         small
% 11.87/2.02  --sat_out_clauses                       false
% 11.87/2.02  
% 11.87/2.02  ------ QBF Options
% 11.87/2.02  
% 11.87/2.02  --qbf_mode                              false
% 11.87/2.02  --qbf_elim_univ                         false
% 11.87/2.02  --qbf_dom_inst                          none
% 11.87/2.02  --qbf_dom_pre_inst                      false
% 11.87/2.02  --qbf_sk_in                             false
% 11.87/2.02  --qbf_pred_elim                         true
% 11.87/2.02  --qbf_split                             512
% 11.87/2.02  
% 11.87/2.02  ------ BMC1 Options
% 11.87/2.02  
% 11.87/2.02  --bmc1_incremental                      false
% 11.87/2.02  --bmc1_axioms                           reachable_all
% 11.87/2.02  --bmc1_min_bound                        0
% 11.87/2.02  --bmc1_max_bound                        -1
% 11.87/2.02  --bmc1_max_bound_default                -1
% 11.87/2.02  --bmc1_symbol_reachability              true
% 11.87/2.02  --bmc1_property_lemmas                  false
% 11.87/2.02  --bmc1_k_induction                      false
% 11.87/2.02  --bmc1_non_equiv_states                 false
% 11.87/2.02  --bmc1_deadlock                         false
% 11.87/2.02  --bmc1_ucm                              false
% 11.87/2.02  --bmc1_add_unsat_core                   none
% 11.87/2.02  --bmc1_unsat_core_children              false
% 11.87/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.87/2.02  --bmc1_out_stat                         full
% 11.87/2.02  --bmc1_ground_init                      false
% 11.87/2.02  --bmc1_pre_inst_next_state              false
% 11.87/2.02  --bmc1_pre_inst_state                   false
% 11.87/2.02  --bmc1_pre_inst_reach_state             false
% 11.87/2.02  --bmc1_out_unsat_core                   false
% 11.87/2.02  --bmc1_aig_witness_out                  false
% 11.87/2.02  --bmc1_verbose                          false
% 11.87/2.02  --bmc1_dump_clauses_tptp                false
% 11.87/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.87/2.02  --bmc1_dump_file                        -
% 11.87/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.87/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.87/2.02  --bmc1_ucm_extend_mode                  1
% 11.87/2.02  --bmc1_ucm_init_mode                    2
% 11.87/2.02  --bmc1_ucm_cone_mode                    none
% 11.87/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.87/2.02  --bmc1_ucm_relax_model                  4
% 11.87/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.87/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.87/2.02  --bmc1_ucm_layered_model                none
% 11.87/2.02  --bmc1_ucm_max_lemma_size               10
% 11.87/2.02  
% 11.87/2.02  ------ AIG Options
% 11.87/2.02  
% 11.87/2.02  --aig_mode                              false
% 11.87/2.02  
% 11.87/2.02  ------ Instantiation Options
% 11.87/2.02  
% 11.87/2.02  --instantiation_flag                    true
% 11.87/2.02  --inst_sos_flag                         true
% 11.87/2.02  --inst_sos_phase                        true
% 11.87/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.87/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.87/2.02  --inst_lit_sel_side                     num_symb
% 11.87/2.02  --inst_solver_per_active                1400
% 11.87/2.02  --inst_solver_calls_frac                1.
% 11.87/2.02  --inst_passive_queue_type               priority_queues
% 11.87/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.87/2.02  --inst_passive_queues_freq              [25;2]
% 11.87/2.02  --inst_dismatching                      true
% 11.87/2.02  --inst_eager_unprocessed_to_passive     true
% 11.87/2.02  --inst_prop_sim_given                   true
% 11.87/2.02  --inst_prop_sim_new                     false
% 11.87/2.02  --inst_subs_new                         false
% 11.87/2.02  --inst_eq_res_simp                      false
% 11.87/2.02  --inst_subs_given                       false
% 11.87/2.02  --inst_orphan_elimination               true
% 11.87/2.02  --inst_learning_loop_flag               true
% 11.87/2.02  --inst_learning_start                   3000
% 11.87/2.02  --inst_learning_factor                  2
% 11.87/2.02  --inst_start_prop_sim_after_learn       3
% 11.87/2.02  --inst_sel_renew                        solver
% 11.87/2.02  --inst_lit_activity_flag                true
% 11.87/2.02  --inst_restr_to_given                   false
% 11.87/2.02  --inst_activity_threshold               500
% 11.87/2.02  --inst_out_proof                        true
% 11.87/2.02  
% 11.87/2.02  ------ Resolution Options
% 11.87/2.02  
% 11.87/2.02  --resolution_flag                       true
% 11.87/2.02  --res_lit_sel                           adaptive
% 11.87/2.02  --res_lit_sel_side                      none
% 11.87/2.02  --res_ordering                          kbo
% 11.87/2.02  --res_to_prop_solver                    active
% 11.87/2.02  --res_prop_simpl_new                    false
% 11.87/2.02  --res_prop_simpl_given                  true
% 11.87/2.02  --res_passive_queue_type                priority_queues
% 11.87/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.87/2.02  --res_passive_queues_freq               [15;5]
% 11.87/2.02  --res_forward_subs                      full
% 11.87/2.02  --res_backward_subs                     full
% 11.87/2.02  --res_forward_subs_resolution           true
% 11.87/2.02  --res_backward_subs_resolution          true
% 11.87/2.02  --res_orphan_elimination                true
% 11.87/2.02  --res_time_limit                        2.
% 11.87/2.02  --res_out_proof                         true
% 11.87/2.02  
% 11.87/2.02  ------ Superposition Options
% 11.87/2.02  
% 11.87/2.02  --superposition_flag                    true
% 11.87/2.02  --sup_passive_queue_type                priority_queues
% 11.87/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.87/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.87/2.02  --demod_completeness_check              fast
% 11.87/2.02  --demod_use_ground                      true
% 11.87/2.02  --sup_to_prop_solver                    passive
% 11.87/2.02  --sup_prop_simpl_new                    true
% 11.87/2.02  --sup_prop_simpl_given                  true
% 11.87/2.02  --sup_fun_splitting                     true
% 11.87/2.02  --sup_smt_interval                      50000
% 11.87/2.02  
% 11.87/2.02  ------ Superposition Simplification Setup
% 11.87/2.02  
% 11.87/2.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.87/2.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.87/2.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.87/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.87/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.87/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.87/2.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.87/2.02  --sup_immed_triv                        [TrivRules]
% 11.87/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/2.02  --sup_immed_bw_main                     []
% 11.87/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.87/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.87/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/2.02  --sup_input_bw                          []
% 11.87/2.02  
% 11.87/2.02  ------ Combination Options
% 11.87/2.02  
% 11.87/2.02  --comb_res_mult                         3
% 11.87/2.02  --comb_sup_mult                         2
% 11.87/2.02  --comb_inst_mult                        10
% 11.87/2.02  
% 11.87/2.02  ------ Debug Options
% 11.87/2.02  
% 11.87/2.02  --dbg_backtrace                         false
% 11.87/2.02  --dbg_dump_prop_clauses                 false
% 11.87/2.02  --dbg_dump_prop_clauses_file            -
% 11.87/2.02  --dbg_out_stat                          false
% 11.87/2.02  ------ Parsing...
% 11.87/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.87/2.02  
% 11.87/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.87/2.02  
% 11.87/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.87/2.02  
% 11.87/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.87/2.02  ------ Proving...
% 11.87/2.02  ------ Problem Properties 
% 11.87/2.02  
% 11.87/2.02  
% 11.87/2.02  clauses                                 7
% 11.87/2.02  conjectures                             1
% 11.87/2.02  EPR                                     0
% 11.87/2.02  Horn                                    7
% 11.87/2.02  unary                                   6
% 11.87/2.02  binary                                  1
% 11.87/2.02  lits                                    8
% 11.87/2.02  lits eq                                 8
% 11.87/2.02  fd_pure                                 0
% 11.87/2.02  fd_pseudo                               0
% 11.87/2.02  fd_cond                                 0
% 11.87/2.02  fd_pseudo_cond                          0
% 11.87/2.02  AC symbols                              0
% 11.87/2.02  
% 11.87/2.02  ------ Schedule dynamic 5 is on 
% 11.87/2.02  
% 11.87/2.02  ------ pure equality problem: resolution off 
% 11.87/2.02  
% 11.87/2.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.87/2.02  
% 11.87/2.02  
% 11.87/2.02  ------ 
% 11.87/2.02  Current options:
% 11.87/2.02  ------ 
% 11.87/2.02  
% 11.87/2.02  ------ Input Options
% 11.87/2.02  
% 11.87/2.02  --out_options                           all
% 11.87/2.02  --tptp_safe_out                         true
% 11.87/2.02  --problem_path                          ""
% 11.87/2.02  --include_path                          ""
% 11.87/2.02  --clausifier                            res/vclausify_rel
% 11.87/2.02  --clausifier_options                    ""
% 11.87/2.02  --stdin                                 false
% 11.87/2.02  --stats_out                             all
% 11.87/2.02  
% 11.87/2.02  ------ General Options
% 11.87/2.02  
% 11.87/2.02  --fof                                   false
% 11.87/2.02  --time_out_real                         305.
% 11.87/2.02  --time_out_virtual                      -1.
% 11.87/2.02  --symbol_type_check                     false
% 11.87/2.02  --clausify_out                          false
% 11.87/2.02  --sig_cnt_out                           false
% 11.87/2.02  --trig_cnt_out                          false
% 11.87/2.02  --trig_cnt_out_tolerance                1.
% 11.87/2.02  --trig_cnt_out_sk_spl                   false
% 11.87/2.02  --abstr_cl_out                          false
% 11.87/2.02  
% 11.87/2.02  ------ Global Options
% 11.87/2.02  
% 11.87/2.02  --schedule                              default
% 11.87/2.02  --add_important_lit                     false
% 11.87/2.02  --prop_solver_per_cl                    1000
% 11.87/2.02  --min_unsat_core                        false
% 11.87/2.02  --soft_assumptions                      false
% 11.87/2.02  --soft_lemma_size                       3
% 11.87/2.02  --prop_impl_unit_size                   0
% 11.87/2.02  --prop_impl_unit                        []
% 11.87/2.02  --share_sel_clauses                     true
% 11.87/2.02  --reset_solvers                         false
% 11.87/2.02  --bc_imp_inh                            [conj_cone]
% 11.87/2.02  --conj_cone_tolerance                   3.
% 11.87/2.02  --extra_neg_conj                        none
% 11.87/2.02  --large_theory_mode                     true
% 11.87/2.02  --prolific_symb_bound                   200
% 11.87/2.02  --lt_threshold                          2000
% 11.87/2.02  --clause_weak_htbl                      true
% 11.87/2.02  --gc_record_bc_elim                     false
% 11.87/2.02  
% 11.87/2.02  ------ Preprocessing Options
% 11.87/2.02  
% 11.87/2.02  --preprocessing_flag                    true
% 11.87/2.02  --time_out_prep_mult                    0.1
% 11.87/2.02  --splitting_mode                        input
% 11.87/2.02  --splitting_grd                         true
% 11.87/2.02  --splitting_cvd                         false
% 11.87/2.02  --splitting_cvd_svl                     false
% 11.87/2.02  --splitting_nvd                         32
% 11.87/2.02  --sub_typing                            true
% 11.87/2.02  --prep_gs_sim                           true
% 11.87/2.02  --prep_unflatten                        true
% 11.87/2.02  --prep_res_sim                          true
% 11.87/2.02  --prep_upred                            true
% 11.87/2.02  --prep_sem_filter                       exhaustive
% 11.87/2.02  --prep_sem_filter_out                   false
% 11.87/2.02  --pred_elim                             true
% 11.87/2.02  --res_sim_input                         true
% 11.87/2.02  --eq_ax_congr_red                       true
% 11.87/2.02  --pure_diseq_elim                       true
% 11.87/2.02  --brand_transform                       false
% 11.87/2.02  --non_eq_to_eq                          false
% 11.87/2.02  --prep_def_merge                        true
% 11.87/2.02  --prep_def_merge_prop_impl              false
% 11.87/2.02  --prep_def_merge_mbd                    true
% 11.87/2.02  --prep_def_merge_tr_red                 false
% 11.87/2.02  --prep_def_merge_tr_cl                  false
% 11.87/2.02  --smt_preprocessing                     true
% 11.87/2.02  --smt_ac_axioms                         fast
% 11.87/2.02  --preprocessed_out                      false
% 11.87/2.02  --preprocessed_stats                    false
% 11.87/2.02  
% 11.87/2.02  ------ Abstraction refinement Options
% 11.87/2.02  
% 11.87/2.02  --abstr_ref                             []
% 11.87/2.02  --abstr_ref_prep                        false
% 11.87/2.02  --abstr_ref_until_sat                   false
% 11.87/2.02  --abstr_ref_sig_restrict                funpre
% 11.87/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.87/2.02  --abstr_ref_under                       []
% 11.87/2.02  
% 11.87/2.02  ------ SAT Options
% 11.87/2.02  
% 11.87/2.02  --sat_mode                              false
% 11.87/2.02  --sat_fm_restart_options                ""
% 11.87/2.02  --sat_gr_def                            false
% 11.87/2.02  --sat_epr_types                         true
% 11.87/2.02  --sat_non_cyclic_types                  false
% 11.87/2.02  --sat_finite_models                     false
% 11.87/2.02  --sat_fm_lemmas                         false
% 11.87/2.02  --sat_fm_prep                           false
% 11.87/2.02  --sat_fm_uc_incr                        true
% 11.87/2.02  --sat_out_model                         small
% 11.87/2.02  --sat_out_clauses                       false
% 11.87/2.02  
% 11.87/2.02  ------ QBF Options
% 11.87/2.02  
% 11.87/2.02  --qbf_mode                              false
% 11.87/2.02  --qbf_elim_univ                         false
% 11.87/2.02  --qbf_dom_inst                          none
% 11.87/2.02  --qbf_dom_pre_inst                      false
% 11.87/2.02  --qbf_sk_in                             false
% 11.87/2.02  --qbf_pred_elim                         true
% 11.87/2.02  --qbf_split                             512
% 11.87/2.02  
% 11.87/2.02  ------ BMC1 Options
% 11.87/2.02  
% 11.87/2.02  --bmc1_incremental                      false
% 11.87/2.02  --bmc1_axioms                           reachable_all
% 11.87/2.02  --bmc1_min_bound                        0
% 11.87/2.02  --bmc1_max_bound                        -1
% 11.87/2.02  --bmc1_max_bound_default                -1
% 11.87/2.02  --bmc1_symbol_reachability              true
% 11.87/2.02  --bmc1_property_lemmas                  false
% 11.87/2.02  --bmc1_k_induction                      false
% 11.87/2.02  --bmc1_non_equiv_states                 false
% 11.87/2.02  --bmc1_deadlock                         false
% 11.87/2.02  --bmc1_ucm                              false
% 11.87/2.02  --bmc1_add_unsat_core                   none
% 11.87/2.02  --bmc1_unsat_core_children              false
% 11.87/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.87/2.02  --bmc1_out_stat                         full
% 11.87/2.02  --bmc1_ground_init                      false
% 11.87/2.02  --bmc1_pre_inst_next_state              false
% 11.87/2.02  --bmc1_pre_inst_state                   false
% 11.87/2.02  --bmc1_pre_inst_reach_state             false
% 11.87/2.02  --bmc1_out_unsat_core                   false
% 11.87/2.02  --bmc1_aig_witness_out                  false
% 11.87/2.02  --bmc1_verbose                          false
% 11.87/2.02  --bmc1_dump_clauses_tptp                false
% 11.87/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.87/2.02  --bmc1_dump_file                        -
% 11.87/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.87/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.87/2.02  --bmc1_ucm_extend_mode                  1
% 11.87/2.02  --bmc1_ucm_init_mode                    2
% 11.87/2.02  --bmc1_ucm_cone_mode                    none
% 11.87/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.87/2.02  --bmc1_ucm_relax_model                  4
% 11.87/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.87/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.87/2.02  --bmc1_ucm_layered_model                none
% 11.87/2.02  --bmc1_ucm_max_lemma_size               10
% 11.87/2.02  
% 11.87/2.02  ------ AIG Options
% 11.87/2.02  
% 11.87/2.02  --aig_mode                              false
% 11.87/2.02  
% 11.87/2.02  ------ Instantiation Options
% 11.87/2.02  
% 11.87/2.02  --instantiation_flag                    true
% 11.87/2.02  --inst_sos_flag                         true
% 11.87/2.02  --inst_sos_phase                        true
% 11.87/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.87/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.87/2.02  --inst_lit_sel_side                     none
% 11.87/2.02  --inst_solver_per_active                1400
% 11.87/2.02  --inst_solver_calls_frac                1.
% 11.87/2.02  --inst_passive_queue_type               priority_queues
% 11.87/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.87/2.02  --inst_passive_queues_freq              [25;2]
% 11.87/2.02  --inst_dismatching                      true
% 11.87/2.02  --inst_eager_unprocessed_to_passive     true
% 11.87/2.02  --inst_prop_sim_given                   true
% 11.87/2.02  --inst_prop_sim_new                     false
% 11.87/2.02  --inst_subs_new                         false
% 11.87/2.02  --inst_eq_res_simp                      false
% 11.87/2.02  --inst_subs_given                       false
% 11.87/2.02  --inst_orphan_elimination               true
% 11.87/2.02  --inst_learning_loop_flag               true
% 11.87/2.02  --inst_learning_start                   3000
% 11.87/2.02  --inst_learning_factor                  2
% 11.87/2.02  --inst_start_prop_sim_after_learn       3
% 11.87/2.02  --inst_sel_renew                        solver
% 11.87/2.02  --inst_lit_activity_flag                true
% 11.87/2.02  --inst_restr_to_given                   false
% 11.87/2.02  --inst_activity_threshold               500
% 11.87/2.02  --inst_out_proof                        true
% 11.87/2.02  
% 11.87/2.02  ------ Resolution Options
% 11.87/2.02  
% 11.87/2.02  --resolution_flag                       false
% 11.87/2.02  --res_lit_sel                           adaptive
% 11.87/2.02  --res_lit_sel_side                      none
% 11.87/2.02  --res_ordering                          kbo
% 11.87/2.02  --res_to_prop_solver                    active
% 11.87/2.02  --res_prop_simpl_new                    false
% 11.87/2.02  --res_prop_simpl_given                  true
% 11.87/2.02  --res_passive_queue_type                priority_queues
% 11.87/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.87/2.02  --res_passive_queues_freq               [15;5]
% 11.87/2.02  --res_forward_subs                      full
% 11.87/2.02  --res_backward_subs                     full
% 11.87/2.02  --res_forward_subs_resolution           true
% 11.87/2.02  --res_backward_subs_resolution          true
% 11.87/2.02  --res_orphan_elimination                true
% 11.87/2.02  --res_time_limit                        2.
% 11.87/2.02  --res_out_proof                         true
% 11.87/2.02  
% 11.87/2.02  ------ Superposition Options
% 11.87/2.02  
% 11.87/2.02  --superposition_flag                    true
% 11.87/2.02  --sup_passive_queue_type                priority_queues
% 11.87/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.87/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.87/2.02  --demod_completeness_check              fast
% 11.87/2.02  --demod_use_ground                      true
% 11.87/2.02  --sup_to_prop_solver                    passive
% 11.87/2.02  --sup_prop_simpl_new                    true
% 11.87/2.02  --sup_prop_simpl_given                  true
% 11.87/2.02  --sup_fun_splitting                     true
% 11.87/2.02  --sup_smt_interval                      50000
% 11.87/2.02  
% 11.87/2.02  ------ Superposition Simplification Setup
% 11.87/2.02  
% 11.87/2.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.87/2.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.87/2.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.87/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.87/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.87/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.87/2.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.87/2.02  --sup_immed_triv                        [TrivRules]
% 11.87/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/2.02  --sup_immed_bw_main                     []
% 11.87/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.87/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.87/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/2.02  --sup_input_bw                          []
% 11.87/2.02  
% 11.87/2.02  ------ Combination Options
% 11.87/2.02  
% 11.87/2.02  --comb_res_mult                         3
% 11.87/2.02  --comb_sup_mult                         2
% 11.87/2.02  --comb_inst_mult                        10
% 11.87/2.02  
% 11.87/2.02  ------ Debug Options
% 11.87/2.02  
% 11.87/2.02  --dbg_backtrace                         false
% 11.87/2.02  --dbg_dump_prop_clauses                 false
% 11.87/2.02  --dbg_dump_prop_clauses_file            -
% 11.87/2.02  --dbg_out_stat                          false
% 11.87/2.02  
% 11.87/2.02  
% 11.87/2.02  
% 11.87/2.02  
% 11.87/2.02  ------ Proving...
% 11.87/2.02  
% 11.87/2.02  
% 11.87/2.02  % SZS status Theorem for theBenchmark.p
% 11.87/2.02  
% 11.87/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.87/2.02  
% 11.87/2.02  fof(f2,axiom,(
% 11.87/2.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.87/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.02  
% 11.87/2.02  fof(f10,plain,(
% 11.87/2.02    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.87/2.02    inference(unused_predicate_definition_removal,[],[f2])).
% 11.87/2.02  
% 11.87/2.02  fof(f11,plain,(
% 11.87/2.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 11.87/2.02    inference(ennf_transformation,[],[f10])).
% 11.87/2.02  
% 11.87/2.02  fof(f18,plain,(
% 11.87/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.87/2.02    inference(cnf_transformation,[],[f11])).
% 11.87/2.02  
% 11.87/2.02  fof(f6,axiom,(
% 11.87/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.87/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.02  
% 11.87/2.02  fof(f23,plain,(
% 11.87/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.87/2.02    inference(cnf_transformation,[],[f6])).
% 11.87/2.02  
% 11.87/2.02  fof(f27,plain,(
% 11.87/2.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.87/2.02    inference(definition_unfolding,[],[f18,f23])).
% 11.87/2.02  
% 11.87/2.02  fof(f8,conjecture,(
% 11.87/2.02    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 11.87/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.02  
% 11.87/2.02  fof(f9,negated_conjecture,(
% 11.87/2.02    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 11.87/2.02    inference(negated_conjecture,[],[f8])).
% 11.87/2.02  
% 11.87/2.02  fof(f13,plain,(
% 11.87/2.02    ? [X0,X1,X2] : (k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 11.87/2.02    inference(ennf_transformation,[],[f9])).
% 11.87/2.02  
% 11.87/2.02  fof(f15,plain,(
% 11.87/2.02    ? [X0,X1,X2] : (k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 11.87/2.02    introduced(choice_axiom,[])).
% 11.87/2.02  
% 11.87/2.02  fof(f16,plain,(
% 11.87/2.02    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 11.87/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 11.87/2.02  
% 11.87/2.02  fof(f25,plain,(
% 11.87/2.02    r1_xboole_0(sK0,sK1)),
% 11.87/2.02    inference(cnf_transformation,[],[f16])).
% 11.87/2.02  
% 11.87/2.02  fof(f3,axiom,(
% 11.87/2.02    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 11.87/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.02  
% 11.87/2.02  fof(f14,plain,(
% 11.87/2.02    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 11.87/2.02    inference(nnf_transformation,[],[f3])).
% 11.87/2.02  
% 11.87/2.02  fof(f19,plain,(
% 11.87/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 11.87/2.02    inference(cnf_transformation,[],[f14])).
% 11.87/2.02  
% 11.87/2.02  fof(f4,axiom,(
% 11.87/2.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.87/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.02  
% 11.87/2.02  fof(f12,plain,(
% 11.87/2.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.87/2.02    inference(ennf_transformation,[],[f4])).
% 11.87/2.02  
% 11.87/2.02  fof(f21,plain,(
% 11.87/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.87/2.02    inference(cnf_transformation,[],[f12])).
% 11.87/2.02  
% 11.87/2.02  fof(f1,axiom,(
% 11.87/2.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.87/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.02  
% 11.87/2.02  fof(f17,plain,(
% 11.87/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.87/2.02    inference(cnf_transformation,[],[f1])).
% 11.87/2.02  
% 11.87/2.02  fof(f7,axiom,(
% 11.87/2.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.87/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.02  
% 11.87/2.02  fof(f24,plain,(
% 11.87/2.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.87/2.02    inference(cnf_transformation,[],[f7])).
% 11.87/2.02  
% 11.87/2.02  fof(f20,plain,(
% 11.87/2.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 11.87/2.02    inference(cnf_transformation,[],[f14])).
% 11.87/2.02  
% 11.87/2.02  fof(f5,axiom,(
% 11.87/2.02    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.87/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.02  
% 11.87/2.02  fof(f22,plain,(
% 11.87/2.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.87/2.02    inference(cnf_transformation,[],[f5])).
% 11.87/2.02  
% 11.87/2.02  fof(f26,plain,(
% 11.87/2.02    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 11.87/2.02    inference(cnf_transformation,[],[f16])).
% 11.87/2.02  
% 11.87/2.02  fof(f28,plain,(
% 11.87/2.02    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 11.87/2.02    inference(definition_unfolding,[],[f26,f23,f23])).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1,plain,
% 11.87/2.02      ( ~ r1_xboole_0(X0,X1)
% 11.87/2.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.87/2.02      inference(cnf_transformation,[],[f27]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_8,negated_conjecture,
% 11.87/2.02      ( r1_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(cnf_transformation,[],[f25]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_98,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.87/2.02      | sK1 != X1
% 11.87/2.02      | sK0 != X0 ),
% 11.87/2.02      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_99,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 11.87/2.02      inference(unflattening,[status(thm)],[c_98]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_3,plain,
% 11.87/2.02      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.87/2.02      inference(cnf_transformation,[],[f19]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_55,plain,
% 11.87/2.02      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.87/2.02      inference(prop_impl,[status(thm)],[c_3]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_4,plain,
% 11.87/2.02      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.87/2.02      inference(cnf_transformation,[],[f21]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_104,plain,
% 11.87/2.02      ( k4_xboole_0(X0,X1) != k1_xboole_0 | k2_xboole_0(X0,X1) = X1 ),
% 11.87/2.02      inference(resolution,[status(thm)],[c_55,c_4]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_351,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_99,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_0,plain,
% 11.87/2.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.87/2.02      inference(cnf_transformation,[],[f17]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_6,plain,
% 11.87/2.02      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 11.87/2.02      inference(cnf_transformation,[],[f24]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_113,plain,
% 11.87/2.02      ( X0 != X1 | k2_xboole_0(X0,X2) != X3 | k2_xboole_0(X1,X3) = X3 ),
% 11.87/2.02      inference(resolution_lifted,[status(thm)],[c_4,c_6]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_114,plain,
% 11.87/2.02      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.87/2.02      inference(unflattening,[status(thm)],[c_113]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_291,plain,
% 11.87/2.02      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_114]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_298,plain,
% 11.87/2.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_114,c_291]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_2,plain,
% 11.87/2.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.87/2.02      inference(cnf_transformation,[],[f20]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_57,plain,
% 11.87/2.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.87/2.02      inference(prop_impl,[status(thm)],[c_2]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_119,plain,
% 11.87/2.02      ( X0 != X1
% 11.87/2.02      | k4_xboole_0(X1,X2) = k1_xboole_0
% 11.87/2.02      | k2_xboole_0(X0,X3) != X2 ),
% 11.87/2.02      inference(resolution_lifted,[status(thm)],[c_57,c_6]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_120,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.87/2.02      inference(unflattening,[status(thm)],[c_119]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_240,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_120]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_294,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_114,c_240]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_786,plain,
% 11.87/2.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_294,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1460,plain,
% 11.87/2.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_298,c_786]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1464,plain,
% 11.87/2.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_1460]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1618,plain,
% 11.87/2.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_1464,c_1460]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1634,plain,
% 11.87/2.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_1618,c_1464]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_52909,plain,
% 11.87/2.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_351,c_1634]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_5,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.87/2.02      inference(cnf_transformation,[],[f22]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_353,plain,
% 11.87/2.02      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_240,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_359,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_240,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_358,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_120,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_446,plain,
% 11.87/2.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_358,c_240]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_489,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_359,c_446]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_491,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_489]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_357,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_99,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_804,plain,
% 11.87/2.02      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_491,c_357]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_980,plain,
% 11.87/2.02      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)) = k2_xboole_0(X0,sK0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_804,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_362,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_5,c_120]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1694,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),sK0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_980,c_362]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1867,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),sK0))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_1694,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1868,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),sK0))) = k1_xboole_0 ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_1867,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_7221,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK0,k1_xboole_0)),sK0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_353,c_1868]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_424,plain,
% 11.87/2.02      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_357,c_240]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_577,plain,
% 11.87/2.02      ( k2_xboole_0(k1_xboole_0,sK0) = sK0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_424,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1471,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_577,c_1460]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1492,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_1471,c_577]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_7291,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK0),sK0)) = k1_xboole_0 ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_7221,c_1492]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_10471,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sK0)),sK0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_5,c_7291]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_361,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0
% 11.87/2.02      | k2_xboole_0(k4_xboole_0(X0,X1),X2) = X2 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_5,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_30682,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,sK0))),sK0) = sK0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_10471,c_361]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_30692,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,sK0)))),sK0) = sK0 ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_30682,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_418,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_357]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_643,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_418,c_418,c_446]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_5254,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_643,c_361]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1862,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),sK0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_5,c_1694]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_7110,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),k2_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_294,c_1862]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_7160,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),sK0) = k1_xboole_0 ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_7110,c_577]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_650,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(X0,k4_xboole_0(sK0,sK1)) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_643,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1963,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_650,c_362]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_8237,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_7160,c_1963]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_651,plain,
% 11.87/2.02      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_643,c_357]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_657,plain,
% 11.87/2.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_651,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_8238,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_8237,c_657]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_8521,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_8238,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_10958,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_5254,c_8521]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_5289,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k4_xboole_0(sK0,sK1)) != k1_xboole_0
% 11.87/2.02      | k2_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_351,c_361]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_13533,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_10958,c_5289]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_13622,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_13533,c_8521]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_15153,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_13622,c_5289]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_15243,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_15153,c_8521]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_17977,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_15243,c_5289]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_18078,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_17977,c_8521]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_21689,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_18078,c_5289]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_646,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_643]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_887,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_646,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_5172,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_887]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_22218,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0)) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_21689,c_5172]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_22239,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_22218,c_351]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_500,plain,
% 11.87/2.02      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_489,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_22342,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0)),X1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_22239,c_500]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_22384,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X1) ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_22342,c_22239]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_22777,plain,
% 11.87/2.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X1),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_22384,c_0]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_798,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_291,c_491]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_41587,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X2),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k1_xboole_0),sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),X0)))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_22777,c_798]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1948,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k2_xboole_0(X0,k4_xboole_0(sK0,sK1)) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_650]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_360,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_364,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_360,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_7783,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(sK0,sK1)),X2)) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_1948,c_364]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_886,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_646,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_422,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_357,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_425,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_422,c_5,c_364]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_888,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k1_xboole_0 ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_886,c_425,c_446]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1891,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_888,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_6684,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X4))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_364,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_6718,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))) ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_6684,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_7812,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK0,sK1),X2))) ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_7783,c_364,c_1891,c_6718]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_520,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_351,c_291]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_521,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_351,c_240]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_582,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_521,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_698,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,sK1) ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_520,c_582]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_6665,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,X1))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_698,c_364]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_443,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_358,c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_506,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k1_xboole_0 ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_443,c_5,c_364,c_446]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_2093,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X2),X3))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_0,c_506]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_2333,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK0,X1))) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_1492,c_2093]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_5275,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(sK0,X1)) = k2_xboole_0(sK0,X1) ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_2333,c_361]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_6736,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) = k4_xboole_0(X0,k2_xboole_0(sK0,X1)) ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_6665,c_5275]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_7813,plain,
% 11.87/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK0,sK1),X2))) = k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(X1,X2))) ),
% 11.87/2.02      inference(demodulation,[status(thm)],[c_7812,c_6736]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_41780,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK0,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.87/2.02      inference(demodulation,
% 11.87/2.02                [status(thm)],
% 11.87/2.02                [c_41587,c_491,c_7813,c_22384]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_43727,plain,
% 11.87/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK0),k2_xboole_0(sK0,sK0)) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_30692,c_41780]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_990,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_577,c_240]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1458,plain,
% 11.87/2.02      ( k2_xboole_0(sK0,sK0) = sK0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_990,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_43774,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0 ),
% 11.87/2.02      inference(light_normalisation,[status(thm)],[c_43727,c_698,c_1458]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_44263,plain,
% 11.87/2.02      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = sK0 ),
% 11.87/2.02      inference(superposition,[status(thm)],[c_43774,c_104]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_53166,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 11.87/2.02      inference(light_normalisation,
% 11.87/2.02                [status(thm)],
% 11.87/2.02                [c_52909,c_351,c_44263]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_136,plain,
% 11.87/2.02      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 11.87/2.02      theory(equality) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_341,plain,
% 11.87/2.02      ( X0 != sK2
% 11.87/2.02      | X1 != sK0
% 11.87/2.02      | k4_xboole_0(X1,X0) = k4_xboole_0(sK0,sK2) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_136]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_484,plain,
% 11.87/2.02      ( X0 != sK0
% 11.87/2.02      | k4_xboole_0(X0,sK2) = k4_xboole_0(sK0,sK2)
% 11.87/2.02      | sK2 != sK2 ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_341]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_3457,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK1) != sK0
% 11.87/2.02      | sK2 != sK2 ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_484]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_134,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_152,plain,
% 11.87/2.02      ( X0 != X1
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != X1
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = X0 ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_134]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_178,plain,
% 11.87/2.02      ( X0 != k4_xboole_0(sK0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = X0
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_152]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_229,plain,
% 11.87/2.02      ( k4_xboole_0(X0,X1) != k4_xboole_0(sK0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = k4_xboole_0(X0,X1)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_178]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_616,plain,
% 11.87/2.02      ( k4_xboole_0(X0,sK2) != k4_xboole_0(sK0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = k4_xboole_0(X0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_229]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1787,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_616]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1644,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_5]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_142,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X0
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != X0
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_134]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_153,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(X0,X1)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != k4_xboole_0(X0,X1)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_142]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_328,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(X0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != k4_xboole_0(X0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_153]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_1421,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 11.87/2.02      | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_328]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_378,plain,
% 11.87/2.02      ( k4_xboole_0(X0,sK2) != X1
% 11.87/2.02      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1
% 11.87/2.02      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(X0,sK2) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_134]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_550,plain,
% 11.87/2.02      ( k4_xboole_0(X0,sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 11.87/2.02      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(X0,sK2)
% 11.87/2.02      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_378]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_973,plain,
% 11.87/2.02      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 11.87/2.02      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 11.87/2.02      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_550]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_133,plain,( X0 = X0 ),theory(equality) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_717,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_133]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_218,plain,
% 11.87/2.02      ( sK2 = sK2 ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_133]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_167,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_133]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_141,plain,
% 11.87/2.02      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
% 11.87/2.02      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 11.87/2.02      | sK0 != sK0 ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_136]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_138,plain,
% 11.87/2.02      ( sK0 = sK0 ),
% 11.87/2.02      inference(instantiation,[status(thm)],[c_133]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(c_7,negated_conjecture,
% 11.87/2.02      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
% 11.87/2.02      inference(cnf_transformation,[],[f28]) ).
% 11.87/2.02  
% 11.87/2.02  cnf(contradiction,plain,
% 11.87/2.02      ( $false ),
% 11.87/2.02      inference(minisat,
% 11.87/2.02                [status(thm)],
% 11.87/2.02                [c_53166,c_3457,c_1787,c_1644,c_1421,c_973,c_717,c_218,
% 11.87/2.02                 c_167,c_141,c_138,c_7]) ).
% 11.87/2.02  
% 11.87/2.02  
% 11.87/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.87/2.02  
% 11.87/2.02  ------                               Statistics
% 11.87/2.02  
% 11.87/2.02  ------ General
% 11.87/2.02  
% 11.87/2.02  abstr_ref_over_cycles:                  0
% 11.87/2.02  abstr_ref_under_cycles:                 0
% 11.87/2.02  gc_basic_clause_elim:                   0
% 11.87/2.02  forced_gc_time:                         0
% 11.87/2.02  parsing_time:                           0.008
% 11.87/2.02  unif_index_cands_time:                  0.
% 11.87/2.02  unif_index_add_time:                    0.
% 11.87/2.02  orderings_time:                         0.
% 11.87/2.02  out_proof_time:                         0.01
% 11.87/2.02  total_time:                             1.381
% 11.87/2.02  num_of_symbols:                         39
% 11.87/2.02  num_of_terms:                           47525
% 11.87/2.02  
% 11.87/2.02  ------ Preprocessing
% 11.87/2.02  
% 11.87/2.02  num_of_splits:                          0
% 11.87/2.02  num_of_split_atoms:                     0
% 11.87/2.02  num_of_reused_defs:                     0
% 11.87/2.02  num_eq_ax_congr_red:                    1
% 11.87/2.02  num_of_sem_filtered_clauses:            0
% 11.87/2.02  num_of_subtypes:                        0
% 11.87/2.02  monotx_restored_types:                  0
% 11.87/2.02  sat_num_of_epr_types:                   0
% 11.87/2.02  sat_num_of_non_cyclic_types:            0
% 11.87/2.02  sat_guarded_non_collapsed_types:        0
% 11.87/2.02  num_pure_diseq_elim:                    0
% 11.87/2.02  simp_replaced_by:                       0
% 11.87/2.02  res_preprocessed:                       27
% 11.87/2.02  prep_upred:                             0
% 11.87/2.02  prep_unflattend:                        6
% 11.87/2.02  smt_new_axioms:                         0
% 11.87/2.02  pred_elim_cands:                        0
% 11.87/2.02  pred_elim:                              2
% 11.87/2.02  pred_elim_cl:                           2
% 11.87/2.02  pred_elim_cycles:                       3
% 11.87/2.02  merged_defs:                            2
% 11.87/2.02  merged_defs_ncl:                        0
% 11.87/2.02  bin_hyper_res:                          2
% 11.87/2.02  prep_cycles:                            3
% 11.87/2.02  pred_elim_time:                         0.
% 11.87/2.02  splitting_time:                         0.
% 11.87/2.02  sem_filter_time:                        0.
% 11.87/2.02  monotx_time:                            0.
% 11.87/2.02  subtype_inf_time:                       0.
% 11.87/2.02  
% 11.87/2.02  ------ Problem properties
% 11.87/2.02  
% 11.87/2.02  clauses:                                7
% 11.87/2.02  conjectures:                            1
% 11.87/2.02  epr:                                    0
% 11.87/2.02  horn:                                   7
% 11.87/2.02  ground:                                 2
% 11.87/2.02  unary:                                  6
% 11.87/2.02  binary:                                 1
% 11.87/2.02  lits:                                   8
% 11.87/2.02  lits_eq:                                8
% 11.87/2.02  fd_pure:                                0
% 11.87/2.02  fd_pseudo:                              0
% 11.87/2.02  fd_cond:                                0
% 11.87/2.02  fd_pseudo_cond:                         0
% 11.87/2.02  ac_symbols:                             0
% 11.87/2.02  
% 11.87/2.02  ------ Propositional Solver
% 11.87/2.02  
% 11.87/2.02  prop_solver_calls:                      35
% 11.87/2.02  prop_fast_solver_calls:                 400
% 11.87/2.02  smt_solver_calls:                       0
% 11.87/2.02  smt_fast_solver_calls:                  0
% 11.87/2.02  prop_num_of_clauses:                    7258
% 11.87/2.02  prop_preprocess_simplified:             12218
% 11.87/2.02  prop_fo_subsumed:                       1
% 11.87/2.02  prop_solver_time:                       0.
% 11.87/2.02  smt_solver_time:                        0.
% 11.87/2.02  smt_fast_solver_time:                   0.
% 11.87/2.02  prop_fast_solver_time:                  0.
% 11.87/2.02  prop_unsat_core_time:                   0.
% 11.87/2.02  
% 11.87/2.02  ------ QBF
% 11.87/2.02  
% 11.87/2.02  qbf_q_res:                              0
% 11.87/2.02  qbf_num_tautologies:                    0
% 11.87/2.02  qbf_prep_cycles:                        0
% 11.87/2.02  
% 11.87/2.02  ------ BMC1
% 11.87/2.02  
% 11.87/2.02  bmc1_current_bound:                     -1
% 11.87/2.02  bmc1_last_solved_bound:                 -1
% 11.87/2.02  bmc1_unsat_core_size:                   -1
% 11.87/2.02  bmc1_unsat_core_parents_size:           -1
% 11.87/2.02  bmc1_merge_next_fun:                    0
% 11.87/2.02  bmc1_unsat_core_clauses_time:           0.
% 11.87/2.02  
% 11.87/2.02  ------ Instantiation
% 11.87/2.02  
% 11.87/2.02  inst_num_of_clauses:                    3040
% 11.87/2.02  inst_num_in_passive:                    878
% 11.87/2.02  inst_num_in_active:                     1242
% 11.87/2.02  inst_num_in_unprocessed:                922
% 11.87/2.02  inst_num_of_loops:                      1330
% 11.87/2.02  inst_num_of_learning_restarts:          0
% 11.87/2.02  inst_num_moves_active_passive:          79
% 11.87/2.02  inst_lit_activity:                      0
% 11.87/2.02  inst_lit_activity_moves:                0
% 11.87/2.02  inst_num_tautologies:                   0
% 11.87/2.02  inst_num_prop_implied:                  0
% 11.87/2.02  inst_num_existing_simplified:           0
% 11.87/2.02  inst_num_eq_res_simplified:             0
% 11.87/2.02  inst_num_child_elim:                    0
% 11.87/2.02  inst_num_of_dismatching_blockings:      9272
% 11.87/2.02  inst_num_of_non_proper_insts:           7895
% 11.87/2.02  inst_num_of_duplicates:                 0
% 11.87/2.02  inst_inst_num_from_inst_to_res:         0
% 11.87/2.02  inst_dismatching_checking_time:         0.
% 11.87/2.02  
% 11.87/2.02  ------ Resolution
% 11.87/2.02  
% 11.87/2.02  res_num_of_clauses:                     0
% 11.87/2.02  res_num_in_passive:                     0
% 11.87/2.02  res_num_in_active:                      0
% 11.87/2.02  res_num_of_loops:                       30
% 11.87/2.02  res_forward_subset_subsumed:            685
% 11.87/2.02  res_backward_subset_subsumed:           6
% 11.87/2.02  res_forward_subsumed:                   0
% 11.87/2.02  res_backward_subsumed:                  0
% 11.87/2.02  res_forward_subsumption_resolution:     0
% 11.87/2.02  res_backward_subsumption_resolution:    0
% 11.87/2.02  res_clause_to_clause_subsumption:       32216
% 11.87/2.02  res_orphan_elimination:                 0
% 11.87/2.02  res_tautology_del:                      1198
% 11.87/2.02  res_num_eq_res_simplified:              0
% 11.87/2.02  res_num_sel_changes:                    0
% 11.87/2.02  res_moves_from_active_to_pass:          0
% 11.87/2.02  
% 11.87/2.02  ------ Superposition
% 11.87/2.02  
% 11.87/2.02  sup_time_total:                         0.
% 11.87/2.02  sup_time_generating:                    0.
% 11.87/2.02  sup_time_sim_full:                      0.
% 11.87/2.02  sup_time_sim_immed:                     0.
% 11.87/2.02  
% 11.87/2.02  sup_num_of_clauses:                     1752
% 11.87/2.02  sup_num_in_active:                      233
% 11.87/2.02  sup_num_in_passive:                     1519
% 11.87/2.02  sup_num_of_loops:                       265
% 11.87/2.02  sup_fw_superposition:                   10765
% 11.87/2.02  sup_bw_superposition:                   6615
% 11.87/2.02  sup_immediate_simplified:               7181
% 11.87/2.02  sup_given_eliminated:                   1
% 11.87/2.02  comparisons_done:                       0
% 11.87/2.02  comparisons_avoided:                    0
% 11.87/2.02  
% 11.87/2.02  ------ Simplifications
% 11.87/2.02  
% 11.87/2.02  
% 11.87/2.02  sim_fw_subset_subsumed:                 0
% 11.87/2.02  sim_bw_subset_subsumed:                 0
% 11.87/2.02  sim_fw_subsumed:                        1409
% 11.87/2.02  sim_bw_subsumed:                        53
% 11.87/2.02  sim_fw_subsumption_res:                 0
% 11.87/2.02  sim_bw_subsumption_res:                 0
% 11.87/2.02  sim_tautology_del:                      0
% 11.87/2.02  sim_eq_tautology_del:                   2771
% 11.87/2.02  sim_eq_res_simp:                        1
% 11.87/2.02  sim_fw_demodulated:                     3971
% 11.87/2.02  sim_bw_demodulated:                     61
% 11.87/2.02  sim_light_normalised:                   2690
% 11.87/2.02  sim_joinable_taut:                      0
% 11.87/2.02  sim_joinable_simp:                      0
% 11.87/2.02  sim_ac_normalised:                      0
% 11.87/2.02  sim_smt_subsumption:                    0
% 11.87/2.02  
%------------------------------------------------------------------------------
