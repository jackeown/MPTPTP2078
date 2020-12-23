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
% DateTime   : Thu Dec  3 11:24:12 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 964 expanded)
%              Number of clauses        :   73 ( 299 expanded)
%              Number of leaves         :   13 ( 257 expanded)
%              Depth                    :   24
%              Number of atoms          :  152 (1398 expanded)
%              Number of equality atoms :  106 ( 858 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f31,f30,f30])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f33,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f24,f30,f30,f30,f30])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f30])).

fof(f34,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f32,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_116,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | k4_xboole_0(X2,k4_xboole_0(X2,X3)) != X0
    | k2_xboole_0(X2,X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_117,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_116])).

cnf(c_305,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_117])).

cnf(c_705,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_305])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_760,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_705,c_10])).

cnf(c_2426,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_760,c_9])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2500,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2426,c_8])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_122,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_123,plain,
    ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_197,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_123,c_10])).

cnf(c_215,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_197,c_8])).

cnf(c_238,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_9,c_215])).

cnf(c_242,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_215,c_9])).

cnf(c_267,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_238,c_242])).

cnf(c_268,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_267,c_9,c_242])).

cnf(c_2566,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_2500,c_268])).

cnf(c_179,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_187,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_179,c_8])).

cnf(c_739,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_187,c_705])).

cnf(c_2597,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2566,c_8,c_242,c_739])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_162,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_4,c_10])).

cnf(c_241,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_215,c_10])).

cnf(c_299,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,X0),X1)) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_241,c_9])).

cnf(c_1220,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK2,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_162,c_299])).

cnf(c_1262,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(light_normalisation,[status(thm)],[c_1220,c_242])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_172,plain,
    ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_123,c_7])).

cnf(c_177,plain,
    ( k2_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_172,c_5])).

cnf(c_219,plain,
    ( k2_xboole_0(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_0,c_177])).

cnf(c_709,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_219,c_305])).

cnf(c_829,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1)))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,k4_xboole_0(sK2,X1)))) ),
    inference(superposition,[status(thm)],[c_709,c_162])).

cnf(c_830,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_709,c_10])).

cnf(c_756,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_705,c_162])).

cnf(c_757,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_705,c_10])).

cnf(c_771,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_757,c_8])).

cnf(c_772,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_756,c_771])).

cnf(c_773,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_772,c_8])).

cnf(c_841,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_830,c_8,c_773])).

cnf(c_842,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,X0),X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1)) ),
    inference(demodulation,[status(thm)],[c_829,c_841])).

cnf(c_843,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1)) ),
    inference(demodulation,[status(thm)],[c_842,c_8,c_773])).

cnf(c_1263,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1262,c_268,c_843])).

cnf(c_1264,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1263,c_9,c_10])).

cnf(c_1265,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1264,c_242])).

cnf(c_2930,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_2597,c_1265])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_67,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_130,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_67,c_11])).

cnf(c_131,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_130])).

cnf(c_181,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_131,c_9])).

cnf(c_183,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_181,c_131])).

cnf(c_184,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_183,c_8])).

cnf(c_2931,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_2930,c_8,c_184])).

cnf(c_178,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_131,c_9])).

cnf(c_188,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK0 ),
    inference(demodulation,[status(thm)],[c_178,c_8])).

cnf(c_2988,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_2931,c_188])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_65,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_135,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_65,c_13])).

cnf(c_136,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_3040,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2988,c_136])).

cnf(c_3041,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3040,c_184])).

cnf(c_3042,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3041])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n003.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 10:17:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.10/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/0.98  
% 3.10/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.98  
% 3.10/0.98  ------  iProver source info
% 3.10/0.98  
% 3.10/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.98  git: non_committed_changes: false
% 3.10/0.98  git: last_make_outside_of_git: false
% 3.10/0.98  
% 3.10/0.98  ------ 
% 3.10/0.98  
% 3.10/0.98  ------ Input Options
% 3.10/0.98  
% 3.10/0.98  --out_options                           all
% 3.10/0.98  --tptp_safe_out                         true
% 3.10/0.98  --problem_path                          ""
% 3.10/0.98  --include_path                          ""
% 3.10/0.98  --clausifier                            res/vclausify_rel
% 3.10/0.98  --clausifier_options                    --mode clausify
% 3.10/0.98  --stdin                                 false
% 3.10/0.98  --stats_out                             all
% 3.10/0.98  
% 3.10/0.98  ------ General Options
% 3.10/0.98  
% 3.10/0.98  --fof                                   false
% 3.10/0.98  --time_out_real                         305.
% 3.10/0.98  --time_out_virtual                      -1.
% 3.10/0.98  --symbol_type_check                     false
% 3.10/0.98  --clausify_out                          false
% 3.10/0.98  --sig_cnt_out                           false
% 3.10/0.98  --trig_cnt_out                          false
% 3.10/0.98  --trig_cnt_out_tolerance                1.
% 3.10/0.98  --trig_cnt_out_sk_spl                   false
% 3.10/0.98  --abstr_cl_out                          false
% 3.10/0.98  
% 3.10/0.98  ------ Global Options
% 3.10/0.98  
% 3.10/0.98  --schedule                              default
% 3.10/0.98  --add_important_lit                     false
% 3.10/0.98  --prop_solver_per_cl                    1000
% 3.10/0.98  --min_unsat_core                        false
% 3.10/0.98  --soft_assumptions                      false
% 3.10/0.98  --soft_lemma_size                       3
% 3.10/0.98  --prop_impl_unit_size                   0
% 3.10/0.98  --prop_impl_unit                        []
% 3.10/0.98  --share_sel_clauses                     true
% 3.10/0.98  --reset_solvers                         false
% 3.10/0.98  --bc_imp_inh                            [conj_cone]
% 3.10/0.98  --conj_cone_tolerance                   3.
% 3.10/0.98  --extra_neg_conj                        none
% 3.10/0.98  --large_theory_mode                     true
% 3.10/0.98  --prolific_symb_bound                   200
% 3.10/0.98  --lt_threshold                          2000
% 3.10/0.98  --clause_weak_htbl                      true
% 3.10/0.98  --gc_record_bc_elim                     false
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing Options
% 3.10/0.98  
% 3.10/0.98  --preprocessing_flag                    true
% 3.10/0.98  --time_out_prep_mult                    0.1
% 3.10/0.98  --splitting_mode                        input
% 3.10/0.98  --splitting_grd                         true
% 3.10/0.98  --splitting_cvd                         false
% 3.10/0.98  --splitting_cvd_svl                     false
% 3.10/0.98  --splitting_nvd                         32
% 3.10/0.98  --sub_typing                            true
% 3.10/0.98  --prep_gs_sim                           true
% 3.10/0.98  --prep_unflatten                        true
% 3.10/0.98  --prep_res_sim                          true
% 3.10/0.98  --prep_upred                            true
% 3.10/0.98  --prep_sem_filter                       exhaustive
% 3.10/0.98  --prep_sem_filter_out                   false
% 3.10/0.98  --pred_elim                             true
% 3.10/0.98  --res_sim_input                         true
% 3.10/0.98  --eq_ax_congr_red                       true
% 3.10/0.98  --pure_diseq_elim                       true
% 3.10/0.98  --brand_transform                       false
% 3.10/0.98  --non_eq_to_eq                          false
% 3.10/0.98  --prep_def_merge                        true
% 3.10/0.98  --prep_def_merge_prop_impl              false
% 3.10/0.98  --prep_def_merge_mbd                    true
% 3.10/0.98  --prep_def_merge_tr_red                 false
% 3.10/0.98  --prep_def_merge_tr_cl                  false
% 3.10/0.98  --smt_preprocessing                     true
% 3.10/0.98  --smt_ac_axioms                         fast
% 3.10/0.98  --preprocessed_out                      false
% 3.10/0.98  --preprocessed_stats                    false
% 3.10/0.98  
% 3.10/0.98  ------ Abstraction refinement Options
% 3.10/0.98  
% 3.10/0.98  --abstr_ref                             []
% 3.10/0.98  --abstr_ref_prep                        false
% 3.10/0.98  --abstr_ref_until_sat                   false
% 3.10/0.98  --abstr_ref_sig_restrict                funpre
% 3.10/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.98  --abstr_ref_under                       []
% 3.10/0.98  
% 3.10/0.98  ------ SAT Options
% 3.10/0.98  
% 3.10/0.98  --sat_mode                              false
% 3.10/0.98  --sat_fm_restart_options                ""
% 3.10/0.98  --sat_gr_def                            false
% 3.10/0.98  --sat_epr_types                         true
% 3.10/0.98  --sat_non_cyclic_types                  false
% 3.10/0.98  --sat_finite_models                     false
% 3.10/0.98  --sat_fm_lemmas                         false
% 3.10/0.98  --sat_fm_prep                           false
% 3.10/0.98  --sat_fm_uc_incr                        true
% 3.10/0.98  --sat_out_model                         small
% 3.10/0.98  --sat_out_clauses                       false
% 3.10/0.98  
% 3.10/0.98  ------ QBF Options
% 3.10/0.98  
% 3.10/0.98  --qbf_mode                              false
% 3.10/0.98  --qbf_elim_univ                         false
% 3.10/0.98  --qbf_dom_inst                          none
% 3.10/0.98  --qbf_dom_pre_inst                      false
% 3.10/0.98  --qbf_sk_in                             false
% 3.10/0.98  --qbf_pred_elim                         true
% 3.10/0.98  --qbf_split                             512
% 3.10/0.98  
% 3.10/0.98  ------ BMC1 Options
% 3.10/0.98  
% 3.10/0.98  --bmc1_incremental                      false
% 3.10/0.98  --bmc1_axioms                           reachable_all
% 3.10/0.98  --bmc1_min_bound                        0
% 3.10/0.98  --bmc1_max_bound                        -1
% 3.10/0.98  --bmc1_max_bound_default                -1
% 3.10/0.98  --bmc1_symbol_reachability              true
% 3.10/0.98  --bmc1_property_lemmas                  false
% 3.10/0.98  --bmc1_k_induction                      false
% 3.10/0.98  --bmc1_non_equiv_states                 false
% 3.10/0.98  --bmc1_deadlock                         false
% 3.10/0.98  --bmc1_ucm                              false
% 3.10/0.98  --bmc1_add_unsat_core                   none
% 3.10/0.98  --bmc1_unsat_core_children              false
% 3.10/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.98  --bmc1_out_stat                         full
% 3.10/0.98  --bmc1_ground_init                      false
% 3.10/0.98  --bmc1_pre_inst_next_state              false
% 3.10/0.98  --bmc1_pre_inst_state                   false
% 3.10/0.98  --bmc1_pre_inst_reach_state             false
% 3.10/0.98  --bmc1_out_unsat_core                   false
% 3.10/0.98  --bmc1_aig_witness_out                  false
% 3.10/0.98  --bmc1_verbose                          false
% 3.10/0.98  --bmc1_dump_clauses_tptp                false
% 3.10/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.98  --bmc1_dump_file                        -
% 3.10/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.98  --bmc1_ucm_extend_mode                  1
% 3.10/0.98  --bmc1_ucm_init_mode                    2
% 3.10/0.98  --bmc1_ucm_cone_mode                    none
% 3.10/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.98  --bmc1_ucm_relax_model                  4
% 3.10/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.98  --bmc1_ucm_layered_model                none
% 3.10/0.98  --bmc1_ucm_max_lemma_size               10
% 3.10/0.98  
% 3.10/0.98  ------ AIG Options
% 3.10/0.98  
% 3.10/0.98  --aig_mode                              false
% 3.10/0.98  
% 3.10/0.98  ------ Instantiation Options
% 3.10/0.98  
% 3.10/0.98  --instantiation_flag                    true
% 3.10/0.98  --inst_sos_flag                         false
% 3.10/0.98  --inst_sos_phase                        true
% 3.10/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.98  --inst_lit_sel_side                     num_symb
% 3.10/0.98  --inst_solver_per_active                1400
% 3.10/0.98  --inst_solver_calls_frac                1.
% 3.10/0.98  --inst_passive_queue_type               priority_queues
% 3.10/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.98  --inst_passive_queues_freq              [25;2]
% 3.10/0.98  --inst_dismatching                      true
% 3.10/0.98  --inst_eager_unprocessed_to_passive     true
% 3.10/0.98  --inst_prop_sim_given                   true
% 3.10/0.98  --inst_prop_sim_new                     false
% 3.10/0.98  --inst_subs_new                         false
% 3.10/0.98  --inst_eq_res_simp                      false
% 3.10/0.98  --inst_subs_given                       false
% 3.10/0.98  --inst_orphan_elimination               true
% 3.10/0.98  --inst_learning_loop_flag               true
% 3.10/0.98  --inst_learning_start                   3000
% 3.10/0.98  --inst_learning_factor                  2
% 3.10/0.98  --inst_start_prop_sim_after_learn       3
% 3.10/0.98  --inst_sel_renew                        solver
% 3.10/0.98  --inst_lit_activity_flag                true
% 3.10/0.98  --inst_restr_to_given                   false
% 3.10/0.98  --inst_activity_threshold               500
% 3.10/0.98  --inst_out_proof                        true
% 3.10/0.98  
% 3.10/0.98  ------ Resolution Options
% 3.10/0.98  
% 3.10/0.98  --resolution_flag                       true
% 3.10/0.98  --res_lit_sel                           adaptive
% 3.10/0.98  --res_lit_sel_side                      none
% 3.10/0.98  --res_ordering                          kbo
% 3.10/0.98  --res_to_prop_solver                    active
% 3.10/0.98  --res_prop_simpl_new                    false
% 3.10/0.98  --res_prop_simpl_given                  true
% 3.10/0.98  --res_passive_queue_type                priority_queues
% 3.10/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.98  --res_passive_queues_freq               [15;5]
% 3.10/0.98  --res_forward_subs                      full
% 3.10/0.98  --res_backward_subs                     full
% 3.10/0.98  --res_forward_subs_resolution           true
% 3.10/0.98  --res_backward_subs_resolution          true
% 3.10/0.98  --res_orphan_elimination                true
% 3.10/0.98  --res_time_limit                        2.
% 3.10/0.98  --res_out_proof                         true
% 3.10/0.98  
% 3.10/0.98  ------ Superposition Options
% 3.10/0.98  
% 3.10/0.98  --superposition_flag                    true
% 3.10/0.98  --sup_passive_queue_type                priority_queues
% 3.10/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.98  --demod_completeness_check              fast
% 3.10/0.98  --demod_use_ground                      true
% 3.10/0.98  --sup_to_prop_solver                    passive
% 3.10/0.98  --sup_prop_simpl_new                    true
% 3.10/0.98  --sup_prop_simpl_given                  true
% 3.10/0.98  --sup_fun_splitting                     false
% 3.10/0.98  --sup_smt_interval                      50000
% 3.10/0.98  
% 3.10/0.98  ------ Superposition Simplification Setup
% 3.10/0.98  
% 3.10/0.98  --sup_indices_passive                   []
% 3.10/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_full_bw                           [BwDemod]
% 3.10/0.98  --sup_immed_triv                        [TrivRules]
% 3.10/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_immed_bw_main                     []
% 3.10/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.98  
% 3.10/0.98  ------ Combination Options
% 3.10/0.98  
% 3.10/0.98  --comb_res_mult                         3
% 3.10/0.98  --comb_sup_mult                         2
% 3.10/0.98  --comb_inst_mult                        10
% 3.10/0.98  
% 3.10/0.98  ------ Debug Options
% 3.10/0.98  
% 3.10/0.98  --dbg_backtrace                         false
% 3.10/0.98  --dbg_dump_prop_clauses                 false
% 3.10/0.98  --dbg_dump_prop_clauses_file            -
% 3.10/0.98  --dbg_out_stat                          false
% 3.10/0.98  ------ Parsing...
% 3.10/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.10/0.98  ------ Proving...
% 3.10/0.98  ------ Problem Properties 
% 3.10/0.98  
% 3.10/0.98  
% 3.10/0.98  clauses                                 12
% 3.10/0.98  conjectures                             0
% 3.10/0.98  EPR                                     0
% 3.10/0.98  Horn                                    12
% 3.10/0.98  unary                                   12
% 3.10/0.98  binary                                  0
% 3.10/0.98  lits                                    12
% 3.10/0.98  lits eq                                 12
% 3.10/0.98  fd_pure                                 0
% 3.10/0.98  fd_pseudo                               0
% 3.10/0.98  fd_cond                                 0
% 3.10/0.98  fd_pseudo_cond                          0
% 3.10/0.98  AC symbols                              0
% 3.10/0.98  
% 3.10/0.98  ------ Schedule UEQ
% 3.10/0.98  
% 3.10/0.98  ------ pure equality problem: resolution off 
% 3.10/0.98  
% 3.10/0.98  ------ Option_UEQ Time Limit: Unbounded
% 3.10/0.98  
% 3.10/0.98  
% 3.10/0.98  ------ 
% 3.10/0.98  Current options:
% 3.10/0.98  ------ 
% 3.10/0.98  
% 3.10/0.98  ------ Input Options
% 3.10/0.98  
% 3.10/0.98  --out_options                           all
% 3.10/0.98  --tptp_safe_out                         true
% 3.10/0.98  --problem_path                          ""
% 3.10/0.98  --include_path                          ""
% 3.10/0.98  --clausifier                            res/vclausify_rel
% 3.10/0.98  --clausifier_options                    --mode clausify
% 3.10/0.98  --stdin                                 false
% 3.10/0.98  --stats_out                             all
% 3.10/0.98  
% 3.10/0.98  ------ General Options
% 3.10/0.98  
% 3.10/0.98  --fof                                   false
% 3.10/0.98  --time_out_real                         305.
% 3.10/0.98  --time_out_virtual                      -1.
% 3.10/0.98  --symbol_type_check                     false
% 3.10/0.98  --clausify_out                          false
% 3.10/0.98  --sig_cnt_out                           false
% 3.10/0.98  --trig_cnt_out                          false
% 3.10/0.98  --trig_cnt_out_tolerance                1.
% 3.10/0.98  --trig_cnt_out_sk_spl                   false
% 3.10/0.98  --abstr_cl_out                          false
% 3.10/0.98  
% 3.10/0.98  ------ Global Options
% 3.10/0.98  
% 3.10/0.98  --schedule                              default
% 3.10/0.98  --add_important_lit                     false
% 3.10/0.98  --prop_solver_per_cl                    1000
% 3.10/0.98  --min_unsat_core                        false
% 3.10/0.98  --soft_assumptions                      false
% 3.10/0.98  --soft_lemma_size                       3
% 3.10/0.98  --prop_impl_unit_size                   0
% 3.10/0.98  --prop_impl_unit                        []
% 3.10/0.98  --share_sel_clauses                     true
% 3.10/0.98  --reset_solvers                         false
% 3.10/0.98  --bc_imp_inh                            [conj_cone]
% 3.10/0.98  --conj_cone_tolerance                   3.
% 3.10/0.98  --extra_neg_conj                        none
% 3.10/0.98  --large_theory_mode                     true
% 3.10/0.98  --prolific_symb_bound                   200
% 3.10/0.98  --lt_threshold                          2000
% 3.10/0.98  --clause_weak_htbl                      true
% 3.10/0.98  --gc_record_bc_elim                     false
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing Options
% 3.10/0.98  
% 3.10/0.98  --preprocessing_flag                    true
% 3.10/0.98  --time_out_prep_mult                    0.1
% 3.10/0.98  --splitting_mode                        input
% 3.10/0.98  --splitting_grd                         true
% 3.10/0.98  --splitting_cvd                         false
% 3.10/0.98  --splitting_cvd_svl                     false
% 3.10/0.98  --splitting_nvd                         32
% 3.10/0.98  --sub_typing                            true
% 3.10/0.98  --prep_gs_sim                           true
% 3.10/0.98  --prep_unflatten                        true
% 3.10/0.98  --prep_res_sim                          true
% 3.10/0.98  --prep_upred                            true
% 3.10/0.98  --prep_sem_filter                       exhaustive
% 3.10/0.98  --prep_sem_filter_out                   false
% 3.10/0.98  --pred_elim                             true
% 3.10/0.98  --res_sim_input                         true
% 3.10/0.99  --eq_ax_congr_red                       true
% 3.10/0.99  --pure_diseq_elim                       true
% 3.10/0.99  --brand_transform                       false
% 3.10/0.99  --non_eq_to_eq                          false
% 3.10/0.99  --prep_def_merge                        true
% 3.10/0.99  --prep_def_merge_prop_impl              false
% 3.10/0.99  --prep_def_merge_mbd                    true
% 3.10/0.99  --prep_def_merge_tr_red                 false
% 3.10/0.99  --prep_def_merge_tr_cl                  false
% 3.10/0.99  --smt_preprocessing                     true
% 3.10/0.99  --smt_ac_axioms                         fast
% 3.10/0.99  --preprocessed_out                      false
% 3.10/0.99  --preprocessed_stats                    false
% 3.10/0.99  
% 3.10/0.99  ------ Abstraction refinement Options
% 3.10/0.99  
% 3.10/0.99  --abstr_ref                             []
% 3.10/0.99  --abstr_ref_prep                        false
% 3.10/0.99  --abstr_ref_until_sat                   false
% 3.10/0.99  --abstr_ref_sig_restrict                funpre
% 3.10/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.99  --abstr_ref_under                       []
% 3.10/0.99  
% 3.10/0.99  ------ SAT Options
% 3.10/0.99  
% 3.10/0.99  --sat_mode                              false
% 3.10/0.99  --sat_fm_restart_options                ""
% 3.10/0.99  --sat_gr_def                            false
% 3.10/0.99  --sat_epr_types                         true
% 3.10/0.99  --sat_non_cyclic_types                  false
% 3.10/0.99  --sat_finite_models                     false
% 3.10/0.99  --sat_fm_lemmas                         false
% 3.10/0.99  --sat_fm_prep                           false
% 3.10/0.99  --sat_fm_uc_incr                        true
% 3.10/0.99  --sat_out_model                         small
% 3.10/0.99  --sat_out_clauses                       false
% 3.10/0.99  
% 3.10/0.99  ------ QBF Options
% 3.10/0.99  
% 3.10/0.99  --qbf_mode                              false
% 3.10/0.99  --qbf_elim_univ                         false
% 3.10/0.99  --qbf_dom_inst                          none
% 3.10/0.99  --qbf_dom_pre_inst                      false
% 3.10/0.99  --qbf_sk_in                             false
% 3.10/0.99  --qbf_pred_elim                         true
% 3.10/0.99  --qbf_split                             512
% 3.10/0.99  
% 3.10/0.99  ------ BMC1 Options
% 3.10/0.99  
% 3.10/0.99  --bmc1_incremental                      false
% 3.10/0.99  --bmc1_axioms                           reachable_all
% 3.10/0.99  --bmc1_min_bound                        0
% 3.10/0.99  --bmc1_max_bound                        -1
% 3.10/0.99  --bmc1_max_bound_default                -1
% 3.10/0.99  --bmc1_symbol_reachability              true
% 3.10/0.99  --bmc1_property_lemmas                  false
% 3.10/0.99  --bmc1_k_induction                      false
% 3.10/0.99  --bmc1_non_equiv_states                 false
% 3.10/0.99  --bmc1_deadlock                         false
% 3.10/0.99  --bmc1_ucm                              false
% 3.10/0.99  --bmc1_add_unsat_core                   none
% 3.10/0.99  --bmc1_unsat_core_children              false
% 3.10/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.99  --bmc1_out_stat                         full
% 3.10/0.99  --bmc1_ground_init                      false
% 3.10/0.99  --bmc1_pre_inst_next_state              false
% 3.10/0.99  --bmc1_pre_inst_state                   false
% 3.10/0.99  --bmc1_pre_inst_reach_state             false
% 3.10/0.99  --bmc1_out_unsat_core                   false
% 3.10/0.99  --bmc1_aig_witness_out                  false
% 3.10/0.99  --bmc1_verbose                          false
% 3.10/0.99  --bmc1_dump_clauses_tptp                false
% 3.10/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.99  --bmc1_dump_file                        -
% 3.10/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.99  --bmc1_ucm_extend_mode                  1
% 3.10/0.99  --bmc1_ucm_init_mode                    2
% 3.10/0.99  --bmc1_ucm_cone_mode                    none
% 3.10/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.99  --bmc1_ucm_relax_model                  4
% 3.10/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.99  --bmc1_ucm_layered_model                none
% 3.10/0.99  --bmc1_ucm_max_lemma_size               10
% 3.10/0.99  
% 3.10/0.99  ------ AIG Options
% 3.10/0.99  
% 3.10/0.99  --aig_mode                              false
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation Options
% 3.10/0.99  
% 3.10/0.99  --instantiation_flag                    false
% 3.10/0.99  --inst_sos_flag                         false
% 3.10/0.99  --inst_sos_phase                        true
% 3.10/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel_side                     num_symb
% 3.10/0.99  --inst_solver_per_active                1400
% 3.10/0.99  --inst_solver_calls_frac                1.
% 3.10/0.99  --inst_passive_queue_type               priority_queues
% 3.10/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.99  --inst_passive_queues_freq              [25;2]
% 3.10/0.99  --inst_dismatching                      true
% 3.10/0.99  --inst_eager_unprocessed_to_passive     true
% 3.10/0.99  --inst_prop_sim_given                   true
% 3.10/0.99  --inst_prop_sim_new                     false
% 3.10/0.99  --inst_subs_new                         false
% 3.10/0.99  --inst_eq_res_simp                      false
% 3.10/0.99  --inst_subs_given                       false
% 3.10/0.99  --inst_orphan_elimination               true
% 3.10/0.99  --inst_learning_loop_flag               true
% 3.10/0.99  --inst_learning_start                   3000
% 3.10/0.99  --inst_learning_factor                  2
% 3.10/0.99  --inst_start_prop_sim_after_learn       3
% 3.10/0.99  --inst_sel_renew                        solver
% 3.10/0.99  --inst_lit_activity_flag                true
% 3.10/0.99  --inst_restr_to_given                   false
% 3.10/0.99  --inst_activity_threshold               500
% 3.10/0.99  --inst_out_proof                        true
% 3.10/0.99  
% 3.10/0.99  ------ Resolution Options
% 3.10/0.99  
% 3.10/0.99  --resolution_flag                       false
% 3.10/0.99  --res_lit_sel                           adaptive
% 3.10/0.99  --res_lit_sel_side                      none
% 3.10/0.99  --res_ordering                          kbo
% 3.10/0.99  --res_to_prop_solver                    active
% 3.10/0.99  --res_prop_simpl_new                    false
% 3.10/0.99  --res_prop_simpl_given                  true
% 3.10/0.99  --res_passive_queue_type                priority_queues
% 3.10/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.99  --res_passive_queues_freq               [15;5]
% 3.10/0.99  --res_forward_subs                      full
% 3.10/0.99  --res_backward_subs                     full
% 3.10/0.99  --res_forward_subs_resolution           true
% 3.10/0.99  --res_backward_subs_resolution          true
% 3.10/0.99  --res_orphan_elimination                true
% 3.10/0.99  --res_time_limit                        2.
% 3.10/0.99  --res_out_proof                         true
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Options
% 3.10/0.99  
% 3.10/0.99  --superposition_flag                    true
% 3.10/0.99  --sup_passive_queue_type                priority_queues
% 3.10/0.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.99  --demod_completeness_check              fast
% 3.10/0.99  --demod_use_ground                      true
% 3.10/0.99  --sup_to_prop_solver                    active
% 3.10/0.99  --sup_prop_simpl_new                    false
% 3.10/0.99  --sup_prop_simpl_given                  false
% 3.10/0.99  --sup_fun_splitting                     true
% 3.10/0.99  --sup_smt_interval                      10000
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Simplification Setup
% 3.10/0.99  
% 3.10/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.10/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_full_triv                         [TrivRules]
% 3.10/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.10/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.10/0.99  --sup_immed_triv                        [TrivRules]
% 3.10/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_immed_bw_main                     []
% 3.10/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.10/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.10/0.99  
% 3.10/0.99  ------ Combination Options
% 3.10/0.99  
% 3.10/0.99  --comb_res_mult                         1
% 3.10/0.99  --comb_sup_mult                         1
% 3.10/0.99  --comb_inst_mult                        1000000
% 3.10/0.99  
% 3.10/0.99  ------ Debug Options
% 3.10/0.99  
% 3.10/0.99  --dbg_backtrace                         false
% 3.10/0.99  --dbg_dump_prop_clauses                 false
% 3.10/0.99  --dbg_dump_prop_clauses_file            -
% 3.10/0.99  --dbg_out_stat                          false
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ Proving...
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS status Theorem for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99   Resolution empty clause
% 3.10/0.99  
% 3.10/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  fof(f5,axiom,(
% 3.10/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f25,plain,(
% 3.10/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.10/0.99    inference(cnf_transformation,[],[f5])).
% 3.10/0.99  
% 3.10/0.99  fof(f9,axiom,(
% 3.10/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f29,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f9])).
% 3.10/0.99  
% 3.10/0.99  fof(f10,axiom,(
% 3.10/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f30,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f10])).
% 3.10/0.99  
% 3.10/0.99  fof(f39,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.10/0.99    inference(definition_unfolding,[],[f29,f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f3,axiom,(
% 3.10/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f14,plain,(
% 3.10/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 3.10/0.99    inference(unused_predicate_definition_removal,[],[f3])).
% 3.10/0.99  
% 3.10/0.99  fof(f15,plain,(
% 3.10/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 3.10/0.99    inference(ennf_transformation,[],[f14])).
% 3.10/0.99  
% 3.10/0.99  fof(f23,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f15])).
% 3.10/0.99  
% 3.10/0.99  fof(f6,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f26,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f6])).
% 3.10/0.99  
% 3.10/0.99  fof(f38,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2))) )),
% 3.10/0.99    inference(definition_unfolding,[],[f26,f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f11,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f31,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f11])).
% 3.10/0.99  
% 3.10/0.99  fof(f40,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.10/0.99    inference(definition_unfolding,[],[f31,f30,f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f8,axiom,(
% 3.10/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f28,plain,(
% 3.10/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.10/0.99    inference(cnf_transformation,[],[f8])).
% 3.10/0.99  
% 3.10/0.99  fof(f12,conjecture,(
% 3.10/0.99    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f13,negated_conjecture,(
% 3.10/0.99    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 3.10/0.99    inference(negated_conjecture,[],[f12])).
% 3.10/0.99  
% 3.10/0.99  fof(f16,plain,(
% 3.10/0.99    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 3.10/0.99    inference(ennf_transformation,[],[f13])).
% 3.10/0.99  
% 3.10/0.99  fof(f18,plain,(
% 3.10/0.99    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f19,plain,(
% 3.10/0.99    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 3.10/0.99  
% 3.10/0.99  fof(f33,plain,(
% 3.10/0.99    r1_tarski(sK0,sK2)),
% 3.10/0.99    inference(cnf_transformation,[],[f19])).
% 3.10/0.99  
% 3.10/0.99  fof(f4,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f24,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f4])).
% 3.10/0.99  
% 3.10/0.99  fof(f37,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 3.10/0.99    inference(definition_unfolding,[],[f24,f30,f30,f30,f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f1,axiom,(
% 3.10/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f20,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f1])).
% 3.10/0.99  
% 3.10/0.99  fof(f7,axiom,(
% 3.10/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f27,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f7])).
% 3.10/0.99  
% 3.10/0.99  fof(f2,axiom,(
% 3.10/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f17,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.10/0.99    inference(nnf_transformation,[],[f2])).
% 3.10/0.99  
% 3.10/0.99  fof(f21,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f17])).
% 3.10/0.99  
% 3.10/0.99  fof(f36,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.10/0.99    inference(definition_unfolding,[],[f21,f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f34,plain,(
% 3.10/0.99    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 3.10/0.99    inference(cnf_transformation,[],[f19])).
% 3.10/0.99  
% 3.10/0.99  fof(f41,plain,(
% 3.10/0.99    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 3.10/0.99    inference(definition_unfolding,[],[f34,f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f22,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.10/0.99    inference(cnf_transformation,[],[f17])).
% 3.10/0.99  
% 3.10/0.99  fof(f35,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.10/0.99    inference(definition_unfolding,[],[f22,f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f32,plain,(
% 3.10/0.99    ~r1_xboole_0(sK0,sK1)),
% 3.10/0.99    inference(cnf_transformation,[],[f19])).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5,plain,
% 3.10/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_9,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6,plain,
% 3.10/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
% 3.10/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_116,plain,
% 3.10/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.10/0.99      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) != X0
% 3.10/0.99      | k2_xboole_0(X2,X4) != X1 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_117,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_116]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_305,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_9,c_117]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_705,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_5,c_305]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_10,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 3.10/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_760,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_705,c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2426,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_760,c_9]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2500,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_2426,c_8]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_12,negated_conjecture,
% 3.10/0.99      ( r1_tarski(sK0,sK2) ),
% 3.10/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_122,plain,
% 3.10/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK2 != X1 | sK0 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_123,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_122]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_197,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_123,c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_215,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_197,c_8]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_238,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_9,c_215]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_242,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_215,c_9]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_267,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_238,c_242]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_268,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_267,c_9,c_242]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2566,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_2500,c_268]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_179,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_187,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_179,c_8]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_739,plain,
% 3.10/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_187,c_705]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2597,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = sK0 ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_2566,c_8,c_242,c_739]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_162,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_4,c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_241,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_215,c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_299,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,X0),X1)) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,X0),X1)) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_241,c_9]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1220,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK2,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_162,c_299]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1262,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_1220,c_242]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_0,plain,
% 3.10/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f20]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_7,plain,
% 3.10/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_172,plain,
% 3.10/0.99      ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k1_xboole_0) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_123,c_7]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_177,plain,
% 3.10/0.99      ( k2_xboole_0(sK2,sK0) = sK2 ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_172,c_5]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_219,plain,
% 3.10/0.99      ( k2_xboole_0(sK0,sK2) = sK2 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_0,c_177]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_709,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(sK0,X0),sK2) = k1_xboole_0 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_219,c_305]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_829,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1)))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,k4_xboole_0(sK2,X1)))) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_709,c_162]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_830,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),X1) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_709,c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_756,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_705,c_162]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_757,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_705,c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_771,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_757,c_8]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_772,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_756,c_771]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_773,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_772,c_8]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_841,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_830,c_8,c_773]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_842,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,X0),X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1)) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_829,c_841]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_843,plain,
% 3.10/0.99      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK2,X1)) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_842,c_8,c_773]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1263,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_1262,c_268,c_843]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1264,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_1263,c_9,c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1265,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_1264,c_242]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2930,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,sK0))) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_2597,c_1265]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2,plain,
% 3.10/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.10/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_67,plain,
% 3.10/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.10/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.10/0.99      inference(prop_impl,[status(thm)],[c_2]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_11,negated_conjecture,
% 3.10/0.99      ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_130,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.10/0.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
% 3.10/0.99      | sK0 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_67,c_11]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_131,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_130]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_181,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_131,c_9]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_183,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_181,c_131]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_184,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_183,c_8]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2931,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k4_xboole_0(sK0,X0) ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_2930,c_8,c_184]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_178,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_131,c_9]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_188,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK0 ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_178,c_8]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2988,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_2931,c_188]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1,plain,
% 3.10/0.99      ( r1_xboole_0(X0,X1)
% 3.10/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_65,plain,
% 3.10/0.99      ( r1_xboole_0(X0,X1)
% 3.10/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.10/0.99      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_13,negated_conjecture,
% 3.10/0.99      ( ~ r1_xboole_0(sK0,sK1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_135,plain,
% 3.10/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.10/0.99      | sK1 != X1
% 3.10/0.99      | sK0 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_65,c_13]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_136,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_135]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3040,plain,
% 3.10/0.99      ( k4_xboole_0(sK0,sK0) != k1_xboole_0 ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_2988,c_136]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3041,plain,
% 3.10/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_3040,c_184]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3042,plain,
% 3.10/0.99      ( $false ),
% 3.10/0.99      inference(equality_resolution_simp,[status(thm)],[c_3041]) ).
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  ------                               Statistics
% 3.10/0.99  
% 3.10/0.99  ------ General
% 3.10/0.99  
% 3.10/0.99  abstr_ref_over_cycles:                  0
% 3.10/0.99  abstr_ref_under_cycles:                 0
% 3.10/0.99  gc_basic_clause_elim:                   0
% 3.10/0.99  forced_gc_time:                         0
% 3.10/0.99  parsing_time:                           0.008
% 3.10/0.99  unif_index_cands_time:                  0.
% 3.10/0.99  unif_index_add_time:                    0.
% 3.10/0.99  orderings_time:                         0.
% 3.10/0.99  out_proof_time:                         0.007
% 3.10/0.99  total_time:                             0.151
% 3.10/0.99  num_of_symbols:                         39
% 3.10/0.99  num_of_terms:                           5533
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing
% 3.10/0.99  
% 3.10/0.99  num_of_splits:                          0
% 3.10/0.99  num_of_split_atoms:                     0
% 3.10/0.99  num_of_reused_defs:                     0
% 3.10/0.99  num_eq_ax_congr_red:                    3
% 3.10/0.99  num_of_sem_filtered_clauses:            0
% 3.10/0.99  num_of_subtypes:                        0
% 3.10/0.99  monotx_restored_types:                  0
% 3.10/0.99  sat_num_of_epr_types:                   0
% 3.10/0.99  sat_num_of_non_cyclic_types:            0
% 3.10/0.99  sat_guarded_non_collapsed_types:        0
% 3.10/0.99  num_pure_diseq_elim:                    0
% 3.10/0.99  simp_replaced_by:                       0
% 3.10/0.99  res_preprocessed:                       42
% 3.10/0.99  prep_upred:                             0
% 3.10/0.99  prep_unflattend:                        8
% 3.10/0.99  smt_new_axioms:                         0
% 3.10/0.99  pred_elim_cands:                        0
% 3.10/0.99  pred_elim:                              2
% 3.10/0.99  pred_elim_cl:                           2
% 3.10/0.99  pred_elim_cycles:                       3
% 3.10/0.99  merged_defs:                            2
% 3.10/0.99  merged_defs_ncl:                        0
% 3.10/0.99  bin_hyper_res:                          2
% 3.10/0.99  prep_cycles:                            3
% 3.10/0.99  pred_elim_time:                         0.001
% 3.10/0.99  splitting_time:                         0.
% 3.10/0.99  sem_filter_time:                        0.
% 3.10/0.99  monotx_time:                            0.
% 3.10/0.99  subtype_inf_time:                       0.
% 3.10/0.99  
% 3.10/0.99  ------ Problem properties
% 3.10/0.99  
% 3.10/0.99  clauses:                                12
% 3.10/0.99  conjectures:                            0
% 3.10/0.99  epr:                                    0
% 3.10/0.99  horn:                                   12
% 3.10/0.99  ground:                                 4
% 3.10/0.99  unary:                                  12
% 3.10/0.99  binary:                                 0
% 3.10/0.99  lits:                                   12
% 3.10/0.99  lits_eq:                                12
% 3.10/0.99  fd_pure:                                0
% 3.10/0.99  fd_pseudo:                              0
% 3.10/0.99  fd_cond:                                0
% 3.10/0.99  fd_pseudo_cond:                         0
% 3.10/0.99  ac_symbols:                             0
% 3.10/0.99  
% 3.10/0.99  ------ Propositional Solver
% 3.10/0.99  
% 3.10/0.99  prop_solver_calls:                      17
% 3.10/0.99  prop_fast_solver_calls:                 106
% 3.10/0.99  smt_solver_calls:                       0
% 3.10/0.99  smt_fast_solver_calls:                  0
% 3.10/0.99  prop_num_of_clauses:                    149
% 3.10/0.99  prop_preprocess_simplified:             611
% 3.10/0.99  prop_fo_subsumed:                       0
% 3.10/0.99  prop_solver_time:                       0.
% 3.10/0.99  smt_solver_time:                        0.
% 3.10/0.99  smt_fast_solver_time:                   0.
% 3.10/0.99  prop_fast_solver_time:                  0.
% 3.10/0.99  prop_unsat_core_time:                   0.
% 3.10/0.99  
% 3.10/0.99  ------ QBF
% 3.10/0.99  
% 3.10/0.99  qbf_q_res:                              0
% 3.10/0.99  qbf_num_tautologies:                    0
% 3.10/0.99  qbf_prep_cycles:                        0
% 3.10/0.99  
% 3.10/0.99  ------ BMC1
% 3.10/0.99  
% 3.10/0.99  bmc1_current_bound:                     -1
% 3.10/0.99  bmc1_last_solved_bound:                 -1
% 3.10/0.99  bmc1_unsat_core_size:                   -1
% 3.10/0.99  bmc1_unsat_core_parents_size:           -1
% 3.10/0.99  bmc1_merge_next_fun:                    0
% 3.10/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation
% 3.10/0.99  
% 3.10/0.99  inst_num_of_clauses:                    0
% 3.10/0.99  inst_num_in_passive:                    0
% 3.10/0.99  inst_num_in_active:                     0
% 3.10/0.99  inst_num_in_unprocessed:                0
% 3.10/0.99  inst_num_of_loops:                      0
% 3.10/0.99  inst_num_of_learning_restarts:          0
% 3.10/0.99  inst_num_moves_active_passive:          0
% 3.10/0.99  inst_lit_activity:                      0
% 3.10/0.99  inst_lit_activity_moves:                0
% 3.10/0.99  inst_num_tautologies:                   0
% 3.10/0.99  inst_num_prop_implied:                  0
% 3.10/0.99  inst_num_existing_simplified:           0
% 3.10/0.99  inst_num_eq_res_simplified:             0
% 3.10/0.99  inst_num_child_elim:                    0
% 3.10/0.99  inst_num_of_dismatching_blockings:      0
% 3.10/0.99  inst_num_of_non_proper_insts:           0
% 3.10/0.99  inst_num_of_duplicates:                 0
% 3.10/0.99  inst_inst_num_from_inst_to_res:         0
% 3.10/0.99  inst_dismatching_checking_time:         0.
% 3.10/0.99  
% 3.10/0.99  ------ Resolution
% 3.10/0.99  
% 3.10/0.99  res_num_of_clauses:                     0
% 3.10/0.99  res_num_in_passive:                     0
% 3.10/0.99  res_num_in_active:                      0
% 3.10/0.99  res_num_of_loops:                       45
% 3.10/0.99  res_forward_subset_subsumed:            0
% 3.10/0.99  res_backward_subset_subsumed:           0
% 3.10/0.99  res_forward_subsumed:                   0
% 3.10/0.99  res_backward_subsumed:                  0
% 3.10/0.99  res_forward_subsumption_resolution:     0
% 3.10/0.99  res_backward_subsumption_resolution:    0
% 3.10/0.99  res_clause_to_clause_subsumption:       2740
% 3.10/0.99  res_orphan_elimination:                 0
% 3.10/0.99  res_tautology_del:                      5
% 3.10/0.99  res_num_eq_res_simplified:              1
% 3.10/0.99  res_num_sel_changes:                    0
% 3.10/0.99  res_moves_from_active_to_pass:          0
% 3.10/0.99  
% 3.10/0.99  ------ Superposition
% 3.10/0.99  
% 3.10/0.99  sup_time_total:                         0.
% 3.10/0.99  sup_time_generating:                    0.
% 3.10/0.99  sup_time_sim_full:                      0.
% 3.10/0.99  sup_time_sim_immed:                     0.
% 3.10/0.99  
% 3.10/0.99  sup_num_of_clauses:                     310
% 3.10/0.99  sup_num_in_active:                      50
% 3.10/0.99  sup_num_in_passive:                     260
% 3.10/0.99  sup_num_of_loops:                       71
% 3.10/0.99  sup_fw_superposition:                   878
% 3.10/0.99  sup_bw_superposition:                   661
% 3.10/0.99  sup_immediate_simplified:               1031
% 3.10/0.99  sup_given_eliminated:                   11
% 3.10/0.99  comparisons_done:                       0
% 3.10/0.99  comparisons_avoided:                    0
% 3.10/0.99  
% 3.10/0.99  ------ Simplifications
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  sim_fw_subset_subsumed:                 0
% 3.10/0.99  sim_bw_subset_subsumed:                 0
% 3.10/0.99  sim_fw_subsumed:                        172
% 3.10/0.99  sim_bw_subsumed:                        26
% 3.10/0.99  sim_fw_subsumption_res:                 0
% 3.10/0.99  sim_bw_subsumption_res:                 0
% 3.10/0.99  sim_tautology_del:                      0
% 3.10/0.99  sim_eq_tautology_del:                   389
% 3.10/0.99  sim_eq_res_simp:                        0
% 3.10/0.99  sim_fw_demodulated:                     828
% 3.10/0.99  sim_bw_demodulated:                     31
% 3.10/0.99  sim_light_normalised:                   440
% 3.10/0.99  sim_joinable_taut:                      0
% 3.10/0.99  sim_joinable_simp:                      0
% 3.10/0.99  sim_ac_normalised:                      0
% 3.10/0.99  sim_smt_subsumption:                    0
% 3.10/0.99  
%------------------------------------------------------------------------------
