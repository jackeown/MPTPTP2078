%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:13 EST 2020

% Result     : Timeout 59.04s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   91 ( 396 expanded)
%              Number of clauses        :   51 ( 138 expanded)
%              Number of leaves         :   13 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  129 ( 576 expanded)
%              Number of equality atoms :   84 ( 354 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f29,f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

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
    inference(definition_unfolding,[],[f21,f29])).

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

fof(f34,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

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
    inference(definition_unfolding,[],[f24,f29,f29,f29,f29])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f32,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_181,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_9,c_8])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_65,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_128,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_65,c_11])).

cnf(c_129,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_1028,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_181,c_129])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_403,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_3792,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1028,c_403])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_114,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) = k1_xboole_0
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_115,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_313,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_115])).

cnf(c_1027,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_181,c_181])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_166,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_1032,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_1027,c_166])).

cnf(c_395,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_37230,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1032,c_395])).

cnf(c_37238,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_313,c_37230])).

cnf(c_38097,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_37238,c_7])).

cnf(c_38698,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_38097,c_8])).

cnf(c_165375,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_3792,c_38698])).

cnf(c_166554,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_165375,c_38698])).

cnf(c_166556,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_166554,c_7])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_120,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_121,plain,
    ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_120])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_184,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_4,c_8,c_181])).

cnf(c_2091,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)))) ),
    inference(superposition,[status(thm)],[c_121,c_184])).

cnf(c_2194,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_2091,c_121])).

cnf(c_2195,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_2194,c_395])).

cnf(c_168407,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_166556,c_2195])).

cnf(c_168507,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_168407,c_121])).

cnf(c_3005,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_2195,c_181])).

cnf(c_3007,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3005,c_121])).

cnf(c_3008,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_3007,c_181,c_395])).

cnf(c_168508,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_168507,c_3008])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_63,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_133,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_63,c_13])).

cnf(c_134,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_168508,c_134])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.04/8.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.04/8.05  
% 59.04/8.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.04/8.05  
% 59.04/8.05  ------  iProver source info
% 59.04/8.05  
% 59.04/8.05  git: date: 2020-06-30 10:37:57 +0100
% 59.04/8.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.04/8.05  git: non_committed_changes: false
% 59.04/8.05  git: last_make_outside_of_git: false
% 59.04/8.05  
% 59.04/8.05  ------ 
% 59.04/8.05  ------ Parsing...
% 59.04/8.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.04/8.05  
% 59.04/8.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 59.04/8.05  
% 59.04/8.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.04/8.05  
% 59.04/8.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.04/8.05  ------ Proving...
% 59.04/8.05  ------ Problem Properties 
% 59.04/8.05  
% 59.04/8.05  
% 59.04/8.05  clauses                                 12
% 59.04/8.05  conjectures                             0
% 59.04/8.05  EPR                                     0
% 59.04/8.05  Horn                                    12
% 59.04/8.05  unary                                   12
% 59.04/8.05  binary                                  0
% 59.04/8.05  lits                                    12
% 59.04/8.05  lits eq                                 12
% 59.04/8.05  fd_pure                                 0
% 59.04/8.05  fd_pseudo                               0
% 59.04/8.05  fd_cond                                 0
% 59.04/8.05  fd_pseudo_cond                          0
% 59.04/8.05  AC symbols                              0
% 59.04/8.05  
% 59.04/8.05  ------ Input Options Time Limit: Unbounded
% 59.04/8.05  
% 59.04/8.05  
% 59.04/8.05  ------ 
% 59.04/8.05  Current options:
% 59.04/8.05  ------ 
% 59.04/8.05  
% 59.04/8.05  
% 59.04/8.05  
% 59.04/8.05  
% 59.04/8.05  ------ Proving...
% 59.04/8.05  
% 59.04/8.05  
% 59.04/8.05  % SZS status Theorem for theBenchmark.p
% 59.04/8.05  
% 59.04/8.05  % SZS output start CNFRefutation for theBenchmark.p
% 59.04/8.05  
% 59.04/8.05  fof(f10,axiom,(
% 59.04/8.05    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f30,plain,(
% 59.04/8.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 59.04/8.05    inference(cnf_transformation,[],[f10])).
% 59.04/8.05  
% 59.04/8.05  fof(f9,axiom,(
% 59.04/8.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f29,plain,(
% 59.04/8.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.04/8.05    inference(cnf_transformation,[],[f9])).
% 59.04/8.05  
% 59.04/8.05  fof(f39,plain,(
% 59.04/8.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 59.04/8.05    inference(definition_unfolding,[],[f30,f29,f29])).
% 59.04/8.05  
% 59.04/8.05  fof(f8,axiom,(
% 59.04/8.05    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f28,plain,(
% 59.04/8.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 59.04/8.05    inference(cnf_transformation,[],[f8])).
% 59.04/8.05  
% 59.04/8.05  fof(f2,axiom,(
% 59.04/8.05    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f17,plain,(
% 59.04/8.05    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 59.04/8.05    inference(nnf_transformation,[],[f2])).
% 59.04/8.05  
% 59.04/8.05  fof(f21,plain,(
% 59.04/8.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 59.04/8.05    inference(cnf_transformation,[],[f17])).
% 59.04/8.05  
% 59.04/8.05  fof(f36,plain,(
% 59.04/8.05    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 59.04/8.05    inference(definition_unfolding,[],[f21,f29])).
% 59.04/8.05  
% 59.04/8.05  fof(f12,conjecture,(
% 59.04/8.05    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f13,negated_conjecture,(
% 59.04/8.05    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 59.04/8.05    inference(negated_conjecture,[],[f12])).
% 59.04/8.05  
% 59.04/8.05  fof(f16,plain,(
% 59.04/8.05    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 59.04/8.05    inference(ennf_transformation,[],[f13])).
% 59.04/8.05  
% 59.04/8.05  fof(f18,plain,(
% 59.04/8.05    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 59.04/8.05    introduced(choice_axiom,[])).
% 59.04/8.05  
% 59.04/8.05  fof(f19,plain,(
% 59.04/8.05    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 59.04/8.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 59.04/8.05  
% 59.04/8.05  fof(f34,plain,(
% 59.04/8.05    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 59.04/8.05    inference(cnf_transformation,[],[f19])).
% 59.04/8.05  
% 59.04/8.05  fof(f40,plain,(
% 59.04/8.05    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 59.04/8.05    inference(definition_unfolding,[],[f34,f29])).
% 59.04/8.05  
% 59.04/8.05  fof(f6,axiom,(
% 59.04/8.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f26,plain,(
% 59.04/8.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 59.04/8.05    inference(cnf_transformation,[],[f6])).
% 59.04/8.05  
% 59.04/8.05  fof(f1,axiom,(
% 59.04/8.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f20,plain,(
% 59.04/8.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 59.04/8.05    inference(cnf_transformation,[],[f1])).
% 59.04/8.05  
% 59.04/8.05  fof(f3,axiom,(
% 59.04/8.05    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f14,plain,(
% 59.04/8.05    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 59.04/8.05    inference(unused_predicate_definition_removal,[],[f3])).
% 59.04/8.05  
% 59.04/8.05  fof(f15,plain,(
% 59.04/8.05    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 59.04/8.05    inference(ennf_transformation,[],[f14])).
% 59.04/8.05  
% 59.04/8.05  fof(f23,plain,(
% 59.04/8.05    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 59.04/8.05    inference(cnf_transformation,[],[f15])).
% 59.04/8.05  
% 59.04/8.05  fof(f11,axiom,(
% 59.04/8.05    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f31,plain,(
% 59.04/8.05    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 59.04/8.05    inference(cnf_transformation,[],[f11])).
% 59.04/8.05  
% 59.04/8.05  fof(f5,axiom,(
% 59.04/8.05    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f25,plain,(
% 59.04/8.05    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 59.04/8.05    inference(cnf_transformation,[],[f5])).
% 59.04/8.05  
% 59.04/8.05  fof(f38,plain,(
% 59.04/8.05    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 59.04/8.05    inference(definition_unfolding,[],[f25,f29])).
% 59.04/8.05  
% 59.04/8.05  fof(f7,axiom,(
% 59.04/8.05    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f27,plain,(
% 59.04/8.05    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.04/8.05    inference(cnf_transformation,[],[f7])).
% 59.04/8.05  
% 59.04/8.05  fof(f33,plain,(
% 59.04/8.05    r1_tarski(sK0,sK2)),
% 59.04/8.05    inference(cnf_transformation,[],[f19])).
% 59.04/8.05  
% 59.04/8.05  fof(f4,axiom,(
% 59.04/8.05    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 59.04/8.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.04/8.05  
% 59.04/8.05  fof(f24,plain,(
% 59.04/8.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 59.04/8.05    inference(cnf_transformation,[],[f4])).
% 59.04/8.05  
% 59.04/8.05  fof(f37,plain,(
% 59.04/8.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 59.04/8.05    inference(definition_unfolding,[],[f24,f29,f29,f29,f29])).
% 59.04/8.05  
% 59.04/8.05  fof(f22,plain,(
% 59.04/8.05    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 59.04/8.05    inference(cnf_transformation,[],[f17])).
% 59.04/8.05  
% 59.04/8.05  fof(f35,plain,(
% 59.04/8.05    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.04/8.05    inference(definition_unfolding,[],[f22,f29])).
% 59.04/8.05  
% 59.04/8.05  fof(f32,plain,(
% 59.04/8.05    ~r1_xboole_0(sK0,sK1)),
% 59.04/8.05    inference(cnf_transformation,[],[f19])).
% 59.04/8.05  
% 59.04/8.05  cnf(c_9,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 59.04/8.05      inference(cnf_transformation,[],[f39]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_8,plain,
% 59.04/8.05      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.04/8.05      inference(cnf_transformation,[],[f28]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_181,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 59.04/8.05      inference(demodulation,[status(thm)],[c_9,c_8]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_2,plain,
% 59.04/8.05      ( ~ r1_xboole_0(X0,X1)
% 59.04/8.05      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.04/8.05      inference(cnf_transformation,[],[f36]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_65,plain,
% 59.04/8.05      ( ~ r1_xboole_0(X0,X1)
% 59.04/8.05      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.04/8.05      inference(prop_impl,[status(thm)],[c_2]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_11,negated_conjecture,
% 59.04/8.05      ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 59.04/8.05      inference(cnf_transformation,[],[f40]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_128,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 59.04/8.05      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
% 59.04/8.05      | sK0 != X0 ),
% 59.04/8.05      inference(resolution_lifted,[status(thm)],[c_65,c_11]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_129,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 59.04/8.05      inference(unflattening,[status(thm)],[c_128]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_1028,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_181,c_129]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_6,plain,
% 59.04/8.05      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 59.04/8.05      inference(cnf_transformation,[],[f26]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_403,plain,
% 59.04/8.05      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_3792,plain,
% 59.04/8.05      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_1028,c_403]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_0,plain,
% 59.04/8.05      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 59.04/8.05      inference(cnf_transformation,[],[f20]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_3,plain,
% 59.04/8.05      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 59.04/8.05      inference(cnf_transformation,[],[f23]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_10,plain,
% 59.04/8.05      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 59.04/8.05      inference(cnf_transformation,[],[f31]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_114,plain,
% 59.04/8.05      ( X0 != X1
% 59.04/8.05      | k4_xboole_0(X1,X2) = k1_xboole_0
% 59.04/8.05      | k2_xboole_0(X0,X3) != X2 ),
% 59.04/8.05      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_115,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.04/8.05      inference(unflattening,[status(thm)],[c_114]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_313,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_0,c_115]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_1027,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_181,c_181]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_5,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 59.04/8.05      inference(cnf_transformation,[],[f38]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_7,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.04/8.05      inference(cnf_transformation,[],[f27]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_166,plain,
% 59.04/8.05      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 59.04/8.05      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_1032,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
% 59.04/8.05      inference(light_normalisation,[status(thm)],[c_1027,c_166]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_395,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_37230,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 59.04/8.05      inference(demodulation,[status(thm)],[c_1032,c_395]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_37238,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_313,c_37230]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_38097,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 59.04/8.05      inference(light_normalisation,[status(thm)],[c_37238,c_7]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_38698,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_38097,c_8]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_165375,plain,
% 59.04/8.05      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_3792,c_38698]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_166554,plain,
% 59.04/8.05      ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK2,k1_xboole_0) ),
% 59.04/8.05      inference(demodulation,[status(thm)],[c_165375,c_38698]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_166556,plain,
% 59.04/8.05      ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = sK2 ),
% 59.04/8.05      inference(demodulation,[status(thm)],[c_166554,c_7]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_12,negated_conjecture,
% 59.04/8.05      ( r1_tarski(sK0,sK2) ),
% 59.04/8.05      inference(cnf_transformation,[],[f33]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_120,plain,
% 59.04/8.05      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK2 != X1 | sK0 != X0 ),
% 59.04/8.05      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_121,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 59.04/8.05      inference(unflattening,[status(thm)],[c_120]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_4,plain,
% 59.04/8.05      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 59.04/8.05      inference(cnf_transformation,[],[f37]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_184,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) ),
% 59.04/8.05      inference(demodulation,[status(thm)],[c_4,c_8,c_181]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_2091,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)))) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_121,c_184]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_2194,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0))) ),
% 59.04/8.05      inference(light_normalisation,[status(thm)],[c_2091,c_121]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_2195,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 59.04/8.05      inference(demodulation,[status(thm)],[c_2194,c_395]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_168407,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK0,sK2) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_166556,c_2195]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_168507,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k1_xboole_0 ),
% 59.04/8.05      inference(light_normalisation,[status(thm)],[c_168407,c_121]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_3005,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 59.04/8.05      inference(superposition,[status(thm)],[c_2195,c_181]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_3007,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 59.04/8.05      inference(light_normalisation,[status(thm)],[c_3005,c_121]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_3008,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
% 59.04/8.05      inference(demodulation,[status(thm)],[c_3007,c_181,c_395]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_168508,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 59.04/8.05      inference(demodulation,[status(thm)],[c_168507,c_3008]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_1,plain,
% 59.04/8.05      ( r1_xboole_0(X0,X1)
% 59.04/8.05      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 59.04/8.05      inference(cnf_transformation,[],[f35]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_63,plain,
% 59.04/8.05      ( r1_xboole_0(X0,X1)
% 59.04/8.05      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 59.04/8.05      inference(prop_impl,[status(thm)],[c_1]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_13,negated_conjecture,
% 59.04/8.05      ( ~ r1_xboole_0(sK0,sK1) ),
% 59.04/8.05      inference(cnf_transformation,[],[f32]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_133,plain,
% 59.04/8.05      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 59.04/8.05      | sK1 != X1
% 59.04/8.05      | sK0 != X0 ),
% 59.04/8.05      inference(resolution_lifted,[status(thm)],[c_63,c_13]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(c_134,plain,
% 59.04/8.05      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 59.04/8.05      inference(unflattening,[status(thm)],[c_133]) ).
% 59.04/8.05  
% 59.04/8.05  cnf(contradiction,plain,
% 59.04/8.05      ( $false ),
% 59.04/8.05      inference(minisat,[status(thm)],[c_168508,c_134]) ).
% 59.04/8.05  
% 59.04/8.05  
% 59.04/8.05  % SZS output end CNFRefutation for theBenchmark.p
% 59.04/8.05  
% 59.04/8.05  ------                               Statistics
% 59.04/8.05  
% 59.04/8.05  ------ Selected
% 59.04/8.05  
% 59.04/8.05  total_time:                             7.121
% 59.04/8.05  
%------------------------------------------------------------------------------
