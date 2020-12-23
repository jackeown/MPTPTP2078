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
% DateTime   : Thu Dec  3 11:23:50 EST 2020

% Result     : Theorem 27.75s
% Output     : CNFRefutation 27.75s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 859 expanded)
%              Number of clauses        :   68 ( 302 expanded)
%              Number of leaves         :   17 ( 208 expanded)
%              Depth                    :   24
%              Number of atoms          :  156 (1497 expanded)
%              Number of equality atoms :  123 (1028 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f25])).

fof(f43,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f44,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f45,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_82,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) = k1_xboole_0
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_14])).

cnf(c_83,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_82])).

cnf(c_122,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_83])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_105,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_18,c_10,c_0])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_166,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_5])).

cnf(c_3828,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_105,c_166])).

cnf(c_4036,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_122,c_3828])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_94,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_95,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_94])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_276,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_95,c_9])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_315,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_276,c_6])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_114,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_6])).

cnf(c_12,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_377,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_114,c_12])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_106,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0])).

cnf(c_262,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_106,c_5])).

cnf(c_402,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_377,c_6,c_262])).

cnf(c_1062,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_315,c_402])).

cnf(c_325,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_105,c_10])).

cnf(c_455,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_325,c_0])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_89,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_90,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_89])).

cnf(c_161,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_90,c_8])).

cnf(c_163,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_114,c_8])).

cnf(c_172,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_163,c_83])).

cnf(c_174,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_161,c_172])).

cnf(c_515,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_455,c_174])).

cnf(c_127,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_90,c_5])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_133,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k4_xboole_0(sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_127,c_3])).

cnf(c_201,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_133,c_0])).

cnf(c_527,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_515,c_201])).

cnf(c_216,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK3,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_174])).

cnf(c_275,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_90,c_9])).

cnf(c_316,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_275,c_6])).

cnf(c_528,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_527,c_105,c_216,c_316])).

cnf(c_3814,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_528,c_166])).

cnf(c_3971,plain,
    ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3814,c_316])).

cnf(c_3972,plain,
    ( k2_xboole_0(sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_3971,c_3])).

cnf(c_3997,plain,
    ( k2_xboole_0(sK3,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_3972,c_0])).

cnf(c_4075,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_4036,c_1062,c_3997])).

cnf(c_4076,plain,
    ( sK0 = sK3 ),
    inference(demodulation,[status(thm)],[c_4075,c_3])).

cnf(c_4267,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_4076,c_315])).

cnf(c_7,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_139,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_105,c_7])).

cnf(c_4274,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_4076,c_139])).

cnf(c_138,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_2560,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_138,c_138,c_402])).

cnf(c_2613,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_316,c_2560])).

cnf(c_4277,plain,
    ( k4_xboole_0(sK2,sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4274,c_2613])).

cnf(c_4278,plain,
    ( sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_4267,c_4277])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_91005,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_4278,c_15])).

cnf(c_91006,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_91005])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 27.75/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.75/4.00  
% 27.75/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.75/4.00  
% 27.75/4.00  ------  iProver source info
% 27.75/4.00  
% 27.75/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.75/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.75/4.00  git: non_committed_changes: false
% 27.75/4.00  git: last_make_outside_of_git: false
% 27.75/4.00  
% 27.75/4.00  ------ 
% 27.75/4.00  
% 27.75/4.00  ------ Input Options
% 27.75/4.00  
% 27.75/4.00  --out_options                           all
% 27.75/4.00  --tptp_safe_out                         true
% 27.75/4.00  --problem_path                          ""
% 27.75/4.00  --include_path                          ""
% 27.75/4.00  --clausifier                            res/vclausify_rel
% 27.75/4.00  --clausifier_options                    --mode clausify
% 27.75/4.00  --stdin                                 false
% 27.75/4.00  --stats_out                             all
% 27.75/4.00  
% 27.75/4.00  ------ General Options
% 27.75/4.00  
% 27.75/4.00  --fof                                   false
% 27.75/4.00  --time_out_real                         305.
% 27.75/4.00  --time_out_virtual                      -1.
% 27.75/4.00  --symbol_type_check                     false
% 27.75/4.00  --clausify_out                          false
% 27.75/4.00  --sig_cnt_out                           false
% 27.75/4.00  --trig_cnt_out                          false
% 27.75/4.00  --trig_cnt_out_tolerance                1.
% 27.75/4.00  --trig_cnt_out_sk_spl                   false
% 27.75/4.00  --abstr_cl_out                          false
% 27.75/4.00  
% 27.75/4.00  ------ Global Options
% 27.75/4.00  
% 27.75/4.00  --schedule                              default
% 27.75/4.00  --add_important_lit                     false
% 27.75/4.00  --prop_solver_per_cl                    1000
% 27.75/4.00  --min_unsat_core                        false
% 27.75/4.00  --soft_assumptions                      false
% 27.75/4.00  --soft_lemma_size                       3
% 27.75/4.00  --prop_impl_unit_size                   0
% 27.75/4.00  --prop_impl_unit                        []
% 27.75/4.00  --share_sel_clauses                     true
% 27.75/4.00  --reset_solvers                         false
% 27.75/4.00  --bc_imp_inh                            [conj_cone]
% 27.75/4.00  --conj_cone_tolerance                   3.
% 27.75/4.00  --extra_neg_conj                        none
% 27.75/4.00  --large_theory_mode                     true
% 27.75/4.00  --prolific_symb_bound                   200
% 27.75/4.00  --lt_threshold                          2000
% 27.75/4.00  --clause_weak_htbl                      true
% 27.75/4.00  --gc_record_bc_elim                     false
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing Options
% 27.75/4.00  
% 27.75/4.00  --preprocessing_flag                    true
% 27.75/4.00  --time_out_prep_mult                    0.1
% 27.75/4.00  --splitting_mode                        input
% 27.75/4.00  --splitting_grd                         true
% 27.75/4.00  --splitting_cvd                         false
% 27.75/4.00  --splitting_cvd_svl                     false
% 27.75/4.00  --splitting_nvd                         32
% 27.75/4.00  --sub_typing                            true
% 27.75/4.00  --prep_gs_sim                           true
% 27.75/4.00  --prep_unflatten                        true
% 27.75/4.00  --prep_res_sim                          true
% 27.75/4.00  --prep_upred                            true
% 27.75/4.00  --prep_sem_filter                       exhaustive
% 27.75/4.00  --prep_sem_filter_out                   false
% 27.75/4.00  --pred_elim                             true
% 27.75/4.00  --res_sim_input                         true
% 27.75/4.00  --eq_ax_congr_red                       true
% 27.75/4.00  --pure_diseq_elim                       true
% 27.75/4.00  --brand_transform                       false
% 27.75/4.00  --non_eq_to_eq                          false
% 27.75/4.00  --prep_def_merge                        true
% 27.75/4.00  --prep_def_merge_prop_impl              false
% 27.75/4.00  --prep_def_merge_mbd                    true
% 27.75/4.00  --prep_def_merge_tr_red                 false
% 27.75/4.00  --prep_def_merge_tr_cl                  false
% 27.75/4.00  --smt_preprocessing                     true
% 27.75/4.00  --smt_ac_axioms                         fast
% 27.75/4.00  --preprocessed_out                      false
% 27.75/4.00  --preprocessed_stats                    false
% 27.75/4.00  
% 27.75/4.00  ------ Abstraction refinement Options
% 27.75/4.00  
% 27.75/4.00  --abstr_ref                             []
% 27.75/4.00  --abstr_ref_prep                        false
% 27.75/4.00  --abstr_ref_until_sat                   false
% 27.75/4.00  --abstr_ref_sig_restrict                funpre
% 27.75/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.75/4.00  --abstr_ref_under                       []
% 27.75/4.00  
% 27.75/4.00  ------ SAT Options
% 27.75/4.00  
% 27.75/4.00  --sat_mode                              false
% 27.75/4.00  --sat_fm_restart_options                ""
% 27.75/4.00  --sat_gr_def                            false
% 27.75/4.00  --sat_epr_types                         true
% 27.75/4.00  --sat_non_cyclic_types                  false
% 27.75/4.00  --sat_finite_models                     false
% 27.75/4.00  --sat_fm_lemmas                         false
% 27.75/4.00  --sat_fm_prep                           false
% 27.75/4.00  --sat_fm_uc_incr                        true
% 27.75/4.00  --sat_out_model                         small
% 27.75/4.00  --sat_out_clauses                       false
% 27.75/4.00  
% 27.75/4.00  ------ QBF Options
% 27.75/4.00  
% 27.75/4.00  --qbf_mode                              false
% 27.75/4.00  --qbf_elim_univ                         false
% 27.75/4.00  --qbf_dom_inst                          none
% 27.75/4.00  --qbf_dom_pre_inst                      false
% 27.75/4.00  --qbf_sk_in                             false
% 27.75/4.00  --qbf_pred_elim                         true
% 27.75/4.00  --qbf_split                             512
% 27.75/4.00  
% 27.75/4.00  ------ BMC1 Options
% 27.75/4.00  
% 27.75/4.00  --bmc1_incremental                      false
% 27.75/4.00  --bmc1_axioms                           reachable_all
% 27.75/4.00  --bmc1_min_bound                        0
% 27.75/4.00  --bmc1_max_bound                        -1
% 27.75/4.00  --bmc1_max_bound_default                -1
% 27.75/4.00  --bmc1_symbol_reachability              true
% 27.75/4.00  --bmc1_property_lemmas                  false
% 27.75/4.00  --bmc1_k_induction                      false
% 27.75/4.00  --bmc1_non_equiv_states                 false
% 27.75/4.00  --bmc1_deadlock                         false
% 27.75/4.00  --bmc1_ucm                              false
% 27.75/4.00  --bmc1_add_unsat_core                   none
% 27.75/4.00  --bmc1_unsat_core_children              false
% 27.75/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.75/4.00  --bmc1_out_stat                         full
% 27.75/4.00  --bmc1_ground_init                      false
% 27.75/4.00  --bmc1_pre_inst_next_state              false
% 27.75/4.00  --bmc1_pre_inst_state                   false
% 27.75/4.00  --bmc1_pre_inst_reach_state             false
% 27.75/4.00  --bmc1_out_unsat_core                   false
% 27.75/4.00  --bmc1_aig_witness_out                  false
% 27.75/4.00  --bmc1_verbose                          false
% 27.75/4.00  --bmc1_dump_clauses_tptp                false
% 27.75/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.75/4.00  --bmc1_dump_file                        -
% 27.75/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.75/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.75/4.00  --bmc1_ucm_extend_mode                  1
% 27.75/4.00  --bmc1_ucm_init_mode                    2
% 27.75/4.00  --bmc1_ucm_cone_mode                    none
% 27.75/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.75/4.00  --bmc1_ucm_relax_model                  4
% 27.75/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.75/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.75/4.00  --bmc1_ucm_layered_model                none
% 27.75/4.00  --bmc1_ucm_max_lemma_size               10
% 27.75/4.00  
% 27.75/4.00  ------ AIG Options
% 27.75/4.00  
% 27.75/4.00  --aig_mode                              false
% 27.75/4.00  
% 27.75/4.00  ------ Instantiation Options
% 27.75/4.00  
% 27.75/4.00  --instantiation_flag                    true
% 27.75/4.00  --inst_sos_flag                         false
% 27.75/4.00  --inst_sos_phase                        true
% 27.75/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.75/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.75/4.00  --inst_lit_sel_side                     num_symb
% 27.75/4.00  --inst_solver_per_active                1400
% 27.75/4.00  --inst_solver_calls_frac                1.
% 27.75/4.00  --inst_passive_queue_type               priority_queues
% 27.75/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.75/4.00  --inst_passive_queues_freq              [25;2]
% 27.75/4.00  --inst_dismatching                      true
% 27.75/4.00  --inst_eager_unprocessed_to_passive     true
% 27.75/4.00  --inst_prop_sim_given                   true
% 27.75/4.00  --inst_prop_sim_new                     false
% 27.75/4.00  --inst_subs_new                         false
% 27.75/4.00  --inst_eq_res_simp                      false
% 27.75/4.00  --inst_subs_given                       false
% 27.75/4.00  --inst_orphan_elimination               true
% 27.75/4.00  --inst_learning_loop_flag               true
% 27.75/4.00  --inst_learning_start                   3000
% 27.75/4.00  --inst_learning_factor                  2
% 27.75/4.00  --inst_start_prop_sim_after_learn       3
% 27.75/4.00  --inst_sel_renew                        solver
% 27.75/4.00  --inst_lit_activity_flag                true
% 27.75/4.00  --inst_restr_to_given                   false
% 27.75/4.00  --inst_activity_threshold               500
% 27.75/4.00  --inst_out_proof                        true
% 27.75/4.00  
% 27.75/4.00  ------ Resolution Options
% 27.75/4.00  
% 27.75/4.00  --resolution_flag                       true
% 27.75/4.00  --res_lit_sel                           adaptive
% 27.75/4.00  --res_lit_sel_side                      none
% 27.75/4.00  --res_ordering                          kbo
% 27.75/4.00  --res_to_prop_solver                    active
% 27.75/4.00  --res_prop_simpl_new                    false
% 27.75/4.00  --res_prop_simpl_given                  true
% 27.75/4.00  --res_passive_queue_type                priority_queues
% 27.75/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.75/4.00  --res_passive_queues_freq               [15;5]
% 27.75/4.00  --res_forward_subs                      full
% 27.75/4.00  --res_backward_subs                     full
% 27.75/4.00  --res_forward_subs_resolution           true
% 27.75/4.00  --res_backward_subs_resolution          true
% 27.75/4.00  --res_orphan_elimination                true
% 27.75/4.00  --res_time_limit                        2.
% 27.75/4.00  --res_out_proof                         true
% 27.75/4.00  
% 27.75/4.00  ------ Superposition Options
% 27.75/4.00  
% 27.75/4.00  --superposition_flag                    true
% 27.75/4.00  --sup_passive_queue_type                priority_queues
% 27.75/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.75/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.75/4.00  --demod_completeness_check              fast
% 27.75/4.00  --demod_use_ground                      true
% 27.75/4.00  --sup_to_prop_solver                    passive
% 27.75/4.00  --sup_prop_simpl_new                    true
% 27.75/4.00  --sup_prop_simpl_given                  true
% 27.75/4.00  --sup_fun_splitting                     false
% 27.75/4.00  --sup_smt_interval                      50000
% 27.75/4.00  
% 27.75/4.00  ------ Superposition Simplification Setup
% 27.75/4.00  
% 27.75/4.00  --sup_indices_passive                   []
% 27.75/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.75/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.75/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.75/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.75/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.75/4.00  --sup_full_bw                           [BwDemod]
% 27.75/4.00  --sup_immed_triv                        [TrivRules]
% 27.75/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.75/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.75/4.00  --sup_immed_bw_main                     []
% 27.75/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.75/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.75/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.75/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.75/4.00  
% 27.75/4.00  ------ Combination Options
% 27.75/4.00  
% 27.75/4.00  --comb_res_mult                         3
% 27.75/4.00  --comb_sup_mult                         2
% 27.75/4.00  --comb_inst_mult                        10
% 27.75/4.00  
% 27.75/4.00  ------ Debug Options
% 27.75/4.00  
% 27.75/4.00  --dbg_backtrace                         false
% 27.75/4.00  --dbg_dump_prop_clauses                 false
% 27.75/4.00  --dbg_dump_prop_clauses_file            -
% 27.75/4.00  --dbg_out_stat                          false
% 27.75/4.00  ------ Parsing...
% 27.75/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.75/4.00  ------ Proving...
% 27.75/4.00  ------ Problem Properties 
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  clauses                                 17
% 27.75/4.00  conjectures                             2
% 27.75/4.00  EPR                                     1
% 27.75/4.00  Horn                                    17
% 27.75/4.00  unary                                   17
% 27.75/4.00  binary                                  0
% 27.75/4.00  lits                                    17
% 27.75/4.00  lits eq                                 17
% 27.75/4.00  fd_pure                                 0
% 27.75/4.00  fd_pseudo                               0
% 27.75/4.00  fd_cond                                 0
% 27.75/4.00  fd_pseudo_cond                          0
% 27.75/4.00  AC symbols                              1
% 27.75/4.00  
% 27.75/4.00  ------ Schedule UEQ
% 27.75/4.00  
% 27.75/4.00  ------ pure equality problem: resolution off 
% 27.75/4.00  
% 27.75/4.00  ------ Option_UEQ Time Limit: Unbounded
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  ------ 
% 27.75/4.00  Current options:
% 27.75/4.00  ------ 
% 27.75/4.00  
% 27.75/4.00  ------ Input Options
% 27.75/4.00  
% 27.75/4.00  --out_options                           all
% 27.75/4.00  --tptp_safe_out                         true
% 27.75/4.00  --problem_path                          ""
% 27.75/4.00  --include_path                          ""
% 27.75/4.00  --clausifier                            res/vclausify_rel
% 27.75/4.00  --clausifier_options                    --mode clausify
% 27.75/4.00  --stdin                                 false
% 27.75/4.00  --stats_out                             all
% 27.75/4.00  
% 27.75/4.00  ------ General Options
% 27.75/4.00  
% 27.75/4.00  --fof                                   false
% 27.75/4.00  --time_out_real                         305.
% 27.75/4.00  --time_out_virtual                      -1.
% 27.75/4.00  --symbol_type_check                     false
% 27.75/4.00  --clausify_out                          false
% 27.75/4.00  --sig_cnt_out                           false
% 27.75/4.00  --trig_cnt_out                          false
% 27.75/4.00  --trig_cnt_out_tolerance                1.
% 27.75/4.00  --trig_cnt_out_sk_spl                   false
% 27.75/4.00  --abstr_cl_out                          false
% 27.75/4.00  
% 27.75/4.00  ------ Global Options
% 27.75/4.00  
% 27.75/4.00  --schedule                              default
% 27.75/4.00  --add_important_lit                     false
% 27.75/4.00  --prop_solver_per_cl                    1000
% 27.75/4.00  --min_unsat_core                        false
% 27.75/4.00  --soft_assumptions                      false
% 27.75/4.00  --soft_lemma_size                       3
% 27.75/4.00  --prop_impl_unit_size                   0
% 27.75/4.00  --prop_impl_unit                        []
% 27.75/4.00  --share_sel_clauses                     true
% 27.75/4.00  --reset_solvers                         false
% 27.75/4.00  --bc_imp_inh                            [conj_cone]
% 27.75/4.00  --conj_cone_tolerance                   3.
% 27.75/4.00  --extra_neg_conj                        none
% 27.75/4.00  --large_theory_mode                     true
% 27.75/4.00  --prolific_symb_bound                   200
% 27.75/4.00  --lt_threshold                          2000
% 27.75/4.00  --clause_weak_htbl                      true
% 27.75/4.00  --gc_record_bc_elim                     false
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing Options
% 27.75/4.00  
% 27.75/4.00  --preprocessing_flag                    true
% 27.75/4.00  --time_out_prep_mult                    0.1
% 27.75/4.00  --splitting_mode                        input
% 27.75/4.00  --splitting_grd                         true
% 27.75/4.00  --splitting_cvd                         false
% 27.75/4.00  --splitting_cvd_svl                     false
% 27.75/4.00  --splitting_nvd                         32
% 27.75/4.00  --sub_typing                            true
% 27.75/4.00  --prep_gs_sim                           true
% 27.75/4.00  --prep_unflatten                        true
% 27.75/4.00  --prep_res_sim                          true
% 27.75/4.00  --prep_upred                            true
% 27.75/4.00  --prep_sem_filter                       exhaustive
% 27.75/4.00  --prep_sem_filter_out                   false
% 27.75/4.00  --pred_elim                             true
% 27.75/4.00  --res_sim_input                         true
% 27.75/4.00  --eq_ax_congr_red                       true
% 27.75/4.00  --pure_diseq_elim                       true
% 27.75/4.00  --brand_transform                       false
% 27.75/4.00  --non_eq_to_eq                          false
% 27.75/4.00  --prep_def_merge                        true
% 27.75/4.00  --prep_def_merge_prop_impl              false
% 27.75/4.00  --prep_def_merge_mbd                    true
% 27.75/4.00  --prep_def_merge_tr_red                 false
% 27.75/4.00  --prep_def_merge_tr_cl                  false
% 27.75/4.00  --smt_preprocessing                     true
% 27.75/4.00  --smt_ac_axioms                         fast
% 27.75/4.00  --preprocessed_out                      false
% 27.75/4.00  --preprocessed_stats                    false
% 27.75/4.00  
% 27.75/4.00  ------ Abstraction refinement Options
% 27.75/4.00  
% 27.75/4.00  --abstr_ref                             []
% 27.75/4.00  --abstr_ref_prep                        false
% 27.75/4.00  --abstr_ref_until_sat                   false
% 27.75/4.00  --abstr_ref_sig_restrict                funpre
% 27.75/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.75/4.00  --abstr_ref_under                       []
% 27.75/4.00  
% 27.75/4.00  ------ SAT Options
% 27.75/4.00  
% 27.75/4.00  --sat_mode                              false
% 27.75/4.00  --sat_fm_restart_options                ""
% 27.75/4.00  --sat_gr_def                            false
% 27.75/4.00  --sat_epr_types                         true
% 27.75/4.00  --sat_non_cyclic_types                  false
% 27.75/4.00  --sat_finite_models                     false
% 27.75/4.00  --sat_fm_lemmas                         false
% 27.75/4.00  --sat_fm_prep                           false
% 27.75/4.00  --sat_fm_uc_incr                        true
% 27.75/4.00  --sat_out_model                         small
% 27.75/4.00  --sat_out_clauses                       false
% 27.75/4.00  
% 27.75/4.00  ------ QBF Options
% 27.75/4.00  
% 27.75/4.00  --qbf_mode                              false
% 27.75/4.00  --qbf_elim_univ                         false
% 27.75/4.00  --qbf_dom_inst                          none
% 27.75/4.00  --qbf_dom_pre_inst                      false
% 27.75/4.00  --qbf_sk_in                             false
% 27.75/4.00  --qbf_pred_elim                         true
% 27.75/4.00  --qbf_split                             512
% 27.75/4.00  
% 27.75/4.00  ------ BMC1 Options
% 27.75/4.00  
% 27.75/4.00  --bmc1_incremental                      false
% 27.75/4.00  --bmc1_axioms                           reachable_all
% 27.75/4.00  --bmc1_min_bound                        0
% 27.75/4.00  --bmc1_max_bound                        -1
% 27.75/4.00  --bmc1_max_bound_default                -1
% 27.75/4.00  --bmc1_symbol_reachability              true
% 27.75/4.00  --bmc1_property_lemmas                  false
% 27.75/4.00  --bmc1_k_induction                      false
% 27.75/4.00  --bmc1_non_equiv_states                 false
% 27.75/4.00  --bmc1_deadlock                         false
% 27.75/4.00  --bmc1_ucm                              false
% 27.75/4.00  --bmc1_add_unsat_core                   none
% 27.75/4.00  --bmc1_unsat_core_children              false
% 27.75/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.75/4.00  --bmc1_out_stat                         full
% 27.75/4.00  --bmc1_ground_init                      false
% 27.75/4.00  --bmc1_pre_inst_next_state              false
% 27.75/4.00  --bmc1_pre_inst_state                   false
% 27.75/4.00  --bmc1_pre_inst_reach_state             false
% 27.75/4.00  --bmc1_out_unsat_core                   false
% 27.75/4.00  --bmc1_aig_witness_out                  false
% 27.75/4.00  --bmc1_verbose                          false
% 27.75/4.00  --bmc1_dump_clauses_tptp                false
% 27.75/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.75/4.00  --bmc1_dump_file                        -
% 27.75/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.75/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.75/4.00  --bmc1_ucm_extend_mode                  1
% 27.75/4.00  --bmc1_ucm_init_mode                    2
% 27.75/4.00  --bmc1_ucm_cone_mode                    none
% 27.75/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.75/4.00  --bmc1_ucm_relax_model                  4
% 27.75/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.75/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.75/4.00  --bmc1_ucm_layered_model                none
% 27.75/4.00  --bmc1_ucm_max_lemma_size               10
% 27.75/4.00  
% 27.75/4.00  ------ AIG Options
% 27.75/4.00  
% 27.75/4.00  --aig_mode                              false
% 27.75/4.00  
% 27.75/4.00  ------ Instantiation Options
% 27.75/4.00  
% 27.75/4.00  --instantiation_flag                    false
% 27.75/4.00  --inst_sos_flag                         false
% 27.75/4.00  --inst_sos_phase                        true
% 27.75/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.75/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.75/4.00  --inst_lit_sel_side                     num_symb
% 27.75/4.00  --inst_solver_per_active                1400
% 27.75/4.00  --inst_solver_calls_frac                1.
% 27.75/4.00  --inst_passive_queue_type               priority_queues
% 27.75/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.75/4.00  --inst_passive_queues_freq              [25;2]
% 27.75/4.00  --inst_dismatching                      true
% 27.75/4.00  --inst_eager_unprocessed_to_passive     true
% 27.75/4.00  --inst_prop_sim_given                   true
% 27.75/4.00  --inst_prop_sim_new                     false
% 27.75/4.00  --inst_subs_new                         false
% 27.75/4.00  --inst_eq_res_simp                      false
% 27.75/4.00  --inst_subs_given                       false
% 27.75/4.00  --inst_orphan_elimination               true
% 27.75/4.00  --inst_learning_loop_flag               true
% 27.75/4.00  --inst_learning_start                   3000
% 27.75/4.00  --inst_learning_factor                  2
% 27.75/4.00  --inst_start_prop_sim_after_learn       3
% 27.75/4.00  --inst_sel_renew                        solver
% 27.75/4.00  --inst_lit_activity_flag                true
% 27.75/4.00  --inst_restr_to_given                   false
% 27.75/4.00  --inst_activity_threshold               500
% 27.75/4.00  --inst_out_proof                        true
% 27.75/4.00  
% 27.75/4.00  ------ Resolution Options
% 27.75/4.00  
% 27.75/4.00  --resolution_flag                       false
% 27.75/4.00  --res_lit_sel                           adaptive
% 27.75/4.00  --res_lit_sel_side                      none
% 27.75/4.00  --res_ordering                          kbo
% 27.75/4.00  --res_to_prop_solver                    active
% 27.75/4.00  --res_prop_simpl_new                    false
% 27.75/4.00  --res_prop_simpl_given                  true
% 27.75/4.00  --res_passive_queue_type                priority_queues
% 27.75/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.75/4.00  --res_passive_queues_freq               [15;5]
% 27.75/4.00  --res_forward_subs                      full
% 27.75/4.00  --res_backward_subs                     full
% 27.75/4.00  --res_forward_subs_resolution           true
% 27.75/4.00  --res_backward_subs_resolution          true
% 27.75/4.00  --res_orphan_elimination                true
% 27.75/4.00  --res_time_limit                        2.
% 27.75/4.00  --res_out_proof                         true
% 27.75/4.00  
% 27.75/4.00  ------ Superposition Options
% 27.75/4.00  
% 27.75/4.00  --superposition_flag                    true
% 27.75/4.00  --sup_passive_queue_type                priority_queues
% 27.75/4.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.75/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.75/4.00  --demod_completeness_check              fast
% 27.75/4.00  --demod_use_ground                      true
% 27.75/4.00  --sup_to_prop_solver                    active
% 27.75/4.00  --sup_prop_simpl_new                    false
% 27.75/4.00  --sup_prop_simpl_given                  false
% 27.75/4.00  --sup_fun_splitting                     true
% 27.75/4.00  --sup_smt_interval                      10000
% 27.75/4.00  
% 27.75/4.00  ------ Superposition Simplification Setup
% 27.75/4.00  
% 27.75/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.75/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.75/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.75/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.75/4.00  --sup_full_triv                         [TrivRules]
% 27.75/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.75/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.75/4.00  --sup_immed_triv                        [TrivRules]
% 27.75/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.75/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.75/4.00  --sup_immed_bw_main                     []
% 27.75/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.75/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.75/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.75/4.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 27.75/4.00  
% 27.75/4.00  ------ Combination Options
% 27.75/4.00  
% 27.75/4.00  --comb_res_mult                         1
% 27.75/4.00  --comb_sup_mult                         1
% 27.75/4.00  --comb_inst_mult                        1000000
% 27.75/4.00  
% 27.75/4.00  ------ Debug Options
% 27.75/4.00  
% 27.75/4.00  --dbg_backtrace                         false
% 27.75/4.00  --dbg_dump_prop_clauses                 false
% 27.75/4.00  --dbg_dump_prop_clauses_file            -
% 27.75/4.00  --dbg_out_stat                          false
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  ------ Proving...
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  % SZS status Theorem for theBenchmark.p
% 27.75/4.00  
% 27.75/4.00   Resolution empty clause
% 27.75/4.00  
% 27.75/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.75/4.00  
% 27.75/4.00  fof(f1,axiom,(
% 27.75/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f27,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f1])).
% 27.75/4.00  
% 27.75/4.00  fof(f3,axiom,(
% 27.75/4.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f19,plain,(
% 27.75/4.00    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 27.75/4.00    inference(unused_predicate_definition_removal,[],[f3])).
% 27.75/4.00  
% 27.75/4.00  fof(f22,plain,(
% 27.75/4.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 27.75/4.00    inference(ennf_transformation,[],[f19])).
% 27.75/4.00  
% 27.75/4.00  fof(f29,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f22])).
% 27.75/4.00  
% 27.75/4.00  fof(f16,axiom,(
% 27.75/4.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f42,plain,(
% 27.75/4.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f16])).
% 27.75/4.00  
% 27.75/4.00  fof(f17,conjecture,(
% 27.75/4.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f18,negated_conjecture,(
% 27.75/4.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 27.75/4.00    inference(negated_conjecture,[],[f17])).
% 27.75/4.00  
% 27.75/4.00  fof(f23,plain,(
% 27.75/4.00    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 27.75/4.00    inference(ennf_transformation,[],[f18])).
% 27.75/4.00  
% 27.75/4.00  fof(f24,plain,(
% 27.75/4.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 27.75/4.00    inference(flattening,[],[f23])).
% 27.75/4.00  
% 27.75/4.00  fof(f25,plain,(
% 27.75/4.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 27.75/4.00    introduced(choice_axiom,[])).
% 27.75/4.00  
% 27.75/4.00  fof(f26,plain,(
% 27.75/4.00    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 27.75/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f25])).
% 27.75/4.00  
% 27.75/4.00  fof(f43,plain,(
% 27.75/4.00    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 27.75/4.00    inference(cnf_transformation,[],[f26])).
% 27.75/4.00  
% 27.75/4.00  fof(f12,axiom,(
% 27.75/4.00    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f38,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f12])).
% 27.75/4.00  
% 27.75/4.00  fof(f9,axiom,(
% 27.75/4.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f35,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f9])).
% 27.75/4.00  
% 27.75/4.00  fof(f6,axiom,(
% 27.75/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f32,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f6])).
% 27.75/4.00  
% 27.75/4.00  fof(f2,axiom,(
% 27.75/4.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f20,plain,(
% 27.75/4.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.75/4.00    inference(unused_predicate_definition_removal,[],[f2])).
% 27.75/4.00  
% 27.75/4.00  fof(f21,plain,(
% 27.75/4.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 27.75/4.00    inference(ennf_transformation,[],[f20])).
% 27.75/4.00  
% 27.75/4.00  fof(f28,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f21])).
% 27.75/4.00  
% 27.75/4.00  fof(f11,axiom,(
% 27.75/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f37,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f11])).
% 27.75/4.00  
% 27.75/4.00  fof(f47,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 27.75/4.00    inference(definition_unfolding,[],[f28,f37])).
% 27.75/4.00  
% 27.75/4.00  fof(f44,plain,(
% 27.75/4.00    r1_xboole_0(sK2,sK0)),
% 27.75/4.00    inference(cnf_transformation,[],[f26])).
% 27.75/4.00  
% 27.75/4.00  fof(f10,axiom,(
% 27.75/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f36,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f10])).
% 27.75/4.00  
% 27.75/4.00  fof(f49,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.75/4.00    inference(definition_unfolding,[],[f36,f37])).
% 27.75/4.00  
% 27.75/4.00  fof(f7,axiom,(
% 27.75/4.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f33,plain,(
% 27.75/4.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.75/4.00    inference(cnf_transformation,[],[f7])).
% 27.75/4.00  
% 27.75/4.00  fof(f5,axiom,(
% 27.75/4.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f31,plain,(
% 27.75/4.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.75/4.00    inference(cnf_transformation,[],[f5])).
% 27.75/4.00  
% 27.75/4.00  fof(f48,plain,(
% 27.75/4.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 27.75/4.00    inference(definition_unfolding,[],[f31,f37])).
% 27.75/4.00  
% 27.75/4.00  fof(f14,axiom,(
% 27.75/4.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f40,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f14])).
% 27.75/4.00  
% 27.75/4.00  fof(f51,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 27.75/4.00    inference(definition_unfolding,[],[f40,f37])).
% 27.75/4.00  
% 27.75/4.00  fof(f13,axiom,(
% 27.75/4.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f39,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 27.75/4.00    inference(cnf_transformation,[],[f13])).
% 27.75/4.00  
% 27.75/4.00  fof(f50,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 27.75/4.00    inference(definition_unfolding,[],[f39,f37])).
% 27.75/4.00  
% 27.75/4.00  fof(f45,plain,(
% 27.75/4.00    r1_xboole_0(sK3,sK1)),
% 27.75/4.00    inference(cnf_transformation,[],[f26])).
% 27.75/4.00  
% 27.75/4.00  fof(f4,axiom,(
% 27.75/4.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f30,plain,(
% 27.75/4.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.75/4.00    inference(cnf_transformation,[],[f4])).
% 27.75/4.00  
% 27.75/4.00  fof(f8,axiom,(
% 27.75/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f34,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f8])).
% 27.75/4.00  
% 27.75/4.00  fof(f46,plain,(
% 27.75/4.00    sK1 != sK2),
% 27.75/4.00    inference(cnf_transformation,[],[f26])).
% 27.75/4.00  
% 27.75/4.00  cnf(c_0,plain,
% 27.75/4.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.75/4.00      inference(cnf_transformation,[],[f27]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_2,plain,
% 27.75/4.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.75/4.00      inference(cnf_transformation,[],[f29]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_14,plain,
% 27.75/4.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.75/4.00      inference(cnf_transformation,[],[f42]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_82,plain,
% 27.75/4.00      ( X0 != X1
% 27.75/4.00      | k4_xboole_0(X1,X2) = k1_xboole_0
% 27.75/4.00      | k2_xboole_0(X0,X3) != X2 ),
% 27.75/4.00      inference(resolution_lifted,[status(thm)],[c_2,c_14]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_83,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.75/4.00      inference(unflattening,[status(thm)],[c_82]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_122,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_0,c_83]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_18,negated_conjecture,
% 27.75/4.00      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 27.75/4.00      inference(cnf_transformation,[],[f43]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_10,plain,
% 27.75/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.75/4.00      inference(cnf_transformation,[],[f38]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_105,negated_conjecture,
% 27.75/4.00      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 27.75/4.00      inference(theory_normalisation,[status(thm)],[c_18,c_10,c_0]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_8,plain,
% 27.75/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.75/4.00      inference(cnf_transformation,[],[f35]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_5,plain,
% 27.75/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.75/4.00      inference(cnf_transformation,[],[f32]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_166,plain,
% 27.75/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_8,c_5]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_3828,plain,
% 27.75/4.00      ( k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_105,c_166]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4036,plain,
% 27.75/4.00      ( k2_xboole_0(sK3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_122,c_3828]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_1,plain,
% 27.75/4.00      ( ~ r1_xboole_0(X0,X1)
% 27.75/4.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.75/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_17,negated_conjecture,
% 27.75/4.00      ( r1_xboole_0(sK2,sK0) ),
% 27.75/4.00      inference(cnf_transformation,[],[f44]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_94,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 27.75/4.00      | sK0 != X1
% 27.75/4.00      | sK2 != X0 ),
% 27.75/4.00      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_95,plain,
% 27.75/4.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 27.75/4.00      inference(unflattening,[status(thm)],[c_94]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_9,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.75/4.00      inference(cnf_transformation,[],[f49]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_276,plain,
% 27.75/4.00      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_95,c_9]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_6,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.75/4.00      inference(cnf_transformation,[],[f33]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_315,plain,
% 27.75/4.00      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_276,c_6]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.75/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_114,plain,
% 27.75/4.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.75/4.00      inference(light_normalisation,[status(thm)],[c_4,c_6]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_12,plain,
% 27.75/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.75/4.00      inference(cnf_transformation,[],[f51]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_377,plain,
% 27.75/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_114,c_12]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_11,plain,
% 27.75/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 27.75/4.00      inference(cnf_transformation,[],[f50]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_106,plain,
% 27.75/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 27.75/4.00      inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_262,plain,
% 27.75/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_106,c_5]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_402,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 27.75/4.00      inference(light_normalisation,[status(thm)],[c_377,c_6,c_262]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_1062,plain,
% 27.75/4.00      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_315,c_402]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_325,plain,
% 27.75/4.00      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_105,c_10]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_455,plain,
% 27.75/4.00      ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_325,c_0]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_16,negated_conjecture,
% 27.75/4.00      ( r1_xboole_0(sK3,sK1) ),
% 27.75/4.00      inference(cnf_transformation,[],[f45]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_89,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 27.75/4.00      | sK3 != X0
% 27.75/4.00      | sK1 != X1 ),
% 27.75/4.00      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_90,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 27.75/4.00      inference(unflattening,[status(thm)],[c_89]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_161,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_90,c_8]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_163,plain,
% 27.75/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_114,c_8]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_172,plain,
% 27.75/4.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.75/4.00      inference(light_normalisation,[status(thm)],[c_163,c_83]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_174,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k1_xboole_0 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_161,c_172]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_515,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) = k1_xboole_0 ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_455,c_174]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_127,plain,
% 27.75/4.00      ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_90,c_5]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_3,plain,
% 27.75/4.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.75/4.00      inference(cnf_transformation,[],[f30]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_133,plain,
% 27.75/4.00      ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k4_xboole_0(sK3,sK1) ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_127,c_3]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_201,plain,
% 27.75/4.00      ( k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(sK3,sK1) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_133,c_0]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_527,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK1))) = k1_xboole_0 ),
% 27.75/4.00      inference(light_normalisation,[status(thm)],[c_515,c_201]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_216,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK3,sK1))) = k1_xboole_0 ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_0,c_174]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_275,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_90,c_9]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_316,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_275,c_6]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_528,plain,
% 27.75/4.00      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_527,c_105,c_216,c_316]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_3814,plain,
% 27.75/4.00      ( k2_xboole_0(sK0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_528,c_166]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_3971,plain,
% 27.75/4.00      ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
% 27.75/4.00      inference(light_normalisation,[status(thm)],[c_3814,c_316]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_3972,plain,
% 27.75/4.00      ( k2_xboole_0(sK0,sK3) = sK0 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_3971,c_3]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_3997,plain,
% 27.75/4.00      ( k2_xboole_0(sK3,sK0) = sK0 ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_3972,c_0]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4075,plain,
% 27.75/4.00      ( k2_xboole_0(sK3,k1_xboole_0) = sK0 ),
% 27.75/4.00      inference(light_normalisation,[status(thm)],[c_4036,c_1062,c_3997]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4076,plain,
% 27.75/4.00      ( sK0 = sK3 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_4075,c_3]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4267,plain,
% 27.75/4.00      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_4076,c_315]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_7,plain,
% 27.75/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 27.75/4.00      inference(cnf_transformation,[],[f34]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_139,plain,
% 27.75/4.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_105,c_7]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4274,plain,
% 27.75/4.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = k4_xboole_0(sK2,sK3) ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_4076,c_139]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_138,plain,
% 27.75/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_2560,plain,
% 27.75/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 27.75/4.00      inference(light_normalisation,[status(thm)],[c_138,c_138,c_402]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_2613,plain,
% 27.75/4.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = sK1 ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_316,c_2560]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4277,plain,
% 27.75/4.00      ( k4_xboole_0(sK2,sK3) = sK1 ),
% 27.75/4.00      inference(light_normalisation,[status(thm)],[c_4274,c_2613]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4278,plain,
% 27.75/4.00      ( sK2 = sK1 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_4267,c_4277]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_15,negated_conjecture,
% 27.75/4.00      ( sK1 != sK2 ),
% 27.75/4.00      inference(cnf_transformation,[],[f46]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_91005,plain,
% 27.75/4.00      ( sK1 != sK1 ),
% 27.75/4.00      inference(demodulation,[status(thm)],[c_4278,c_15]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_91006,plain,
% 27.75/4.00      ( $false ),
% 27.75/4.00      inference(equality_resolution_simp,[status(thm)],[c_91005]) ).
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.75/4.00  
% 27.75/4.00  ------                               Statistics
% 27.75/4.00  
% 27.75/4.00  ------ General
% 27.75/4.00  
% 27.75/4.00  abstr_ref_over_cycles:                  0
% 27.75/4.00  abstr_ref_under_cycles:                 0
% 27.75/4.00  gc_basic_clause_elim:                   0
% 27.75/4.00  forced_gc_time:                         0
% 27.75/4.00  parsing_time:                           0.011
% 27.75/4.00  unif_index_cands_time:                  0.
% 27.75/4.00  unif_index_add_time:                    0.
% 27.75/4.00  orderings_time:                         0.
% 27.75/4.00  out_proof_time:                         0.007
% 27.75/4.00  total_time:                             3.484
% 27.75/4.00  num_of_symbols:                         40
% 27.75/4.00  num_of_terms:                           189505
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing
% 27.75/4.00  
% 27.75/4.00  num_of_splits:                          0
% 27.75/4.00  num_of_split_atoms:                     0
% 27.75/4.00  num_of_reused_defs:                     0
% 27.75/4.00  num_eq_ax_congr_red:                    1
% 27.75/4.00  num_of_sem_filtered_clauses:            0
% 27.75/4.00  num_of_subtypes:                        0
% 27.75/4.00  monotx_restored_types:                  0
% 27.75/4.00  sat_num_of_epr_types:                   0
% 27.75/4.00  sat_num_of_non_cyclic_types:            0
% 27.75/4.00  sat_guarded_non_collapsed_types:        0
% 27.75/4.00  num_pure_diseq_elim:                    0
% 27.75/4.00  simp_replaced_by:                       0
% 27.75/4.00  res_preprocessed:                       57
% 27.75/4.00  prep_upred:                             0
% 27.75/4.00  prep_unflattend:                        6
% 27.75/4.00  smt_new_axioms:                         0
% 27.75/4.00  pred_elim_cands:                        0
% 27.75/4.00  pred_elim:                              2
% 27.75/4.00  pred_elim_cl:                           2
% 27.75/4.00  pred_elim_cycles:                       3
% 27.75/4.00  merged_defs:                            0
% 27.75/4.00  merged_defs_ncl:                        0
% 27.75/4.00  bin_hyper_res:                          0
% 27.75/4.00  prep_cycles:                            3
% 27.75/4.00  pred_elim_time:                         0.001
% 27.75/4.00  splitting_time:                         0.
% 27.75/4.00  sem_filter_time:                        0.
% 27.75/4.00  monotx_time:                            0.
% 27.75/4.00  subtype_inf_time:                       0.
% 27.75/4.00  
% 27.75/4.00  ------ Problem properties
% 27.75/4.00  
% 27.75/4.00  clauses:                                17
% 27.75/4.00  conjectures:                            2
% 27.75/4.00  epr:                                    1
% 27.75/4.00  horn:                                   17
% 27.75/4.00  ground:                                 4
% 27.75/4.00  unary:                                  17
% 27.75/4.00  binary:                                 0
% 27.75/4.00  lits:                                   17
% 27.75/4.00  lits_eq:                                17
% 27.75/4.00  fd_pure:                                0
% 27.75/4.00  fd_pseudo:                              0
% 27.75/4.00  fd_cond:                                0
% 27.75/4.00  fd_pseudo_cond:                         0
% 27.75/4.00  ac_symbols:                             1
% 27.75/4.00  
% 27.75/4.00  ------ Propositional Solver
% 27.75/4.00  
% 27.75/4.00  prop_solver_calls:                      17
% 27.75/4.00  prop_fast_solver_calls:                 133
% 27.75/4.00  smt_solver_calls:                       0
% 27.75/4.00  smt_fast_solver_calls:                  0
% 27.75/4.00  prop_num_of_clauses:                    622
% 27.75/4.00  prop_preprocess_simplified:             821
% 27.75/4.00  prop_fo_subsumed:                       0
% 27.75/4.00  prop_solver_time:                       0.
% 27.75/4.00  smt_solver_time:                        0.
% 27.75/4.00  smt_fast_solver_time:                   0.
% 27.75/4.00  prop_fast_solver_time:                  0.
% 27.75/4.00  prop_unsat_core_time:                   0.
% 27.75/4.00  
% 27.75/4.00  ------ QBF
% 27.75/4.00  
% 27.75/4.00  qbf_q_res:                              0
% 27.75/4.00  qbf_num_tautologies:                    0
% 27.75/4.00  qbf_prep_cycles:                        0
% 27.75/4.00  
% 27.75/4.00  ------ BMC1
% 27.75/4.00  
% 27.75/4.00  bmc1_current_bound:                     -1
% 27.75/4.00  bmc1_last_solved_bound:                 -1
% 27.75/4.00  bmc1_unsat_core_size:                   -1
% 27.75/4.00  bmc1_unsat_core_parents_size:           -1
% 27.75/4.00  bmc1_merge_next_fun:                    0
% 27.75/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.75/4.00  
% 27.75/4.00  ------ Instantiation
% 27.75/4.00  
% 27.75/4.00  inst_num_of_clauses:                    0
% 27.75/4.00  inst_num_in_passive:                    0
% 27.75/4.00  inst_num_in_active:                     0
% 27.75/4.00  inst_num_in_unprocessed:                0
% 27.75/4.00  inst_num_of_loops:                      0
% 27.75/4.00  inst_num_of_learning_restarts:          0
% 27.75/4.00  inst_num_moves_active_passive:          0
% 27.75/4.00  inst_lit_activity:                      0
% 27.75/4.00  inst_lit_activity_moves:                0
% 27.75/4.00  inst_num_tautologies:                   0
% 27.75/4.00  inst_num_prop_implied:                  0
% 27.75/4.00  inst_num_existing_simplified:           0
% 27.75/4.00  inst_num_eq_res_simplified:             0
% 27.75/4.00  inst_num_child_elim:                    0
% 27.75/4.00  inst_num_of_dismatching_blockings:      0
% 27.75/4.00  inst_num_of_non_proper_insts:           0
% 27.75/4.00  inst_num_of_duplicates:                 0
% 27.75/4.00  inst_inst_num_from_inst_to_res:         0
% 27.75/4.00  inst_dismatching_checking_time:         0.
% 27.75/4.00  
% 27.75/4.00  ------ Resolution
% 27.75/4.00  
% 27.75/4.00  res_num_of_clauses:                     0
% 27.75/4.00  res_num_in_passive:                     0
% 27.75/4.00  res_num_in_active:                      0
% 27.75/4.00  res_num_of_loops:                       60
% 27.75/4.00  res_forward_subset_subsumed:            0
% 27.75/4.00  res_backward_subset_subsumed:           0
% 27.75/4.00  res_forward_subsumed:                   0
% 27.75/4.00  res_backward_subsumed:                  0
% 27.75/4.00  res_forward_subsumption_resolution:     0
% 27.75/4.00  res_backward_subsumption_resolution:    0
% 27.75/4.00  res_clause_to_clause_subsumption:       277523
% 27.75/4.00  res_orphan_elimination:                 0
% 27.75/4.00  res_tautology_del:                      0
% 27.75/4.00  res_num_eq_res_simplified:              0
% 27.75/4.00  res_num_sel_changes:                    0
% 27.75/4.00  res_moves_from_active_to_pass:          0
% 27.75/4.00  
% 27.75/4.00  ------ Superposition
% 27.75/4.00  
% 27.75/4.00  sup_time_total:                         0.
% 27.75/4.00  sup_time_generating:                    0.
% 27.75/4.00  sup_time_sim_full:                      0.
% 27.75/4.00  sup_time_sim_immed:                     0.
% 27.75/4.00  
% 27.75/4.00  sup_num_of_clauses:                     11094
% 27.75/4.00  sup_num_in_active:                      235
% 27.75/4.00  sup_num_in_passive:                     10859
% 27.75/4.00  sup_num_of_loops:                       336
% 27.75/4.00  sup_fw_superposition:                   27686
% 27.75/4.00  sup_bw_superposition:                   19789
% 27.75/4.00  sup_immediate_simplified:               33625
% 27.75/4.00  sup_given_eliminated:                   10
% 27.75/4.00  comparisons_done:                       0
% 27.75/4.00  comparisons_avoided:                    0
% 27.75/4.00  
% 27.75/4.00  ------ Simplifications
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  sim_fw_subset_subsumed:                 0
% 27.75/4.00  sim_bw_subset_subsumed:                 0
% 27.75/4.00  sim_fw_subsumed:                        4170
% 27.75/4.00  sim_bw_subsumed:                        304
% 27.75/4.00  sim_fw_subsumption_res:                 0
% 27.75/4.00  sim_bw_subsumption_res:                 0
% 27.75/4.00  sim_tautology_del:                      0
% 27.75/4.00  sim_eq_tautology_del:                   9809
% 27.75/4.00  sim_eq_res_simp:                        0
% 27.75/4.00  sim_fw_demodulated:                     30066
% 27.75/4.00  sim_bw_demodulated:                     690
% 27.75/4.00  sim_light_normalised:                   12389
% 27.75/4.00  sim_joinable_taut:                      944
% 27.75/4.00  sim_joinable_simp:                      0
% 27.75/4.00  sim_ac_normalised:                      0
% 27.75/4.00  sim_smt_subsumption:                    0
% 27.75/4.00  
%------------------------------------------------------------------------------
