%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:53 EST 2020

% Result     : Theorem 6.78s
% Output     : CNFRefutation 6.78s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 143 expanded)
%              Number of clauses        :   56 (  62 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  201 ( 350 expanded)
%              Number of equality atoms :  116 ( 190 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,
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

fof(f27,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26])).

fof(f44,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f43,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_32657,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1594,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,sK3))
    | r1_tarski(k4_xboole_0(X0,X1),sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14184,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3)
    | ~ r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | sK3 != X1
    | sK1 != X2
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_4200,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),sK3)
    | ~ r1_tarski(k4_xboole_0(X0,X1),sK1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_5543,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK3)
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4200])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_522,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1652,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_522])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_523,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2508,plain,
    ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_523])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_521,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2894,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_521])).

cnf(c_3209,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1652,c_2894])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_520,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4733,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3209,c_520])).

cnf(c_4745,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4733])).

cnf(c_258,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1219,plain,
    ( k4_xboole_0(X0,sK2) = k4_xboole_0(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_3127,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_259,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_772,plain,
    ( X0 != X1
    | k4_xboole_0(X2,sK2) != X1
    | k4_xboole_0(X2,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_1218,plain,
    ( X0 != k4_xboole_0(X1,sK2)
    | k4_xboole_0(X1,sK2) = X0
    | k4_xboole_0(X1,sK2) != k4_xboole_0(X1,sK2) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_2358,plain,
    ( k4_xboole_0(X0,sK2) != k4_xboole_0(X0,sK2)
    | k4_xboole_0(X0,sK2) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_2646,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_518,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_519,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1482,plain,
    ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_519])).

cnf(c_1871,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_518,c_1482])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_104,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_207,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_104,c_15])).

cnf(c_208,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_837,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_208,c_9])).

cnf(c_853,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_837,c_7])).

cnf(c_1887,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1871,c_853])).

cnf(c_642,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_643,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_615,plain,
    ( k4_xboole_0(sK2,sK1) != X0
    | k4_xboole_0(sK1,sK2) != X0
    | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_616,plain,
    ( k4_xboole_0(sK2,sK1) != k1_xboole_0
    | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)
    | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_3,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_609,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK2,sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_13,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32657,c_14184,c_5543,c_4745,c_3127,c_2646,c_1887,c_643,c_616,c_609,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:42:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.78/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/1.53  
% 6.78/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.78/1.53  
% 6.78/1.53  ------  iProver source info
% 6.78/1.53  
% 6.78/1.53  git: date: 2020-06-30 10:37:57 +0100
% 6.78/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.78/1.53  git: non_committed_changes: false
% 6.78/1.53  git: last_make_outside_of_git: false
% 6.78/1.53  
% 6.78/1.53  ------ 
% 6.78/1.53  
% 6.78/1.53  ------ Input Options
% 6.78/1.53  
% 6.78/1.53  --out_options                           all
% 6.78/1.53  --tptp_safe_out                         true
% 6.78/1.53  --problem_path                          ""
% 6.78/1.53  --include_path                          ""
% 6.78/1.53  --clausifier                            res/vclausify_rel
% 6.78/1.53  --clausifier_options                    --mode clausify
% 6.78/1.53  --stdin                                 false
% 6.78/1.53  --stats_out                             all
% 6.78/1.53  
% 6.78/1.53  ------ General Options
% 6.78/1.53  
% 6.78/1.53  --fof                                   false
% 6.78/1.53  --time_out_real                         305.
% 6.78/1.53  --time_out_virtual                      -1.
% 6.78/1.53  --symbol_type_check                     false
% 6.78/1.53  --clausify_out                          false
% 6.78/1.53  --sig_cnt_out                           false
% 6.78/1.53  --trig_cnt_out                          false
% 6.78/1.53  --trig_cnt_out_tolerance                1.
% 6.78/1.53  --trig_cnt_out_sk_spl                   false
% 6.78/1.53  --abstr_cl_out                          false
% 6.78/1.53  
% 6.78/1.53  ------ Global Options
% 6.78/1.53  
% 6.78/1.53  --schedule                              default
% 6.78/1.53  --add_important_lit                     false
% 6.78/1.53  --prop_solver_per_cl                    1000
% 6.78/1.53  --min_unsat_core                        false
% 6.78/1.53  --soft_assumptions                      false
% 6.78/1.53  --soft_lemma_size                       3
% 6.78/1.53  --prop_impl_unit_size                   0
% 6.78/1.53  --prop_impl_unit                        []
% 6.78/1.53  --share_sel_clauses                     true
% 6.78/1.53  --reset_solvers                         false
% 6.78/1.53  --bc_imp_inh                            [conj_cone]
% 6.78/1.53  --conj_cone_tolerance                   3.
% 6.78/1.53  --extra_neg_conj                        none
% 6.78/1.53  --large_theory_mode                     true
% 6.78/1.53  --prolific_symb_bound                   200
% 6.78/1.53  --lt_threshold                          2000
% 6.78/1.53  --clause_weak_htbl                      true
% 6.78/1.53  --gc_record_bc_elim                     false
% 6.78/1.53  
% 6.78/1.53  ------ Preprocessing Options
% 6.78/1.53  
% 6.78/1.53  --preprocessing_flag                    true
% 6.78/1.53  --time_out_prep_mult                    0.1
% 6.78/1.53  --splitting_mode                        input
% 6.78/1.53  --splitting_grd                         true
% 6.78/1.53  --splitting_cvd                         false
% 6.78/1.53  --splitting_cvd_svl                     false
% 6.78/1.53  --splitting_nvd                         32
% 6.78/1.53  --sub_typing                            true
% 6.78/1.53  --prep_gs_sim                           true
% 6.78/1.53  --prep_unflatten                        true
% 6.78/1.53  --prep_res_sim                          true
% 6.78/1.53  --prep_upred                            true
% 6.78/1.53  --prep_sem_filter                       exhaustive
% 6.78/1.53  --prep_sem_filter_out                   false
% 6.78/1.53  --pred_elim                             true
% 6.78/1.53  --res_sim_input                         true
% 6.78/1.53  --eq_ax_congr_red                       true
% 6.78/1.53  --pure_diseq_elim                       true
% 6.78/1.53  --brand_transform                       false
% 6.78/1.53  --non_eq_to_eq                          false
% 6.78/1.53  --prep_def_merge                        true
% 6.78/1.53  --prep_def_merge_prop_impl              false
% 6.78/1.53  --prep_def_merge_mbd                    true
% 6.78/1.53  --prep_def_merge_tr_red                 false
% 6.78/1.53  --prep_def_merge_tr_cl                  false
% 6.78/1.53  --smt_preprocessing                     true
% 6.78/1.53  --smt_ac_axioms                         fast
% 6.78/1.53  --preprocessed_out                      false
% 6.78/1.53  --preprocessed_stats                    false
% 6.78/1.53  
% 6.78/1.53  ------ Abstraction refinement Options
% 6.78/1.53  
% 6.78/1.53  --abstr_ref                             []
% 6.78/1.53  --abstr_ref_prep                        false
% 6.78/1.53  --abstr_ref_until_sat                   false
% 6.78/1.53  --abstr_ref_sig_restrict                funpre
% 6.78/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 6.78/1.53  --abstr_ref_under                       []
% 6.78/1.53  
% 6.78/1.53  ------ SAT Options
% 6.78/1.53  
% 6.78/1.53  --sat_mode                              false
% 6.78/1.53  --sat_fm_restart_options                ""
% 6.78/1.53  --sat_gr_def                            false
% 6.78/1.53  --sat_epr_types                         true
% 6.78/1.53  --sat_non_cyclic_types                  false
% 6.78/1.53  --sat_finite_models                     false
% 6.78/1.53  --sat_fm_lemmas                         false
% 6.78/1.53  --sat_fm_prep                           false
% 6.78/1.53  --sat_fm_uc_incr                        true
% 6.78/1.53  --sat_out_model                         small
% 6.78/1.53  --sat_out_clauses                       false
% 6.78/1.53  
% 6.78/1.53  ------ QBF Options
% 6.78/1.53  
% 6.78/1.53  --qbf_mode                              false
% 6.78/1.53  --qbf_elim_univ                         false
% 6.78/1.53  --qbf_dom_inst                          none
% 6.78/1.53  --qbf_dom_pre_inst                      false
% 6.78/1.53  --qbf_sk_in                             false
% 6.78/1.53  --qbf_pred_elim                         true
% 6.78/1.53  --qbf_split                             512
% 6.78/1.53  
% 6.78/1.53  ------ BMC1 Options
% 6.78/1.53  
% 6.78/1.53  --bmc1_incremental                      false
% 6.78/1.53  --bmc1_axioms                           reachable_all
% 6.78/1.53  --bmc1_min_bound                        0
% 6.78/1.53  --bmc1_max_bound                        -1
% 6.78/1.53  --bmc1_max_bound_default                -1
% 6.78/1.53  --bmc1_symbol_reachability              true
% 6.78/1.53  --bmc1_property_lemmas                  false
% 6.78/1.53  --bmc1_k_induction                      false
% 6.78/1.53  --bmc1_non_equiv_states                 false
% 6.78/1.53  --bmc1_deadlock                         false
% 6.78/1.53  --bmc1_ucm                              false
% 6.78/1.53  --bmc1_add_unsat_core                   none
% 6.78/1.53  --bmc1_unsat_core_children              false
% 6.78/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 6.78/1.53  --bmc1_out_stat                         full
% 6.78/1.53  --bmc1_ground_init                      false
% 6.78/1.53  --bmc1_pre_inst_next_state              false
% 6.78/1.53  --bmc1_pre_inst_state                   false
% 6.78/1.53  --bmc1_pre_inst_reach_state             false
% 6.78/1.53  --bmc1_out_unsat_core                   false
% 6.78/1.53  --bmc1_aig_witness_out                  false
% 6.78/1.53  --bmc1_verbose                          false
% 6.78/1.53  --bmc1_dump_clauses_tptp                false
% 6.78/1.53  --bmc1_dump_unsat_core_tptp             false
% 6.78/1.53  --bmc1_dump_file                        -
% 6.78/1.53  --bmc1_ucm_expand_uc_limit              128
% 6.78/1.53  --bmc1_ucm_n_expand_iterations          6
% 6.78/1.53  --bmc1_ucm_extend_mode                  1
% 6.78/1.53  --bmc1_ucm_init_mode                    2
% 6.78/1.53  --bmc1_ucm_cone_mode                    none
% 6.78/1.53  --bmc1_ucm_reduced_relation_type        0
% 6.78/1.53  --bmc1_ucm_relax_model                  4
% 6.78/1.53  --bmc1_ucm_full_tr_after_sat            true
% 6.78/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 6.78/1.53  --bmc1_ucm_layered_model                none
% 6.78/1.53  --bmc1_ucm_max_lemma_size               10
% 6.78/1.53  
% 6.78/1.53  ------ AIG Options
% 6.78/1.53  
% 6.78/1.53  --aig_mode                              false
% 6.78/1.53  
% 6.78/1.53  ------ Instantiation Options
% 6.78/1.53  
% 6.78/1.53  --instantiation_flag                    true
% 6.78/1.53  --inst_sos_flag                         false
% 6.78/1.53  --inst_sos_phase                        true
% 6.78/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.78/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.78/1.53  --inst_lit_sel_side                     num_symb
% 6.78/1.53  --inst_solver_per_active                1400
% 6.78/1.53  --inst_solver_calls_frac                1.
% 6.78/1.53  --inst_passive_queue_type               priority_queues
% 6.78/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.78/1.53  --inst_passive_queues_freq              [25;2]
% 6.78/1.53  --inst_dismatching                      true
% 6.78/1.53  --inst_eager_unprocessed_to_passive     true
% 6.78/1.53  --inst_prop_sim_given                   true
% 6.78/1.53  --inst_prop_sim_new                     false
% 6.78/1.53  --inst_subs_new                         false
% 6.78/1.53  --inst_eq_res_simp                      false
% 6.78/1.53  --inst_subs_given                       false
% 6.78/1.53  --inst_orphan_elimination               true
% 6.78/1.53  --inst_learning_loop_flag               true
% 6.78/1.53  --inst_learning_start                   3000
% 6.78/1.53  --inst_learning_factor                  2
% 6.78/1.53  --inst_start_prop_sim_after_learn       3
% 6.78/1.53  --inst_sel_renew                        solver
% 6.78/1.53  --inst_lit_activity_flag                true
% 6.78/1.53  --inst_restr_to_given                   false
% 6.78/1.53  --inst_activity_threshold               500
% 6.78/1.53  --inst_out_proof                        true
% 6.78/1.53  
% 6.78/1.53  ------ Resolution Options
% 6.78/1.53  
% 6.78/1.53  --resolution_flag                       true
% 6.78/1.53  --res_lit_sel                           adaptive
% 6.78/1.53  --res_lit_sel_side                      none
% 6.78/1.53  --res_ordering                          kbo
% 6.78/1.53  --res_to_prop_solver                    active
% 6.78/1.53  --res_prop_simpl_new                    false
% 6.78/1.53  --res_prop_simpl_given                  true
% 6.78/1.53  --res_passive_queue_type                priority_queues
% 6.78/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.78/1.53  --res_passive_queues_freq               [15;5]
% 6.78/1.53  --res_forward_subs                      full
% 6.78/1.53  --res_backward_subs                     full
% 6.78/1.53  --res_forward_subs_resolution           true
% 6.78/1.53  --res_backward_subs_resolution          true
% 6.78/1.53  --res_orphan_elimination                true
% 6.78/1.53  --res_time_limit                        2.
% 6.78/1.53  --res_out_proof                         true
% 6.78/1.53  
% 6.78/1.53  ------ Superposition Options
% 6.78/1.53  
% 6.78/1.53  --superposition_flag                    true
% 6.78/1.53  --sup_passive_queue_type                priority_queues
% 6.78/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.78/1.53  --sup_passive_queues_freq               [8;1;4]
% 6.78/1.53  --demod_completeness_check              fast
% 6.78/1.53  --demod_use_ground                      true
% 6.78/1.53  --sup_to_prop_solver                    passive
% 6.78/1.53  --sup_prop_simpl_new                    true
% 6.78/1.53  --sup_prop_simpl_given                  true
% 6.78/1.53  --sup_fun_splitting                     false
% 6.78/1.53  --sup_smt_interval                      50000
% 6.78/1.53  
% 6.78/1.53  ------ Superposition Simplification Setup
% 6.78/1.53  
% 6.78/1.53  --sup_indices_passive                   []
% 6.78/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 6.78/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.53  --sup_full_bw                           [BwDemod]
% 6.78/1.53  --sup_immed_triv                        [TrivRules]
% 6.78/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.78/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.53  --sup_immed_bw_main                     []
% 6.78/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.78/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 6.78/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.78/1.53  
% 6.78/1.53  ------ Combination Options
% 6.78/1.53  
% 6.78/1.53  --comb_res_mult                         3
% 6.78/1.53  --comb_sup_mult                         2
% 6.78/1.53  --comb_inst_mult                        10
% 6.78/1.53  
% 6.78/1.53  ------ Debug Options
% 6.78/1.53  
% 6.78/1.53  --dbg_backtrace                         false
% 6.78/1.53  --dbg_dump_prop_clauses                 false
% 6.78/1.53  --dbg_dump_prop_clauses_file            -
% 6.78/1.53  --dbg_out_stat                          false
% 6.78/1.53  ------ Parsing...
% 6.78/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.78/1.53  
% 6.78/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 6.78/1.53  
% 6.78/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.78/1.53  
% 6.78/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.78/1.53  ------ Proving...
% 6.78/1.53  ------ Problem Properties 
% 6.78/1.53  
% 6.78/1.53  
% 6.78/1.53  clauses                                 17
% 6.78/1.53  conjectures                             2
% 6.78/1.53  EPR                                     3
% 6.78/1.53  Horn                                    17
% 6.78/1.53  unary                                   8
% 6.78/1.53  binary                                  5
% 6.78/1.53  lits                                    31
% 6.78/1.53  lits eq                                 14
% 6.78/1.53  fd_pure                                 0
% 6.78/1.53  fd_pseudo                               0
% 6.78/1.53  fd_cond                                 3
% 6.78/1.53  fd_pseudo_cond                          1
% 6.78/1.53  AC symbols                              0
% 6.78/1.53  
% 6.78/1.53  ------ Schedule dynamic 5 is on 
% 6.78/1.53  
% 6.78/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.78/1.53  
% 6.78/1.53  
% 6.78/1.53  ------ 
% 6.78/1.53  Current options:
% 6.78/1.53  ------ 
% 6.78/1.53  
% 6.78/1.53  ------ Input Options
% 6.78/1.53  
% 6.78/1.53  --out_options                           all
% 6.78/1.53  --tptp_safe_out                         true
% 6.78/1.53  --problem_path                          ""
% 6.78/1.53  --include_path                          ""
% 6.78/1.53  --clausifier                            res/vclausify_rel
% 6.78/1.53  --clausifier_options                    --mode clausify
% 6.78/1.53  --stdin                                 false
% 6.78/1.53  --stats_out                             all
% 6.78/1.53  
% 6.78/1.53  ------ General Options
% 6.78/1.53  
% 6.78/1.53  --fof                                   false
% 6.78/1.53  --time_out_real                         305.
% 6.78/1.53  --time_out_virtual                      -1.
% 6.78/1.53  --symbol_type_check                     false
% 6.78/1.53  --clausify_out                          false
% 6.78/1.53  --sig_cnt_out                           false
% 6.78/1.53  --trig_cnt_out                          false
% 6.78/1.53  --trig_cnt_out_tolerance                1.
% 6.78/1.53  --trig_cnt_out_sk_spl                   false
% 6.78/1.53  --abstr_cl_out                          false
% 6.78/1.53  
% 6.78/1.53  ------ Global Options
% 6.78/1.53  
% 6.78/1.53  --schedule                              default
% 6.78/1.53  --add_important_lit                     false
% 6.78/1.53  --prop_solver_per_cl                    1000
% 6.78/1.53  --min_unsat_core                        false
% 6.78/1.53  --soft_assumptions                      false
% 6.78/1.53  --soft_lemma_size                       3
% 6.78/1.53  --prop_impl_unit_size                   0
% 6.78/1.53  --prop_impl_unit                        []
% 6.78/1.53  --share_sel_clauses                     true
% 6.78/1.53  --reset_solvers                         false
% 6.78/1.53  --bc_imp_inh                            [conj_cone]
% 6.78/1.53  --conj_cone_tolerance                   3.
% 6.78/1.53  --extra_neg_conj                        none
% 6.78/1.53  --large_theory_mode                     true
% 6.78/1.53  --prolific_symb_bound                   200
% 6.78/1.53  --lt_threshold                          2000
% 6.78/1.53  --clause_weak_htbl                      true
% 6.78/1.53  --gc_record_bc_elim                     false
% 6.78/1.53  
% 6.78/1.53  ------ Preprocessing Options
% 6.78/1.53  
% 6.78/1.53  --preprocessing_flag                    true
% 6.78/1.53  --time_out_prep_mult                    0.1
% 6.78/1.53  --splitting_mode                        input
% 6.78/1.53  --splitting_grd                         true
% 6.78/1.53  --splitting_cvd                         false
% 6.78/1.53  --splitting_cvd_svl                     false
% 6.78/1.53  --splitting_nvd                         32
% 6.78/1.53  --sub_typing                            true
% 6.78/1.53  --prep_gs_sim                           true
% 6.78/1.53  --prep_unflatten                        true
% 6.78/1.53  --prep_res_sim                          true
% 6.78/1.53  --prep_upred                            true
% 6.78/1.53  --prep_sem_filter                       exhaustive
% 6.78/1.53  --prep_sem_filter_out                   false
% 6.78/1.53  --pred_elim                             true
% 6.78/1.53  --res_sim_input                         true
% 6.78/1.53  --eq_ax_congr_red                       true
% 6.78/1.53  --pure_diseq_elim                       true
% 6.78/1.53  --brand_transform                       false
% 6.78/1.53  --non_eq_to_eq                          false
% 6.78/1.53  --prep_def_merge                        true
% 6.78/1.53  --prep_def_merge_prop_impl              false
% 6.78/1.53  --prep_def_merge_mbd                    true
% 6.78/1.53  --prep_def_merge_tr_red                 false
% 6.78/1.53  --prep_def_merge_tr_cl                  false
% 6.78/1.53  --smt_preprocessing                     true
% 6.78/1.53  --smt_ac_axioms                         fast
% 6.78/1.53  --preprocessed_out                      false
% 6.78/1.53  --preprocessed_stats                    false
% 6.78/1.53  
% 6.78/1.53  ------ Abstraction refinement Options
% 6.78/1.53  
% 6.78/1.53  --abstr_ref                             []
% 6.78/1.53  --abstr_ref_prep                        false
% 6.78/1.53  --abstr_ref_until_sat                   false
% 6.78/1.53  --abstr_ref_sig_restrict                funpre
% 6.78/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 6.78/1.53  --abstr_ref_under                       []
% 6.78/1.53  
% 6.78/1.53  ------ SAT Options
% 6.78/1.53  
% 6.78/1.53  --sat_mode                              false
% 6.78/1.53  --sat_fm_restart_options                ""
% 6.78/1.53  --sat_gr_def                            false
% 6.78/1.53  --sat_epr_types                         true
% 6.78/1.53  --sat_non_cyclic_types                  false
% 6.78/1.53  --sat_finite_models                     false
% 6.78/1.53  --sat_fm_lemmas                         false
% 6.78/1.53  --sat_fm_prep                           false
% 6.78/1.53  --sat_fm_uc_incr                        true
% 6.78/1.53  --sat_out_model                         small
% 6.78/1.53  --sat_out_clauses                       false
% 6.78/1.53  
% 6.78/1.53  ------ QBF Options
% 6.78/1.53  
% 6.78/1.53  --qbf_mode                              false
% 6.78/1.53  --qbf_elim_univ                         false
% 6.78/1.53  --qbf_dom_inst                          none
% 6.78/1.53  --qbf_dom_pre_inst                      false
% 6.78/1.53  --qbf_sk_in                             false
% 6.78/1.53  --qbf_pred_elim                         true
% 6.78/1.53  --qbf_split                             512
% 6.78/1.53  
% 6.78/1.53  ------ BMC1 Options
% 6.78/1.53  
% 6.78/1.53  --bmc1_incremental                      false
% 6.78/1.53  --bmc1_axioms                           reachable_all
% 6.78/1.53  --bmc1_min_bound                        0
% 6.78/1.53  --bmc1_max_bound                        -1
% 6.78/1.53  --bmc1_max_bound_default                -1
% 6.78/1.53  --bmc1_symbol_reachability              true
% 6.78/1.53  --bmc1_property_lemmas                  false
% 6.78/1.53  --bmc1_k_induction                      false
% 6.78/1.53  --bmc1_non_equiv_states                 false
% 6.78/1.53  --bmc1_deadlock                         false
% 6.78/1.53  --bmc1_ucm                              false
% 6.78/1.53  --bmc1_add_unsat_core                   none
% 6.78/1.53  --bmc1_unsat_core_children              false
% 6.78/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 6.78/1.53  --bmc1_out_stat                         full
% 6.78/1.53  --bmc1_ground_init                      false
% 6.78/1.53  --bmc1_pre_inst_next_state              false
% 6.78/1.53  --bmc1_pre_inst_state                   false
% 6.78/1.53  --bmc1_pre_inst_reach_state             false
% 6.78/1.53  --bmc1_out_unsat_core                   false
% 6.78/1.53  --bmc1_aig_witness_out                  false
% 6.78/1.53  --bmc1_verbose                          false
% 6.78/1.53  --bmc1_dump_clauses_tptp                false
% 6.78/1.53  --bmc1_dump_unsat_core_tptp             false
% 6.78/1.53  --bmc1_dump_file                        -
% 6.78/1.53  --bmc1_ucm_expand_uc_limit              128
% 6.78/1.53  --bmc1_ucm_n_expand_iterations          6
% 6.78/1.53  --bmc1_ucm_extend_mode                  1
% 6.78/1.53  --bmc1_ucm_init_mode                    2
% 6.78/1.53  --bmc1_ucm_cone_mode                    none
% 6.78/1.53  --bmc1_ucm_reduced_relation_type        0
% 6.78/1.53  --bmc1_ucm_relax_model                  4
% 6.78/1.53  --bmc1_ucm_full_tr_after_sat            true
% 6.78/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 6.78/1.53  --bmc1_ucm_layered_model                none
% 6.78/1.53  --bmc1_ucm_max_lemma_size               10
% 6.78/1.53  
% 6.78/1.53  ------ AIG Options
% 6.78/1.53  
% 6.78/1.53  --aig_mode                              false
% 6.78/1.53  
% 6.78/1.53  ------ Instantiation Options
% 6.78/1.53  
% 6.78/1.53  --instantiation_flag                    true
% 6.78/1.53  --inst_sos_flag                         false
% 6.78/1.53  --inst_sos_phase                        true
% 6.78/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.78/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.78/1.53  --inst_lit_sel_side                     none
% 6.78/1.53  --inst_solver_per_active                1400
% 6.78/1.53  --inst_solver_calls_frac                1.
% 6.78/1.53  --inst_passive_queue_type               priority_queues
% 6.78/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.78/1.53  --inst_passive_queues_freq              [25;2]
% 6.78/1.53  --inst_dismatching                      true
% 6.78/1.53  --inst_eager_unprocessed_to_passive     true
% 6.78/1.53  --inst_prop_sim_given                   true
% 6.78/1.53  --inst_prop_sim_new                     false
% 6.78/1.53  --inst_subs_new                         false
% 6.78/1.53  --inst_eq_res_simp                      false
% 6.78/1.53  --inst_subs_given                       false
% 6.78/1.53  --inst_orphan_elimination               true
% 6.78/1.53  --inst_learning_loop_flag               true
% 6.78/1.53  --inst_learning_start                   3000
% 6.78/1.53  --inst_learning_factor                  2
% 6.78/1.53  --inst_start_prop_sim_after_learn       3
% 6.78/1.53  --inst_sel_renew                        solver
% 6.78/1.53  --inst_lit_activity_flag                true
% 6.78/1.53  --inst_restr_to_given                   false
% 6.78/1.53  --inst_activity_threshold               500
% 6.78/1.53  --inst_out_proof                        true
% 6.78/1.53  
% 6.78/1.53  ------ Resolution Options
% 6.78/1.53  
% 6.78/1.53  --resolution_flag                       false
% 6.78/1.53  --res_lit_sel                           adaptive
% 6.78/1.53  --res_lit_sel_side                      none
% 6.78/1.53  --res_ordering                          kbo
% 6.78/1.53  --res_to_prop_solver                    active
% 6.78/1.53  --res_prop_simpl_new                    false
% 6.78/1.53  --res_prop_simpl_given                  true
% 6.78/1.53  --res_passive_queue_type                priority_queues
% 6.78/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.78/1.53  --res_passive_queues_freq               [15;5]
% 6.78/1.53  --res_forward_subs                      full
% 6.78/1.53  --res_backward_subs                     full
% 6.78/1.53  --res_forward_subs_resolution           true
% 6.78/1.53  --res_backward_subs_resolution          true
% 6.78/1.53  --res_orphan_elimination                true
% 6.78/1.53  --res_time_limit                        2.
% 6.78/1.53  --res_out_proof                         true
% 6.78/1.53  
% 6.78/1.53  ------ Superposition Options
% 6.78/1.53  
% 6.78/1.53  --superposition_flag                    true
% 6.78/1.53  --sup_passive_queue_type                priority_queues
% 6.78/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.78/1.53  --sup_passive_queues_freq               [8;1;4]
% 6.78/1.53  --demod_completeness_check              fast
% 6.78/1.53  --demod_use_ground                      true
% 6.78/1.53  --sup_to_prop_solver                    passive
% 6.78/1.53  --sup_prop_simpl_new                    true
% 6.78/1.53  --sup_prop_simpl_given                  true
% 6.78/1.53  --sup_fun_splitting                     false
% 6.78/1.53  --sup_smt_interval                      50000
% 6.78/1.53  
% 6.78/1.53  ------ Superposition Simplification Setup
% 6.78/1.53  
% 6.78/1.53  --sup_indices_passive                   []
% 6.78/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 6.78/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.53  --sup_full_bw                           [BwDemod]
% 6.78/1.53  --sup_immed_triv                        [TrivRules]
% 6.78/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.78/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.53  --sup_immed_bw_main                     []
% 6.78/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.78/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 6.78/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.78/1.53  
% 6.78/1.53  ------ Combination Options
% 6.78/1.53  
% 6.78/1.53  --comb_res_mult                         3
% 6.78/1.53  --comb_sup_mult                         2
% 6.78/1.53  --comb_inst_mult                        10
% 6.78/1.53  
% 6.78/1.53  ------ Debug Options
% 6.78/1.53  
% 6.78/1.53  --dbg_backtrace                         false
% 6.78/1.53  --dbg_dump_prop_clauses                 false
% 6.78/1.53  --dbg_dump_prop_clauses_file            -
% 6.78/1.53  --dbg_out_stat                          false
% 6.78/1.53  
% 6.78/1.53  
% 6.78/1.53  
% 6.78/1.53  
% 6.78/1.53  ------ Proving...
% 6.78/1.53  
% 6.78/1.53  
% 6.78/1.53  % SZS status Theorem for theBenchmark.p
% 6.78/1.53  
% 6.78/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 6.78/1.53  
% 6.78/1.53  fof(f4,axiom,(
% 6.78/1.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f32,plain,(
% 6.78/1.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.78/1.53    inference(cnf_transformation,[],[f4])).
% 6.78/1.53  
% 6.78/1.53  fof(f7,axiom,(
% 6.78/1.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f17,plain,(
% 6.78/1.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.78/1.53    inference(ennf_transformation,[],[f7])).
% 6.78/1.53  
% 6.78/1.53  fof(f36,plain,(
% 6.78/1.53    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 6.78/1.53    inference(cnf_transformation,[],[f17])).
% 6.78/1.53  
% 6.78/1.53  fof(f10,axiom,(
% 6.78/1.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f18,plain,(
% 6.78/1.53    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 6.78/1.53    inference(ennf_transformation,[],[f10])).
% 6.78/1.53  
% 6.78/1.53  fof(f19,plain,(
% 6.78/1.53    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 6.78/1.53    inference(flattening,[],[f18])).
% 6.78/1.53  
% 6.78/1.53  fof(f39,plain,(
% 6.78/1.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 6.78/1.53    inference(cnf_transformation,[],[f19])).
% 6.78/1.53  
% 6.78/1.53  fof(f13,conjecture,(
% 6.78/1.53    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f14,negated_conjecture,(
% 6.78/1.53    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 6.78/1.53    inference(negated_conjecture,[],[f13])).
% 6.78/1.53  
% 6.78/1.53  fof(f22,plain,(
% 6.78/1.53    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 6.78/1.53    inference(ennf_transformation,[],[f14])).
% 6.78/1.53  
% 6.78/1.53  fof(f23,plain,(
% 6.78/1.53    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 6.78/1.53    inference(flattening,[],[f22])).
% 6.78/1.53  
% 6.78/1.53  fof(f26,plain,(
% 6.78/1.53    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 6.78/1.53    introduced(choice_axiom,[])).
% 6.78/1.53  
% 6.78/1.53  fof(f27,plain,(
% 6.78/1.53    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 6.78/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26])).
% 6.78/1.53  
% 6.78/1.53  fof(f44,plain,(
% 6.78/1.53    r1_xboole_0(sK3,sK1)),
% 6.78/1.53    inference(cnf_transformation,[],[f27])).
% 6.78/1.53  
% 6.78/1.53  fof(f6,axiom,(
% 6.78/1.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f35,plain,(
% 6.78/1.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.78/1.53    inference(cnf_transformation,[],[f6])).
% 6.78/1.53  
% 6.78/1.53  fof(f42,plain,(
% 6.78/1.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 6.78/1.53    inference(cnf_transformation,[],[f27])).
% 6.78/1.53  
% 6.78/1.53  fof(f2,axiom,(
% 6.78/1.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f15,plain,(
% 6.78/1.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 6.78/1.53    inference(ennf_transformation,[],[f2])).
% 6.78/1.53  
% 6.78/1.53  fof(f30,plain,(
% 6.78/1.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 6.78/1.53    inference(cnf_transformation,[],[f15])).
% 6.78/1.53  
% 6.78/1.53  fof(f5,axiom,(
% 6.78/1.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f25,plain,(
% 6.78/1.53    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 6.78/1.53    inference(nnf_transformation,[],[f5])).
% 6.78/1.53  
% 6.78/1.53  fof(f34,plain,(
% 6.78/1.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 6.78/1.53    inference(cnf_transformation,[],[f25])).
% 6.78/1.53  
% 6.78/1.53  fof(f33,plain,(
% 6.78/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 6.78/1.53    inference(cnf_transformation,[],[f25])).
% 6.78/1.53  
% 6.78/1.53  fof(f11,axiom,(
% 6.78/1.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f40,plain,(
% 6.78/1.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.78/1.53    inference(cnf_transformation,[],[f11])).
% 6.78/1.53  
% 6.78/1.53  fof(f1,axiom,(
% 6.78/1.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f24,plain,(
% 6.78/1.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.78/1.53    inference(nnf_transformation,[],[f1])).
% 6.78/1.53  
% 6.78/1.53  fof(f28,plain,(
% 6.78/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.78/1.53    inference(cnf_transformation,[],[f24])).
% 6.78/1.53  
% 6.78/1.53  fof(f9,axiom,(
% 6.78/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f38,plain,(
% 6.78/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.78/1.53    inference(cnf_transformation,[],[f9])).
% 6.78/1.53  
% 6.78/1.53  fof(f47,plain,(
% 6.78/1.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 6.78/1.53    inference(definition_unfolding,[],[f28,f38])).
% 6.78/1.53  
% 6.78/1.53  fof(f43,plain,(
% 6.78/1.53    r1_xboole_0(sK2,sK0)),
% 6.78/1.53    inference(cnf_transformation,[],[f27])).
% 6.78/1.53  
% 6.78/1.53  fof(f8,axiom,(
% 6.78/1.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f37,plain,(
% 6.78/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.78/1.53    inference(cnf_transformation,[],[f8])).
% 6.78/1.53  
% 6.78/1.53  fof(f48,plain,(
% 6.78/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 6.78/1.53    inference(definition_unfolding,[],[f37,f38])).
% 6.78/1.53  
% 6.78/1.53  fof(f3,axiom,(
% 6.78/1.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 6.78/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.53  
% 6.78/1.53  fof(f16,plain,(
% 6.78/1.53    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 6.78/1.53    inference(ennf_transformation,[],[f3])).
% 6.78/1.53  
% 6.78/1.53  fof(f31,plain,(
% 6.78/1.53    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 6.78/1.53    inference(cnf_transformation,[],[f16])).
% 6.78/1.53  
% 6.78/1.53  fof(f45,plain,(
% 6.78/1.53    sK1 != sK2),
% 6.78/1.53    inference(cnf_transformation,[],[f27])).
% 6.78/1.53  
% 6.78/1.53  cnf(c_4,plain,
% 6.78/1.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 6.78/1.53      inference(cnf_transformation,[],[f32]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_32657,plain,
% 6.78/1.53      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_4]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_8,plain,
% 6.78/1.53      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 6.78/1.53      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 6.78/1.53      inference(cnf_transformation,[],[f36]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_1594,plain,
% 6.78/1.53      ( ~ r1_tarski(X0,k2_xboole_0(X1,sK3))
% 6.78/1.53      | r1_tarski(k4_xboole_0(X0,X1),sK3) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_8]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_14184,plain,
% 6.78/1.53      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3)
% 6.78/1.53      | ~ r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_1594]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_10,plain,
% 6.78/1.53      ( ~ r1_tarski(X0,X1)
% 6.78/1.53      | ~ r1_tarski(X0,X2)
% 6.78/1.53      | ~ r1_xboole_0(X1,X2)
% 6.78/1.53      | k1_xboole_0 = X0 ),
% 6.78/1.53      inference(cnf_transformation,[],[f39]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_14,negated_conjecture,
% 6.78/1.53      ( r1_xboole_0(sK3,sK1) ),
% 6.78/1.53      inference(cnf_transformation,[],[f44]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_212,plain,
% 6.78/1.53      ( ~ r1_tarski(X0,X1)
% 6.78/1.53      | ~ r1_tarski(X0,X2)
% 6.78/1.53      | sK3 != X1
% 6.78/1.53      | sK1 != X2
% 6.78/1.53      | k1_xboole_0 = X0 ),
% 6.78/1.53      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_213,plain,
% 6.78/1.53      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(X0,sK1) | k1_xboole_0 = X0 ),
% 6.78/1.53      inference(unflattening,[status(thm)],[c_212]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_4200,plain,
% 6.78/1.53      ( ~ r1_tarski(k4_xboole_0(X0,X1),sK3)
% 6.78/1.53      | ~ r1_tarski(k4_xboole_0(X0,X1),sK1)
% 6.78/1.53      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_213]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_5543,plain,
% 6.78/1.53      ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK3)
% 6.78/1.53      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
% 6.78/1.53      | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_4200]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_7,plain,
% 6.78/1.53      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.78/1.53      inference(cnf_transformation,[],[f35]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_522,plain,
% 6.78/1.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 6.78/1.53      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_1652,plain,
% 6.78/1.53      ( r1_tarski(X0,X0) = iProver_top ),
% 6.78/1.53      inference(superposition,[status(thm)],[c_7,c_522]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_16,negated_conjecture,
% 6.78/1.53      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 6.78/1.53      inference(cnf_transformation,[],[f42]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_2,plain,
% 6.78/1.53      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 6.78/1.53      inference(cnf_transformation,[],[f30]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_523,plain,
% 6.78/1.53      ( r1_tarski(X0,X1) != iProver_top
% 6.78/1.53      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 6.78/1.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_2508,plain,
% 6.78/1.53      ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) = iProver_top
% 6.78/1.53      | r1_tarski(X0,sK1) != iProver_top ),
% 6.78/1.53      inference(superposition,[status(thm)],[c_16,c_523]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_5,plain,
% 6.78/1.53      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.78/1.53      inference(cnf_transformation,[],[f34]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_521,plain,
% 6.78/1.53      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 6.78/1.53      | r1_tarski(X0,X1) != iProver_top ),
% 6.78/1.53      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_2894,plain,
% 6.78/1.53      ( k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) = k1_xboole_0
% 6.78/1.53      | r1_tarski(X0,sK1) != iProver_top ),
% 6.78/1.53      inference(superposition,[status(thm)],[c_2508,c_521]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_3209,plain,
% 6.78/1.53      ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 6.78/1.53      inference(superposition,[status(thm)],[c_1652,c_2894]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_6,plain,
% 6.78/1.53      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 6.78/1.53      inference(cnf_transformation,[],[f33]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_520,plain,
% 6.78/1.53      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 6.78/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 6.78/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_4733,plain,
% 6.78/1.53      ( r1_tarski(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 6.78/1.53      inference(superposition,[status(thm)],[c_3209,c_520]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_4745,plain,
% 6.78/1.53      ( r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
% 6.78/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_4733]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_258,plain,( X0 = X0 ),theory(equality) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_1219,plain,
% 6.78/1.53      ( k4_xboole_0(X0,sK2) = k4_xboole_0(X0,sK2) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_258]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_3127,plain,
% 6.78/1.53      ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_1219]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_259,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_772,plain,
% 6.78/1.53      ( X0 != X1 | k4_xboole_0(X2,sK2) != X1 | k4_xboole_0(X2,sK2) = X0 ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_259]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_1218,plain,
% 6.78/1.53      ( X0 != k4_xboole_0(X1,sK2)
% 6.78/1.53      | k4_xboole_0(X1,sK2) = X0
% 6.78/1.53      | k4_xboole_0(X1,sK2) != k4_xboole_0(X1,sK2) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_772]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_2358,plain,
% 6.78/1.53      ( k4_xboole_0(X0,sK2) != k4_xboole_0(X0,sK2)
% 6.78/1.53      | k4_xboole_0(X0,sK2) = k1_xboole_0
% 6.78/1.53      | k1_xboole_0 != k4_xboole_0(X0,sK2) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_1218]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_2646,plain,
% 6.78/1.53      ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)
% 6.78/1.53      | k4_xboole_0(sK1,sK2) = k1_xboole_0
% 6.78/1.53      | k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_2358]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_11,plain,
% 6.78/1.53      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 6.78/1.53      inference(cnf_transformation,[],[f40]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_518,plain,
% 6.78/1.53      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 6.78/1.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_519,plain,
% 6.78/1.53      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 6.78/1.53      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 6.78/1.53      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_1482,plain,
% 6.78/1.53      ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
% 6.78/1.53      | r1_tarski(k4_xboole_0(X0,sK0),sK1) = iProver_top ),
% 6.78/1.53      inference(superposition,[status(thm)],[c_16,c_519]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_1871,plain,
% 6.78/1.53      ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
% 6.78/1.53      inference(superposition,[status(thm)],[c_518,c_1482]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_1,plain,
% 6.78/1.53      ( ~ r1_xboole_0(X0,X1)
% 6.78/1.53      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 6.78/1.53      inference(cnf_transformation,[],[f47]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_104,plain,
% 6.78/1.53      ( ~ r1_xboole_0(X0,X1)
% 6.78/1.53      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 6.78/1.53      inference(prop_impl,[status(thm)],[c_1]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_15,negated_conjecture,
% 6.78/1.53      ( r1_xboole_0(sK2,sK0) ),
% 6.78/1.53      inference(cnf_transformation,[],[f43]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_207,plain,
% 6.78/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 6.78/1.53      | sK0 != X1
% 6.78/1.53      | sK2 != X0 ),
% 6.78/1.53      inference(resolution_lifted,[status(thm)],[c_104,c_15]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_208,plain,
% 6.78/1.53      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 6.78/1.53      inference(unflattening,[status(thm)],[c_207]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_9,plain,
% 6.78/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 6.78/1.53      inference(cnf_transformation,[],[f48]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_837,plain,
% 6.78/1.53      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 6.78/1.53      inference(superposition,[status(thm)],[c_208,c_9]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_853,plain,
% 6.78/1.53      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 6.78/1.53      inference(demodulation,[status(thm)],[c_837,c_7]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_1887,plain,
% 6.78/1.53      ( r1_tarski(sK2,sK1) = iProver_top ),
% 6.78/1.53      inference(light_normalisation,[status(thm)],[c_1871,c_853]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_642,plain,
% 6.78/1.53      ( ~ r1_tarski(sK2,sK1) | k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_643,plain,
% 6.78/1.53      ( k4_xboole_0(sK2,sK1) = k1_xboole_0
% 6.78/1.53      | r1_tarski(sK2,sK1) != iProver_top ),
% 6.78/1.53      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_615,plain,
% 6.78/1.53      ( k4_xboole_0(sK2,sK1) != X0
% 6.78/1.53      | k4_xboole_0(sK1,sK2) != X0
% 6.78/1.53      | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_259]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_616,plain,
% 6.78/1.53      ( k4_xboole_0(sK2,sK1) != k1_xboole_0
% 6.78/1.53      | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)
% 6.78/1.53      | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_615]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_3,plain,
% 6.78/1.53      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 6.78/1.53      inference(cnf_transformation,[],[f31]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_609,plain,
% 6.78/1.53      ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK2,sK1) | sK1 = sK2 ),
% 6.78/1.53      inference(instantiation,[status(thm)],[c_3]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(c_13,negated_conjecture,
% 6.78/1.53      ( sK1 != sK2 ),
% 6.78/1.53      inference(cnf_transformation,[],[f45]) ).
% 6.78/1.53  
% 6.78/1.53  cnf(contradiction,plain,
% 6.78/1.53      ( $false ),
% 6.78/1.53      inference(minisat,
% 6.78/1.53                [status(thm)],
% 6.78/1.53                [c_32657,c_14184,c_5543,c_4745,c_3127,c_2646,c_1887,
% 6.78/1.53                 c_643,c_616,c_609,c_13]) ).
% 6.78/1.53  
% 6.78/1.53  
% 6.78/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 6.78/1.53  
% 6.78/1.53  ------                               Statistics
% 6.78/1.53  
% 6.78/1.53  ------ General
% 6.78/1.53  
% 6.78/1.53  abstr_ref_over_cycles:                  0
% 6.78/1.53  abstr_ref_under_cycles:                 0
% 6.78/1.53  gc_basic_clause_elim:                   0
% 6.78/1.53  forced_gc_time:                         0
% 6.78/1.53  parsing_time:                           0.005
% 6.78/1.53  unif_index_cands_time:                  0.
% 6.78/1.53  unif_index_add_time:                    0.
% 6.78/1.53  orderings_time:                         0.
% 6.78/1.53  out_proof_time:                         0.006
% 6.78/1.53  total_time:                             0.776
% 6.78/1.53  num_of_symbols:                         40
% 6.78/1.53  num_of_terms:                           24941
% 6.78/1.53  
% 6.78/1.53  ------ Preprocessing
% 6.78/1.53  
% 6.78/1.53  num_of_splits:                          0
% 6.78/1.53  num_of_split_atoms:                     0
% 6.78/1.53  num_of_reused_defs:                     0
% 6.78/1.53  num_eq_ax_congr_red:                    1
% 6.78/1.53  num_of_sem_filtered_clauses:            1
% 6.78/1.53  num_of_subtypes:                        0
% 6.78/1.53  monotx_restored_types:                  0
% 6.78/1.53  sat_num_of_epr_types:                   0
% 6.78/1.53  sat_num_of_non_cyclic_types:            0
% 6.78/1.53  sat_guarded_non_collapsed_types:        0
% 6.78/1.53  num_pure_diseq_elim:                    0
% 6.78/1.53  simp_replaced_by:                       0
% 6.78/1.53  res_preprocessed:                       62
% 6.78/1.53  prep_upred:                             0
% 6.78/1.53  prep_unflattend:                        10
% 6.78/1.53  smt_new_axioms:                         0
% 6.78/1.53  pred_elim_cands:                        2
% 6.78/1.53  pred_elim:                              1
% 6.78/1.53  pred_elim_cl:                           0
% 6.78/1.53  pred_elim_cycles:                       2
% 6.78/1.53  merged_defs:                            8
% 6.78/1.53  merged_defs_ncl:                        0
% 6.78/1.53  bin_hyper_res:                          8
% 6.78/1.53  prep_cycles:                            3
% 6.78/1.53  pred_elim_time:                         0.
% 6.78/1.53  splitting_time:                         0.
% 6.78/1.53  sem_filter_time:                        0.
% 6.78/1.53  monotx_time:                            0.
% 6.78/1.53  subtype_inf_time:                       0.
% 6.78/1.53  
% 6.78/1.53  ------ Problem properties
% 6.78/1.53  
% 6.78/1.53  clauses:                                17
% 6.78/1.53  conjectures:                            2
% 6.78/1.53  epr:                                    3
% 6.78/1.53  horn:                                   17
% 6.78/1.53  ground:                                 4
% 6.78/1.53  unary:                                  8
% 6.78/1.53  binary:                                 5
% 6.78/1.53  lits:                                   31
% 6.78/1.53  lits_eq:                                14
% 6.78/1.53  fd_pure:                                0
% 6.78/1.53  fd_pseudo:                              0
% 6.78/1.53  fd_cond:                                3
% 6.78/1.53  fd_pseudo_cond:                         1
% 6.78/1.53  ac_symbols:                             0
% 6.78/1.53  
% 6.78/1.53  ------ Propositional Solver
% 6.78/1.53  
% 6.78/1.53  prop_solver_calls:                      29
% 6.78/1.53  prop_fast_solver_calls:                 717
% 6.78/1.53  smt_solver_calls:                       0
% 6.78/1.53  smt_fast_solver_calls:                  0
% 6.78/1.53  prop_num_of_clauses:                    9543
% 6.78/1.53  prop_preprocess_simplified:             17308
% 6.78/1.53  prop_fo_subsumed:                       10
% 6.78/1.53  prop_solver_time:                       0.
% 6.78/1.53  smt_solver_time:                        0.
% 6.78/1.53  smt_fast_solver_time:                   0.
% 6.78/1.53  prop_fast_solver_time:                  0.
% 6.78/1.53  prop_unsat_core_time:                   0.001
% 6.78/1.53  
% 6.78/1.53  ------ QBF
% 6.78/1.53  
% 6.78/1.53  qbf_q_res:                              0
% 6.78/1.53  qbf_num_tautologies:                    0
% 6.78/1.53  qbf_prep_cycles:                        0
% 6.78/1.53  
% 6.78/1.53  ------ BMC1
% 6.78/1.53  
% 6.78/1.53  bmc1_current_bound:                     -1
% 6.78/1.53  bmc1_last_solved_bound:                 -1
% 6.78/1.53  bmc1_unsat_core_size:                   -1
% 6.78/1.53  bmc1_unsat_core_parents_size:           -1
% 6.78/1.53  bmc1_merge_next_fun:                    0
% 6.78/1.53  bmc1_unsat_core_clauses_time:           0.
% 6.78/1.53  
% 6.78/1.53  ------ Instantiation
% 6.78/1.53  
% 6.78/1.53  inst_num_of_clauses:                    3640
% 6.78/1.53  inst_num_in_passive:                    2094
% 6.78/1.53  inst_num_in_active:                     1258
% 6.78/1.53  inst_num_in_unprocessed:                287
% 6.78/1.53  inst_num_of_loops:                      1344
% 6.78/1.53  inst_num_of_learning_restarts:          0
% 6.78/1.53  inst_num_moves_active_passive:          81
% 6.78/1.53  inst_lit_activity:                      0
% 6.78/1.53  inst_lit_activity_moves:                0
% 6.78/1.53  inst_num_tautologies:                   0
% 6.78/1.53  inst_num_prop_implied:                  0
% 6.78/1.53  inst_num_existing_simplified:           0
% 6.78/1.53  inst_num_eq_res_simplified:             0
% 6.78/1.53  inst_num_child_elim:                    0
% 6.78/1.53  inst_num_of_dismatching_blockings:      4665
% 6.78/1.53  inst_num_of_non_proper_insts:           4998
% 6.78/1.53  inst_num_of_duplicates:                 0
% 6.78/1.53  inst_inst_num_from_inst_to_res:         0
% 6.78/1.53  inst_dismatching_checking_time:         0.
% 6.78/1.53  
% 6.78/1.53  ------ Resolution
% 6.78/1.53  
% 6.78/1.53  res_num_of_clauses:                     0
% 6.78/1.53  res_num_in_passive:                     0
% 6.78/1.53  res_num_in_active:                      0
% 6.78/1.53  res_num_of_loops:                       65
% 6.78/1.53  res_forward_subset_subsumed:            573
% 6.78/1.53  res_backward_subset_subsumed:           2
% 6.78/1.53  res_forward_subsumed:                   0
% 6.78/1.53  res_backward_subsumed:                  0
% 6.78/1.53  res_forward_subsumption_resolution:     0
% 6.78/1.53  res_backward_subsumption_resolution:    0
% 6.78/1.53  res_clause_to_clause_subsumption:       5385
% 6.78/1.53  res_orphan_elimination:                 0
% 6.78/1.53  res_tautology_del:                      461
% 6.78/1.53  res_num_eq_res_simplified:              0
% 6.78/1.53  res_num_sel_changes:                    0
% 6.78/1.53  res_moves_from_active_to_pass:          0
% 6.78/1.53  
% 6.78/1.53  ------ Superposition
% 6.78/1.53  
% 6.78/1.53  sup_time_total:                         0.
% 6.78/1.53  sup_time_generating:                    0.
% 6.78/1.53  sup_time_sim_full:                      0.
% 6.78/1.53  sup_time_sim_immed:                     0.
% 6.78/1.53  
% 6.78/1.53  sup_num_of_clauses:                     1034
% 6.78/1.53  sup_num_in_active:                      264
% 6.78/1.53  sup_num_in_passive:                     770
% 6.78/1.53  sup_num_of_loops:                       268
% 6.78/1.53  sup_fw_superposition:                   1149
% 6.78/1.53  sup_bw_superposition:                   875
% 6.78/1.53  sup_immediate_simplified:               792
% 6.78/1.53  sup_given_eliminated:                   0
% 6.78/1.53  comparisons_done:                       0
% 6.78/1.53  comparisons_avoided:                    0
% 6.78/1.53  
% 6.78/1.53  ------ Simplifications
% 6.78/1.53  
% 6.78/1.53  
% 6.78/1.53  sim_fw_subset_subsumed:                 56
% 6.78/1.53  sim_bw_subset_subsumed:                 4
% 6.78/1.53  sim_fw_subsumed:                        232
% 6.78/1.53  sim_bw_subsumed:                        3
% 6.78/1.53  sim_fw_subsumption_res:                 5
% 6.78/1.53  sim_bw_subsumption_res:                 0
% 6.78/1.53  sim_tautology_del:                      10
% 6.78/1.53  sim_eq_tautology_del:                   92
% 6.78/1.53  sim_eq_res_simp:                        0
% 6.78/1.53  sim_fw_demodulated:                     326
% 6.78/1.53  sim_bw_demodulated:                     4
% 6.78/1.53  sim_light_normalised:                   308
% 6.78/1.53  sim_joinable_taut:                      0
% 6.78/1.53  sim_joinable_simp:                      0
% 6.78/1.53  sim_ac_normalised:                      0
% 6.78/1.53  sim_smt_subsumption:                    0
% 6.78/1.53  
%------------------------------------------------------------------------------
