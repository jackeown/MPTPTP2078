%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:13 EST 2020

% Result     : Theorem 39.28s
% Output     : CNFRefutation 39.28s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 285 expanded)
%              Number of clauses        :   51 (  78 expanded)
%              Number of leaves         :   18 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 ( 468 expanded)
%              Number of equality atoms :   81 ( 223 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))
      & r1_tarski(sK2,sK4)
      & ~ r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))
    & r1_tarski(sK2,sK4)
    & ~ r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f26])).

fof(f43,plain,(
    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f34,f38,f38,f38,f38])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_367,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_369,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_371,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1854,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_369,c_371])).

cnf(c_70169,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_367,c_1854])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_373,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_9])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_696,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1502,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_696,c_8])).

cnf(c_1938,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_1502])).

cnf(c_13808,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_373,c_1938])).

cnf(c_1943,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_1502,c_0])).

cnf(c_1949,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_1943])).

cnf(c_13954,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_13808,c_6,c_9,c_1949])).

cnf(c_668,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_672,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
    inference(demodulation,[status(thm)],[c_668,c_6])).

cnf(c_14174,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_13954,c_672])).

cnf(c_14392,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_14174,c_6])).

cnf(c_71998,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_70169,c_14392])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_112,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK4 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_113,plain,
    ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_112])).

cnf(c_73386,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k1_xboole_0))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_71998,c_113])).

cnf(c_73387,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_73386,c_9,c_373])).

cnf(c_383,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))))
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5581,plain,
    ( ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))))
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_235,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_477,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | X0 != sK0(sK3,sK2)
    | X1 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_515,plain,
    ( r2_hidden(sK0(sK3,sK2),X0)
    | ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | X0 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))
    | sK0(sK3,sK2) != sK0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_1151,plain,
    ( r2_hidden(sK0(sK3,sK2),k4_xboole_0(X0,X1))
    | ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | sK0(sK3,sK2) != sK0(sK3,sK2)
    | k4_xboole_0(X0,X1) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_5580,plain,
    ( ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))))
    | sK0(sK3,sK2) != sK0(sK3,sK2)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_230,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_609,plain,
    ( sK0(sK3,sK2) = sK0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_231,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_462,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) != X0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) != X0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_463,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) != k1_xboole_0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_400,plain,
    ( r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_391,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73387,c_70169,c_5581,c_5580,c_609,c_463,c_400,c_391,c_12,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:59:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 39.28/5.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.28/5.52  
% 39.28/5.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.28/5.52  
% 39.28/5.52  ------  iProver source info
% 39.28/5.52  
% 39.28/5.52  git: date: 2020-06-30 10:37:57 +0100
% 39.28/5.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.28/5.52  git: non_committed_changes: false
% 39.28/5.52  git: last_make_outside_of_git: false
% 39.28/5.52  
% 39.28/5.52  ------ 
% 39.28/5.52  
% 39.28/5.52  ------ Input Options
% 39.28/5.52  
% 39.28/5.52  --out_options                           all
% 39.28/5.52  --tptp_safe_out                         true
% 39.28/5.52  --problem_path                          ""
% 39.28/5.52  --include_path                          ""
% 39.28/5.52  --clausifier                            res/vclausify_rel
% 39.28/5.52  --clausifier_options                    ""
% 39.28/5.52  --stdin                                 false
% 39.28/5.52  --stats_out                             all
% 39.28/5.52  
% 39.28/5.52  ------ General Options
% 39.28/5.52  
% 39.28/5.52  --fof                                   false
% 39.28/5.52  --time_out_real                         305.
% 39.28/5.52  --time_out_virtual                      -1.
% 39.28/5.52  --symbol_type_check                     false
% 39.28/5.52  --clausify_out                          false
% 39.28/5.52  --sig_cnt_out                           false
% 39.28/5.52  --trig_cnt_out                          false
% 39.28/5.52  --trig_cnt_out_tolerance                1.
% 39.28/5.52  --trig_cnt_out_sk_spl                   false
% 39.28/5.52  --abstr_cl_out                          false
% 39.28/5.52  
% 39.28/5.52  ------ Global Options
% 39.28/5.52  
% 39.28/5.52  --schedule                              default
% 39.28/5.52  --add_important_lit                     false
% 39.28/5.52  --prop_solver_per_cl                    1000
% 39.28/5.52  --min_unsat_core                        false
% 39.28/5.52  --soft_assumptions                      false
% 39.28/5.52  --soft_lemma_size                       3
% 39.28/5.52  --prop_impl_unit_size                   0
% 39.28/5.52  --prop_impl_unit                        []
% 39.28/5.52  --share_sel_clauses                     true
% 39.28/5.52  --reset_solvers                         false
% 39.28/5.52  --bc_imp_inh                            [conj_cone]
% 39.28/5.52  --conj_cone_tolerance                   3.
% 39.28/5.52  --extra_neg_conj                        none
% 39.28/5.52  --large_theory_mode                     true
% 39.28/5.52  --prolific_symb_bound                   200
% 39.28/5.52  --lt_threshold                          2000
% 39.28/5.52  --clause_weak_htbl                      true
% 39.28/5.52  --gc_record_bc_elim                     false
% 39.28/5.52  
% 39.28/5.52  ------ Preprocessing Options
% 39.28/5.52  
% 39.28/5.52  --preprocessing_flag                    true
% 39.28/5.52  --time_out_prep_mult                    0.1
% 39.28/5.52  --splitting_mode                        input
% 39.28/5.52  --splitting_grd                         true
% 39.28/5.52  --splitting_cvd                         false
% 39.28/5.52  --splitting_cvd_svl                     false
% 39.28/5.52  --splitting_nvd                         32
% 39.28/5.52  --sub_typing                            true
% 39.28/5.52  --prep_gs_sim                           true
% 39.28/5.52  --prep_unflatten                        true
% 39.28/5.52  --prep_res_sim                          true
% 39.28/5.52  --prep_upred                            true
% 39.28/5.52  --prep_sem_filter                       exhaustive
% 39.28/5.52  --prep_sem_filter_out                   false
% 39.28/5.52  --pred_elim                             true
% 39.28/5.52  --res_sim_input                         true
% 39.28/5.52  --eq_ax_congr_red                       true
% 39.28/5.52  --pure_diseq_elim                       true
% 39.28/5.52  --brand_transform                       false
% 39.28/5.52  --non_eq_to_eq                          false
% 39.28/5.52  --prep_def_merge                        true
% 39.28/5.52  --prep_def_merge_prop_impl              false
% 39.28/5.52  --prep_def_merge_mbd                    true
% 39.28/5.52  --prep_def_merge_tr_red                 false
% 39.28/5.52  --prep_def_merge_tr_cl                  false
% 39.28/5.52  --smt_preprocessing                     true
% 39.28/5.52  --smt_ac_axioms                         fast
% 39.28/5.52  --preprocessed_out                      false
% 39.28/5.52  --preprocessed_stats                    false
% 39.28/5.52  
% 39.28/5.52  ------ Abstraction refinement Options
% 39.28/5.52  
% 39.28/5.52  --abstr_ref                             []
% 39.28/5.52  --abstr_ref_prep                        false
% 39.28/5.52  --abstr_ref_until_sat                   false
% 39.28/5.52  --abstr_ref_sig_restrict                funpre
% 39.28/5.52  --abstr_ref_af_restrict_to_split_sk     false
% 39.28/5.52  --abstr_ref_under                       []
% 39.28/5.52  
% 39.28/5.52  ------ SAT Options
% 39.28/5.52  
% 39.28/5.52  --sat_mode                              false
% 39.28/5.52  --sat_fm_restart_options                ""
% 39.28/5.52  --sat_gr_def                            false
% 39.28/5.52  --sat_epr_types                         true
% 39.28/5.52  --sat_non_cyclic_types                  false
% 39.28/5.52  --sat_finite_models                     false
% 39.28/5.52  --sat_fm_lemmas                         false
% 39.28/5.52  --sat_fm_prep                           false
% 39.28/5.52  --sat_fm_uc_incr                        true
% 39.28/5.52  --sat_out_model                         small
% 39.28/5.52  --sat_out_clauses                       false
% 39.28/5.52  
% 39.28/5.52  ------ QBF Options
% 39.28/5.52  
% 39.28/5.52  --qbf_mode                              false
% 39.28/5.52  --qbf_elim_univ                         false
% 39.28/5.52  --qbf_dom_inst                          none
% 39.28/5.52  --qbf_dom_pre_inst                      false
% 39.28/5.52  --qbf_sk_in                             false
% 39.28/5.52  --qbf_pred_elim                         true
% 39.28/5.52  --qbf_split                             512
% 39.28/5.52  
% 39.28/5.52  ------ BMC1 Options
% 39.28/5.52  
% 39.28/5.52  --bmc1_incremental                      false
% 39.28/5.52  --bmc1_axioms                           reachable_all
% 39.28/5.52  --bmc1_min_bound                        0
% 39.28/5.52  --bmc1_max_bound                        -1
% 39.28/5.52  --bmc1_max_bound_default                -1
% 39.28/5.52  --bmc1_symbol_reachability              true
% 39.28/5.52  --bmc1_property_lemmas                  false
% 39.28/5.52  --bmc1_k_induction                      false
% 39.28/5.52  --bmc1_non_equiv_states                 false
% 39.28/5.52  --bmc1_deadlock                         false
% 39.28/5.52  --bmc1_ucm                              false
% 39.28/5.52  --bmc1_add_unsat_core                   none
% 39.28/5.52  --bmc1_unsat_core_children              false
% 39.28/5.52  --bmc1_unsat_core_extrapolate_axioms    false
% 39.28/5.52  --bmc1_out_stat                         full
% 39.28/5.52  --bmc1_ground_init                      false
% 39.28/5.52  --bmc1_pre_inst_next_state              false
% 39.28/5.52  --bmc1_pre_inst_state                   false
% 39.28/5.52  --bmc1_pre_inst_reach_state             false
% 39.28/5.52  --bmc1_out_unsat_core                   false
% 39.28/5.52  --bmc1_aig_witness_out                  false
% 39.28/5.52  --bmc1_verbose                          false
% 39.28/5.52  --bmc1_dump_clauses_tptp                false
% 39.28/5.52  --bmc1_dump_unsat_core_tptp             false
% 39.28/5.52  --bmc1_dump_file                        -
% 39.28/5.52  --bmc1_ucm_expand_uc_limit              128
% 39.28/5.52  --bmc1_ucm_n_expand_iterations          6
% 39.28/5.52  --bmc1_ucm_extend_mode                  1
% 39.28/5.52  --bmc1_ucm_init_mode                    2
% 39.28/5.52  --bmc1_ucm_cone_mode                    none
% 39.28/5.52  --bmc1_ucm_reduced_relation_type        0
% 39.28/5.52  --bmc1_ucm_relax_model                  4
% 39.28/5.52  --bmc1_ucm_full_tr_after_sat            true
% 39.28/5.52  --bmc1_ucm_expand_neg_assumptions       false
% 39.28/5.52  --bmc1_ucm_layered_model                none
% 39.28/5.52  --bmc1_ucm_max_lemma_size               10
% 39.28/5.52  
% 39.28/5.52  ------ AIG Options
% 39.28/5.52  
% 39.28/5.52  --aig_mode                              false
% 39.28/5.52  
% 39.28/5.52  ------ Instantiation Options
% 39.28/5.52  
% 39.28/5.52  --instantiation_flag                    true
% 39.28/5.52  --inst_sos_flag                         true
% 39.28/5.52  --inst_sos_phase                        true
% 39.28/5.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.28/5.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.28/5.52  --inst_lit_sel_side                     num_symb
% 39.28/5.52  --inst_solver_per_active                1400
% 39.28/5.52  --inst_solver_calls_frac                1.
% 39.28/5.52  --inst_passive_queue_type               priority_queues
% 39.28/5.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.28/5.52  --inst_passive_queues_freq              [25;2]
% 39.28/5.52  --inst_dismatching                      true
% 39.28/5.52  --inst_eager_unprocessed_to_passive     true
% 39.28/5.52  --inst_prop_sim_given                   true
% 39.28/5.52  --inst_prop_sim_new                     false
% 39.28/5.52  --inst_subs_new                         false
% 39.28/5.52  --inst_eq_res_simp                      false
% 39.28/5.52  --inst_subs_given                       false
% 39.28/5.52  --inst_orphan_elimination               true
% 39.28/5.52  --inst_learning_loop_flag               true
% 39.28/5.52  --inst_learning_start                   3000
% 39.28/5.52  --inst_learning_factor                  2
% 39.28/5.52  --inst_start_prop_sim_after_learn       3
% 39.28/5.52  --inst_sel_renew                        solver
% 39.28/5.52  --inst_lit_activity_flag                true
% 39.28/5.52  --inst_restr_to_given                   false
% 39.28/5.52  --inst_activity_threshold               500
% 39.28/5.52  --inst_out_proof                        true
% 39.28/5.52  
% 39.28/5.52  ------ Resolution Options
% 39.28/5.52  
% 39.28/5.52  --resolution_flag                       true
% 39.28/5.52  --res_lit_sel                           adaptive
% 39.28/5.52  --res_lit_sel_side                      none
% 39.28/5.52  --res_ordering                          kbo
% 39.28/5.52  --res_to_prop_solver                    active
% 39.28/5.52  --res_prop_simpl_new                    false
% 39.28/5.52  --res_prop_simpl_given                  true
% 39.28/5.52  --res_passive_queue_type                priority_queues
% 39.28/5.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.28/5.52  --res_passive_queues_freq               [15;5]
% 39.28/5.52  --res_forward_subs                      full
% 39.28/5.52  --res_backward_subs                     full
% 39.28/5.52  --res_forward_subs_resolution           true
% 39.28/5.52  --res_backward_subs_resolution          true
% 39.28/5.52  --res_orphan_elimination                true
% 39.28/5.52  --res_time_limit                        2.
% 39.28/5.52  --res_out_proof                         true
% 39.28/5.52  
% 39.28/5.52  ------ Superposition Options
% 39.28/5.52  
% 39.28/5.52  --superposition_flag                    true
% 39.28/5.52  --sup_passive_queue_type                priority_queues
% 39.28/5.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.28/5.52  --sup_passive_queues_freq               [8;1;4]
% 39.28/5.52  --demod_completeness_check              fast
% 39.28/5.52  --demod_use_ground                      true
% 39.28/5.52  --sup_to_prop_solver                    passive
% 39.28/5.52  --sup_prop_simpl_new                    true
% 39.28/5.52  --sup_prop_simpl_given                  true
% 39.28/5.52  --sup_fun_splitting                     true
% 39.28/5.52  --sup_smt_interval                      50000
% 39.28/5.52  
% 39.28/5.52  ------ Superposition Simplification Setup
% 39.28/5.52  
% 39.28/5.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.28/5.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.28/5.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.28/5.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.28/5.52  --sup_full_triv                         [TrivRules;PropSubs]
% 39.28/5.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.28/5.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.28/5.52  --sup_immed_triv                        [TrivRules]
% 39.28/5.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.28/5.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.28/5.52  --sup_immed_bw_main                     []
% 39.28/5.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.28/5.52  --sup_input_triv                        [Unflattening;TrivRules]
% 39.28/5.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.28/5.52  --sup_input_bw                          []
% 39.28/5.52  
% 39.28/5.52  ------ Combination Options
% 39.28/5.52  
% 39.28/5.52  --comb_res_mult                         3
% 39.28/5.52  --comb_sup_mult                         2
% 39.28/5.52  --comb_inst_mult                        10
% 39.28/5.52  
% 39.28/5.52  ------ Debug Options
% 39.28/5.52  
% 39.28/5.52  --dbg_backtrace                         false
% 39.28/5.52  --dbg_dump_prop_clauses                 false
% 39.28/5.52  --dbg_dump_prop_clauses_file            -
% 39.28/5.52  --dbg_out_stat                          false
% 39.28/5.52  ------ Parsing...
% 39.28/5.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.28/5.52  
% 39.28/5.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.28/5.52  
% 39.28/5.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.28/5.52  
% 39.28/5.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.28/5.52  ------ Proving...
% 39.28/5.52  ------ Problem Properties 
% 39.28/5.52  
% 39.28/5.52  
% 39.28/5.52  clauses                                 14
% 39.28/5.52  conjectures                             2
% 39.28/5.52  EPR                                     3
% 39.28/5.52  Horn                                    12
% 39.28/5.52  unary                                   10
% 39.28/5.52  binary                                  4
% 39.28/5.52  lits                                    18
% 39.28/5.52  lits eq                                 8
% 39.28/5.52  fd_pure                                 0
% 39.28/5.52  fd_pseudo                               0
% 39.28/5.52  fd_cond                                 1
% 39.28/5.52  fd_pseudo_cond                          0
% 39.28/5.52  AC symbols                              0
% 39.28/5.52  
% 39.28/5.52  ------ Schedule dynamic 5 is on 
% 39.28/5.52  
% 39.28/5.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.28/5.52  
% 39.28/5.52  
% 39.28/5.52  ------ 
% 39.28/5.52  Current options:
% 39.28/5.52  ------ 
% 39.28/5.52  
% 39.28/5.52  ------ Input Options
% 39.28/5.52  
% 39.28/5.52  --out_options                           all
% 39.28/5.52  --tptp_safe_out                         true
% 39.28/5.52  --problem_path                          ""
% 39.28/5.52  --include_path                          ""
% 39.28/5.52  --clausifier                            res/vclausify_rel
% 39.28/5.52  --clausifier_options                    ""
% 39.28/5.52  --stdin                                 false
% 39.28/5.52  --stats_out                             all
% 39.28/5.52  
% 39.28/5.52  ------ General Options
% 39.28/5.52  
% 39.28/5.52  --fof                                   false
% 39.28/5.52  --time_out_real                         305.
% 39.28/5.52  --time_out_virtual                      -1.
% 39.28/5.52  --symbol_type_check                     false
% 39.28/5.52  --clausify_out                          false
% 39.28/5.52  --sig_cnt_out                           false
% 39.28/5.52  --trig_cnt_out                          false
% 39.28/5.52  --trig_cnt_out_tolerance                1.
% 39.28/5.52  --trig_cnt_out_sk_spl                   false
% 39.28/5.52  --abstr_cl_out                          false
% 39.28/5.52  
% 39.28/5.52  ------ Global Options
% 39.28/5.52  
% 39.28/5.52  --schedule                              default
% 39.28/5.52  --add_important_lit                     false
% 39.28/5.52  --prop_solver_per_cl                    1000
% 39.28/5.52  --min_unsat_core                        false
% 39.28/5.52  --soft_assumptions                      false
% 39.28/5.52  --soft_lemma_size                       3
% 39.28/5.52  --prop_impl_unit_size                   0
% 39.28/5.52  --prop_impl_unit                        []
% 39.28/5.52  --share_sel_clauses                     true
% 39.28/5.52  --reset_solvers                         false
% 39.28/5.52  --bc_imp_inh                            [conj_cone]
% 39.28/5.52  --conj_cone_tolerance                   3.
% 39.28/5.52  --extra_neg_conj                        none
% 39.28/5.52  --large_theory_mode                     true
% 39.28/5.52  --prolific_symb_bound                   200
% 39.28/5.52  --lt_threshold                          2000
% 39.28/5.52  --clause_weak_htbl                      true
% 39.28/5.52  --gc_record_bc_elim                     false
% 39.28/5.52  
% 39.28/5.52  ------ Preprocessing Options
% 39.28/5.52  
% 39.28/5.52  --preprocessing_flag                    true
% 39.28/5.52  --time_out_prep_mult                    0.1
% 39.28/5.52  --splitting_mode                        input
% 39.28/5.52  --splitting_grd                         true
% 39.28/5.52  --splitting_cvd                         false
% 39.28/5.52  --splitting_cvd_svl                     false
% 39.28/5.52  --splitting_nvd                         32
% 39.28/5.52  --sub_typing                            true
% 39.28/5.52  --prep_gs_sim                           true
% 39.28/5.52  --prep_unflatten                        true
% 39.28/5.52  --prep_res_sim                          true
% 39.28/5.52  --prep_upred                            true
% 39.28/5.52  --prep_sem_filter                       exhaustive
% 39.28/5.52  --prep_sem_filter_out                   false
% 39.28/5.52  --pred_elim                             true
% 39.28/5.52  --res_sim_input                         true
% 39.28/5.52  --eq_ax_congr_red                       true
% 39.28/5.52  --pure_diseq_elim                       true
% 39.28/5.52  --brand_transform                       false
% 39.28/5.52  --non_eq_to_eq                          false
% 39.28/5.52  --prep_def_merge                        true
% 39.28/5.52  --prep_def_merge_prop_impl              false
% 39.28/5.52  --prep_def_merge_mbd                    true
% 39.28/5.52  --prep_def_merge_tr_red                 false
% 39.28/5.52  --prep_def_merge_tr_cl                  false
% 39.28/5.52  --smt_preprocessing                     true
% 39.28/5.52  --smt_ac_axioms                         fast
% 39.28/5.52  --preprocessed_out                      false
% 39.28/5.52  --preprocessed_stats                    false
% 39.28/5.52  
% 39.28/5.52  ------ Abstraction refinement Options
% 39.28/5.52  
% 39.28/5.52  --abstr_ref                             []
% 39.28/5.52  --abstr_ref_prep                        false
% 39.28/5.52  --abstr_ref_until_sat                   false
% 39.28/5.52  --abstr_ref_sig_restrict                funpre
% 39.28/5.52  --abstr_ref_af_restrict_to_split_sk     false
% 39.28/5.52  --abstr_ref_under                       []
% 39.28/5.52  
% 39.28/5.52  ------ SAT Options
% 39.28/5.52  
% 39.28/5.52  --sat_mode                              false
% 39.28/5.52  --sat_fm_restart_options                ""
% 39.28/5.52  --sat_gr_def                            false
% 39.28/5.52  --sat_epr_types                         true
% 39.28/5.52  --sat_non_cyclic_types                  false
% 39.28/5.52  --sat_finite_models                     false
% 39.28/5.52  --sat_fm_lemmas                         false
% 39.28/5.52  --sat_fm_prep                           false
% 39.28/5.52  --sat_fm_uc_incr                        true
% 39.28/5.52  --sat_out_model                         small
% 39.28/5.52  --sat_out_clauses                       false
% 39.28/5.52  
% 39.28/5.52  ------ QBF Options
% 39.28/5.52  
% 39.28/5.52  --qbf_mode                              false
% 39.28/5.52  --qbf_elim_univ                         false
% 39.28/5.52  --qbf_dom_inst                          none
% 39.28/5.52  --qbf_dom_pre_inst                      false
% 39.28/5.52  --qbf_sk_in                             false
% 39.28/5.52  --qbf_pred_elim                         true
% 39.28/5.52  --qbf_split                             512
% 39.28/5.52  
% 39.28/5.52  ------ BMC1 Options
% 39.28/5.52  
% 39.28/5.52  --bmc1_incremental                      false
% 39.28/5.52  --bmc1_axioms                           reachable_all
% 39.28/5.52  --bmc1_min_bound                        0
% 39.28/5.52  --bmc1_max_bound                        -1
% 39.28/5.52  --bmc1_max_bound_default                -1
% 39.28/5.52  --bmc1_symbol_reachability              true
% 39.28/5.52  --bmc1_property_lemmas                  false
% 39.28/5.52  --bmc1_k_induction                      false
% 39.28/5.52  --bmc1_non_equiv_states                 false
% 39.28/5.52  --bmc1_deadlock                         false
% 39.28/5.52  --bmc1_ucm                              false
% 39.28/5.52  --bmc1_add_unsat_core                   none
% 39.28/5.52  --bmc1_unsat_core_children              false
% 39.28/5.52  --bmc1_unsat_core_extrapolate_axioms    false
% 39.28/5.52  --bmc1_out_stat                         full
% 39.28/5.52  --bmc1_ground_init                      false
% 39.28/5.52  --bmc1_pre_inst_next_state              false
% 39.28/5.52  --bmc1_pre_inst_state                   false
% 39.28/5.52  --bmc1_pre_inst_reach_state             false
% 39.28/5.52  --bmc1_out_unsat_core                   false
% 39.28/5.52  --bmc1_aig_witness_out                  false
% 39.28/5.52  --bmc1_verbose                          false
% 39.28/5.52  --bmc1_dump_clauses_tptp                false
% 39.28/5.52  --bmc1_dump_unsat_core_tptp             false
% 39.28/5.52  --bmc1_dump_file                        -
% 39.28/5.52  --bmc1_ucm_expand_uc_limit              128
% 39.28/5.52  --bmc1_ucm_n_expand_iterations          6
% 39.28/5.52  --bmc1_ucm_extend_mode                  1
% 39.28/5.52  --bmc1_ucm_init_mode                    2
% 39.28/5.52  --bmc1_ucm_cone_mode                    none
% 39.28/5.52  --bmc1_ucm_reduced_relation_type        0
% 39.28/5.52  --bmc1_ucm_relax_model                  4
% 39.28/5.52  --bmc1_ucm_full_tr_after_sat            true
% 39.28/5.52  --bmc1_ucm_expand_neg_assumptions       false
% 39.28/5.52  --bmc1_ucm_layered_model                none
% 39.28/5.52  --bmc1_ucm_max_lemma_size               10
% 39.28/5.52  
% 39.28/5.52  ------ AIG Options
% 39.28/5.52  
% 39.28/5.52  --aig_mode                              false
% 39.28/5.52  
% 39.28/5.52  ------ Instantiation Options
% 39.28/5.52  
% 39.28/5.52  --instantiation_flag                    true
% 39.28/5.52  --inst_sos_flag                         true
% 39.28/5.52  --inst_sos_phase                        true
% 39.28/5.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.28/5.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.28/5.52  --inst_lit_sel_side                     none
% 39.28/5.52  --inst_solver_per_active                1400
% 39.28/5.52  --inst_solver_calls_frac                1.
% 39.28/5.52  --inst_passive_queue_type               priority_queues
% 39.28/5.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.28/5.52  --inst_passive_queues_freq              [25;2]
% 39.28/5.52  --inst_dismatching                      true
% 39.28/5.52  --inst_eager_unprocessed_to_passive     true
% 39.28/5.52  --inst_prop_sim_given                   true
% 39.28/5.52  --inst_prop_sim_new                     false
% 39.28/5.52  --inst_subs_new                         false
% 39.28/5.52  --inst_eq_res_simp                      false
% 39.28/5.52  --inst_subs_given                       false
% 39.28/5.52  --inst_orphan_elimination               true
% 39.28/5.52  --inst_learning_loop_flag               true
% 39.28/5.52  --inst_learning_start                   3000
% 39.28/5.52  --inst_learning_factor                  2
% 39.28/5.52  --inst_start_prop_sim_after_learn       3
% 39.28/5.52  --inst_sel_renew                        solver
% 39.28/5.52  --inst_lit_activity_flag                true
% 39.28/5.52  --inst_restr_to_given                   false
% 39.28/5.52  --inst_activity_threshold               500
% 39.28/5.52  --inst_out_proof                        true
% 39.28/5.52  
% 39.28/5.52  ------ Resolution Options
% 39.28/5.52  
% 39.28/5.52  --resolution_flag                       false
% 39.28/5.52  --res_lit_sel                           adaptive
% 39.28/5.52  --res_lit_sel_side                      none
% 39.28/5.52  --res_ordering                          kbo
% 39.28/5.52  --res_to_prop_solver                    active
% 39.28/5.52  --res_prop_simpl_new                    false
% 39.28/5.52  --res_prop_simpl_given                  true
% 39.28/5.52  --res_passive_queue_type                priority_queues
% 39.28/5.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.28/5.52  --res_passive_queues_freq               [15;5]
% 39.28/5.52  --res_forward_subs                      full
% 39.28/5.52  --res_backward_subs                     full
% 39.28/5.52  --res_forward_subs_resolution           true
% 39.28/5.52  --res_backward_subs_resolution          true
% 39.28/5.52  --res_orphan_elimination                true
% 39.28/5.52  --res_time_limit                        2.
% 39.28/5.52  --res_out_proof                         true
% 39.28/5.52  
% 39.28/5.52  ------ Superposition Options
% 39.28/5.52  
% 39.28/5.52  --superposition_flag                    true
% 39.28/5.52  --sup_passive_queue_type                priority_queues
% 39.28/5.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.28/5.52  --sup_passive_queues_freq               [8;1;4]
% 39.28/5.52  --demod_completeness_check              fast
% 39.28/5.52  --demod_use_ground                      true
% 39.28/5.52  --sup_to_prop_solver                    passive
% 39.28/5.52  --sup_prop_simpl_new                    true
% 39.28/5.52  --sup_prop_simpl_given                  true
% 39.28/5.52  --sup_fun_splitting                     true
% 39.28/5.52  --sup_smt_interval                      50000
% 39.28/5.52  
% 39.28/5.52  ------ Superposition Simplification Setup
% 39.28/5.52  
% 39.28/5.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.28/5.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.28/5.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.28/5.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.28/5.52  --sup_full_triv                         [TrivRules;PropSubs]
% 39.28/5.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.28/5.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.28/5.52  --sup_immed_triv                        [TrivRules]
% 39.28/5.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.28/5.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.28/5.52  --sup_immed_bw_main                     []
% 39.28/5.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.28/5.52  --sup_input_triv                        [Unflattening;TrivRules]
% 39.28/5.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.28/5.52  --sup_input_bw                          []
% 39.28/5.52  
% 39.28/5.52  ------ Combination Options
% 39.28/5.52  
% 39.28/5.52  --comb_res_mult                         3
% 39.28/5.52  --comb_sup_mult                         2
% 39.28/5.52  --comb_inst_mult                        10
% 39.28/5.52  
% 39.28/5.52  ------ Debug Options
% 39.28/5.52  
% 39.28/5.52  --dbg_backtrace                         false
% 39.28/5.52  --dbg_dump_prop_clauses                 false
% 39.28/5.52  --dbg_dump_prop_clauses_file            -
% 39.28/5.52  --dbg_out_stat                          false
% 39.28/5.52  
% 39.28/5.52  
% 39.28/5.52  
% 39.28/5.52  
% 39.28/5.52  ------ Proving...
% 39.28/5.52  
% 39.28/5.52  
% 39.28/5.52  % SZS status Theorem for theBenchmark.p
% 39.28/5.52  
% 39.28/5.52  % SZS output start CNFRefutation for theBenchmark.p
% 39.28/5.52  
% 39.28/5.52  fof(f13,conjecture,(
% 39.28/5.52    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f14,negated_conjecture,(
% 39.28/5.52    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 39.28/5.52    inference(negated_conjecture,[],[f13])).
% 39.28/5.52  
% 39.28/5.52  fof(f21,plain,(
% 39.28/5.52    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 39.28/5.52    inference(ennf_transformation,[],[f14])).
% 39.28/5.52  
% 39.28/5.52  fof(f26,plain,(
% 39.28/5.52    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) & r1_tarski(sK2,sK4) & ~r1_xboole_0(sK2,sK3))),
% 39.28/5.52    introduced(choice_axiom,[])).
% 39.28/5.52  
% 39.28/5.52  fof(f27,plain,(
% 39.28/5.52    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) & r1_tarski(sK2,sK4) & ~r1_xboole_0(sK2,sK3)),
% 39.28/5.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f26])).
% 39.28/5.52  
% 39.28/5.52  fof(f43,plain,(
% 39.28/5.52    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))),
% 39.28/5.52    inference(cnf_transformation,[],[f27])).
% 39.28/5.52  
% 39.28/5.52  fof(f10,axiom,(
% 39.28/5.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f38,plain,(
% 39.28/5.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.28/5.52    inference(cnf_transformation,[],[f10])).
% 39.28/5.52  
% 39.28/5.52  fof(f49,plain,(
% 39.28/5.52    r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))),
% 39.28/5.52    inference(definition_unfolding,[],[f43,f38])).
% 39.28/5.52  
% 39.28/5.52  fof(f4,axiom,(
% 39.28/5.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f19,plain,(
% 39.28/5.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 39.28/5.52    inference(ennf_transformation,[],[f4])).
% 39.28/5.52  
% 39.28/5.52  fof(f24,plain,(
% 39.28/5.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 39.28/5.52    introduced(choice_axiom,[])).
% 39.28/5.52  
% 39.28/5.52  fof(f25,plain,(
% 39.28/5.52    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 39.28/5.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).
% 39.28/5.52  
% 39.28/5.52  fof(f32,plain,(
% 39.28/5.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 39.28/5.52    inference(cnf_transformation,[],[f25])).
% 39.28/5.52  
% 39.28/5.52  fof(f3,axiom,(
% 39.28/5.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f15,plain,(
% 39.28/5.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 39.28/5.52    inference(rectify,[],[f3])).
% 39.28/5.52  
% 39.28/5.52  fof(f18,plain,(
% 39.28/5.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 39.28/5.52    inference(ennf_transformation,[],[f15])).
% 39.28/5.52  
% 39.28/5.52  fof(f22,plain,(
% 39.28/5.52    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 39.28/5.52    introduced(choice_axiom,[])).
% 39.28/5.52  
% 39.28/5.52  fof(f23,plain,(
% 39.28/5.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 39.28/5.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).
% 39.28/5.52  
% 39.28/5.52  fof(f31,plain,(
% 39.28/5.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 39.28/5.52    inference(cnf_transformation,[],[f23])).
% 39.28/5.52  
% 39.28/5.52  fof(f44,plain,(
% 39.28/5.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 39.28/5.52    inference(definition_unfolding,[],[f31,f38])).
% 39.28/5.52  
% 39.28/5.52  fof(f7,axiom,(
% 39.28/5.52    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f35,plain,(
% 39.28/5.52    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 39.28/5.52    inference(cnf_transformation,[],[f7])).
% 39.28/5.52  
% 39.28/5.52  fof(f47,plain,(
% 39.28/5.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 39.28/5.52    inference(definition_unfolding,[],[f35,f38])).
% 39.28/5.52  
% 39.28/5.52  fof(f9,axiom,(
% 39.28/5.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f37,plain,(
% 39.28/5.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.28/5.52    inference(cnf_transformation,[],[f9])).
% 39.28/5.52  
% 39.28/5.52  fof(f6,axiom,(
% 39.28/5.52    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f34,plain,(
% 39.28/5.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 39.28/5.52    inference(cnf_transformation,[],[f6])).
% 39.28/5.52  
% 39.28/5.52  fof(f46,plain,(
% 39.28/5.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 39.28/5.52    inference(definition_unfolding,[],[f34,f38,f38,f38,f38])).
% 39.28/5.52  
% 39.28/5.52  fof(f11,axiom,(
% 39.28/5.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f39,plain,(
% 39.28/5.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 39.28/5.52    inference(cnf_transformation,[],[f11])).
% 39.28/5.52  
% 39.28/5.52  fof(f48,plain,(
% 39.28/5.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 39.28/5.52    inference(definition_unfolding,[],[f39,f38])).
% 39.28/5.52  
% 39.28/5.52  fof(f1,axiom,(
% 39.28/5.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f28,plain,(
% 39.28/5.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 39.28/5.52    inference(cnf_transformation,[],[f1])).
% 39.28/5.52  
% 39.28/5.52  fof(f8,axiom,(
% 39.28/5.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f36,plain,(
% 39.28/5.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 39.28/5.52    inference(cnf_transformation,[],[f8])).
% 39.28/5.52  
% 39.28/5.52  fof(f5,axiom,(
% 39.28/5.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f16,plain,(
% 39.28/5.52    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 39.28/5.52    inference(unused_predicate_definition_removal,[],[f5])).
% 39.28/5.52  
% 39.28/5.52  fof(f20,plain,(
% 39.28/5.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 39.28/5.52    inference(ennf_transformation,[],[f16])).
% 39.28/5.52  
% 39.28/5.52  fof(f33,plain,(
% 39.28/5.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 39.28/5.52    inference(cnf_transformation,[],[f20])).
% 39.28/5.52  
% 39.28/5.52  fof(f42,plain,(
% 39.28/5.52    r1_tarski(sK2,sK4)),
% 39.28/5.52    inference(cnf_transformation,[],[f27])).
% 39.28/5.52  
% 39.28/5.52  fof(f30,plain,(
% 39.28/5.52    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 39.28/5.52    inference(cnf_transformation,[],[f23])).
% 39.28/5.52  
% 39.28/5.52  fof(f45,plain,(
% 39.28/5.52    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 39.28/5.52    inference(definition_unfolding,[],[f30,f38])).
% 39.28/5.52  
% 39.28/5.52  fof(f2,axiom,(
% 39.28/5.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 39.28/5.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.28/5.52  
% 39.28/5.52  fof(f17,plain,(
% 39.28/5.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 39.28/5.52    inference(ennf_transformation,[],[f2])).
% 39.28/5.52  
% 39.28/5.52  fof(f29,plain,(
% 39.28/5.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 39.28/5.52    inference(cnf_transformation,[],[f17])).
% 39.28/5.52  
% 39.28/5.52  fof(f41,plain,(
% 39.28/5.52    ~r1_xboole_0(sK2,sK3)),
% 39.28/5.52    inference(cnf_transformation,[],[f27])).
% 39.28/5.52  
% 39.28/5.52  cnf(c_12,negated_conjecture,
% 39.28/5.52      ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
% 39.28/5.52      inference(cnf_transformation,[],[f49]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_367,plain,
% 39.28/5.52      ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 39.28/5.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_4,plain,
% 39.28/5.52      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 39.28/5.52      inference(cnf_transformation,[],[f32]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_369,plain,
% 39.28/5.52      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 39.28/5.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_2,plain,
% 39.28/5.52      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 39.28/5.52      | ~ r1_xboole_0(X1,X2) ),
% 39.28/5.52      inference(cnf_transformation,[],[f44]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_371,plain,
% 39.28/5.52      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 39.28/5.52      | r1_xboole_0(X1,X2) != iProver_top ),
% 39.28/5.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_1854,plain,
% 39.28/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 39.28/5.52      | r1_xboole_0(X0,X1) != iProver_top ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_369,c_371]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_70169,plain,
% 39.28/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k1_xboole_0 ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_367,c_1854]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_7,plain,
% 39.28/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 39.28/5.52      inference(cnf_transformation,[],[f47]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_9,plain,
% 39.28/5.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.28/5.52      inference(cnf_transformation,[],[f37]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_373,plain,
% 39.28/5.52      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.28/5.52      inference(light_normalisation,[status(thm)],[c_7,c_9]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_6,plain,
% 39.28/5.52      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 39.28/5.52      inference(cnf_transformation,[],[f46]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_10,plain,
% 39.28/5.52      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 39.28/5.52      inference(cnf_transformation,[],[f48]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_0,plain,
% 39.28/5.52      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 39.28/5.52      inference(cnf_transformation,[],[f28]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_696,plain,
% 39.28/5.52      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_8,plain,
% 39.28/5.52      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 39.28/5.52      inference(cnf_transformation,[],[f36]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_1502,plain,
% 39.28/5.52      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_696,c_8]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_1938,plain,
% 39.28/5.52      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_6,c_1502]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_13808,plain,
% 39.28/5.52      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_373,c_1938]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_1943,plain,
% 39.28/5.52      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_1502,c_0]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_1949,plain,
% 39.28/5.52      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_6,c_1943]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_13954,plain,
% 39.28/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 39.28/5.52      inference(demodulation,[status(thm)],[c_13808,c_6,c_9,c_1949]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_668,plain,
% 39.28/5.52      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_672,plain,
% 39.28/5.52      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
% 39.28/5.52      inference(demodulation,[status(thm)],[c_668,c_6]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_14174,plain,
% 39.28/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_13954,c_672]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_14392,plain,
% 39.28/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 39.28/5.52      inference(light_normalisation,[status(thm)],[c_14174,c_6]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_71998,plain,
% 39.28/5.52      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) ),
% 39.28/5.52      inference(superposition,[status(thm)],[c_70169,c_14392]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_5,plain,
% 39.28/5.52      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 39.28/5.52      inference(cnf_transformation,[],[f33]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_13,negated_conjecture,
% 39.28/5.52      ( r1_tarski(sK2,sK4) ),
% 39.28/5.52      inference(cnf_transformation,[],[f42]) ).
% 39.28/5.52  
% 39.28/5.52  cnf(c_112,plain,
% 39.28/5.53      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK4 != X1 | sK2 != X0 ),
% 39.28/5.53      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_113,plain,
% 39.28/5.53      ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
% 39.28/5.53      inference(unflattening,[status(thm)],[c_112]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_73386,plain,
% 39.28/5.53      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k1_xboole_0))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) ),
% 39.28/5.53      inference(light_normalisation,[status(thm)],[c_71998,c_113]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_73387,plain,
% 39.28/5.53      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 39.28/5.53      inference(demodulation,[status(thm)],[c_73386,c_9,c_373]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_383,plain,
% 39.28/5.53      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))))
% 39.28/5.53      | ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_2]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_5581,plain,
% 39.28/5.53      ( ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))))
% 39.28/5.53      | ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_383]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_235,plain,
% 39.28/5.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.28/5.53      theory(equality) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_477,plain,
% 39.28/5.53      ( r2_hidden(X0,X1)
% 39.28/5.53      | ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
% 39.28/5.53      | X0 != sK0(sK3,sK2)
% 39.28/5.53      | X1 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_235]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_515,plain,
% 39.28/5.53      ( r2_hidden(sK0(sK3,sK2),X0)
% 39.28/5.53      | ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
% 39.28/5.53      | X0 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))
% 39.28/5.53      | sK0(sK3,sK2) != sK0(sK3,sK2) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_477]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_1151,plain,
% 39.28/5.53      ( r2_hidden(sK0(sK3,sK2),k4_xboole_0(X0,X1))
% 39.28/5.53      | ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
% 39.28/5.53      | sK0(sK3,sK2) != sK0(sK3,sK2)
% 39.28/5.53      | k4_xboole_0(X0,X1) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_515]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_5580,plain,
% 39.28/5.53      ( ~ r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
% 39.28/5.53      | r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))))
% 39.28/5.53      | sK0(sK3,sK2) != sK0(sK3,sK2)
% 39.28/5.53      | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_1151]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_230,plain,( X0 = X0 ),theory(equality) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_609,plain,
% 39.28/5.53      ( sK0(sK3,sK2) = sK0(sK3,sK2) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_230]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_231,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_462,plain,
% 39.28/5.53      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) != X0
% 39.28/5.53      | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) != X0
% 39.28/5.53      | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_231]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_463,plain,
% 39.28/5.53      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) != k1_xboole_0
% 39.28/5.53      | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))
% 39.28/5.53      | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) != k1_xboole_0 ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_462]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_3,plain,
% 39.28/5.53      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 39.28/5.53      | r1_xboole_0(X0,X1) ),
% 39.28/5.53      inference(cnf_transformation,[],[f45]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_400,plain,
% 39.28/5.53      ( r2_hidden(sK0(sK3,sK2),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
% 39.28/5.53      | r1_xboole_0(sK3,sK2) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_3]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_1,plain,
% 39.28/5.53      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 39.28/5.53      inference(cnf_transformation,[],[f29]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_391,plain,
% 39.28/5.53      ( ~ r1_xboole_0(sK3,sK2) | r1_xboole_0(sK2,sK3) ),
% 39.28/5.53      inference(instantiation,[status(thm)],[c_1]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(c_14,negated_conjecture,
% 39.28/5.53      ( ~ r1_xboole_0(sK2,sK3) ),
% 39.28/5.53      inference(cnf_transformation,[],[f41]) ).
% 39.28/5.53  
% 39.28/5.53  cnf(contradiction,plain,
% 39.28/5.53      ( $false ),
% 39.28/5.53      inference(minisat,
% 39.28/5.53                [status(thm)],
% 39.28/5.53                [c_73387,c_70169,c_5581,c_5580,c_609,c_463,c_400,c_391,
% 39.28/5.53                 c_12,c_14]) ).
% 39.28/5.53  
% 39.28/5.53  
% 39.28/5.53  % SZS output end CNFRefutation for theBenchmark.p
% 39.28/5.53  
% 39.28/5.53  ------                               Statistics
% 39.28/5.53  
% 39.28/5.53  ------ General
% 39.28/5.53  
% 39.28/5.53  abstr_ref_over_cycles:                  0
% 39.28/5.53  abstr_ref_under_cycles:                 0
% 39.28/5.53  gc_basic_clause_elim:                   0
% 39.28/5.53  forced_gc_time:                         0
% 39.28/5.53  parsing_time:                           0.016
% 39.28/5.53  unif_index_cands_time:                  0.
% 39.28/5.53  unif_index_add_time:                    0.
% 39.28/5.53  orderings_time:                         0.
% 39.28/5.53  out_proof_time:                         0.014
% 39.28/5.53  total_time:                             4.729
% 39.28/5.53  num_of_symbols:                         42
% 39.28/5.53  num_of_terms:                           151844
% 39.28/5.53  
% 39.28/5.53  ------ Preprocessing
% 39.28/5.53  
% 39.28/5.53  num_of_splits:                          0
% 39.28/5.53  num_of_split_atoms:                     0
% 39.28/5.53  num_of_reused_defs:                     0
% 39.28/5.53  num_eq_ax_congr_red:                    9
% 39.28/5.53  num_of_sem_filtered_clauses:            1
% 39.28/5.53  num_of_subtypes:                        0
% 39.28/5.53  monotx_restored_types:                  0
% 39.28/5.53  sat_num_of_epr_types:                   0
% 39.28/5.53  sat_num_of_non_cyclic_types:            0
% 39.28/5.53  sat_guarded_non_collapsed_types:        0
% 39.28/5.53  num_pure_diseq_elim:                    0
% 39.28/5.53  simp_replaced_by:                       0
% 39.28/5.53  res_preprocessed:                       70
% 39.28/5.53  prep_upred:                             0
% 39.28/5.53  prep_unflattend:                        8
% 39.28/5.53  smt_new_axioms:                         0
% 39.28/5.53  pred_elim_cands:                        2
% 39.28/5.53  pred_elim:                              1
% 39.28/5.53  pred_elim_cl:                           1
% 39.28/5.53  pred_elim_cycles:                       3
% 39.28/5.53  merged_defs:                            0
% 39.28/5.53  merged_defs_ncl:                        0
% 39.28/5.53  bin_hyper_res:                          0
% 39.28/5.53  prep_cycles:                            4
% 39.28/5.53  pred_elim_time:                         0.001
% 39.28/5.53  splitting_time:                         0.
% 39.28/5.53  sem_filter_time:                        0.
% 39.28/5.53  monotx_time:                            0.
% 39.28/5.53  subtype_inf_time:                       0.
% 39.28/5.53  
% 39.28/5.53  ------ Problem properties
% 39.28/5.53  
% 39.28/5.53  clauses:                                14
% 39.28/5.53  conjectures:                            2
% 39.28/5.53  epr:                                    3
% 39.28/5.53  horn:                                   12
% 39.28/5.53  ground:                                 3
% 39.28/5.53  unary:                                  10
% 39.28/5.53  binary:                                 4
% 39.28/5.53  lits:                                   18
% 39.28/5.53  lits_eq:                                8
% 39.28/5.53  fd_pure:                                0
% 39.28/5.53  fd_pseudo:                              0
% 39.28/5.53  fd_cond:                                1
% 39.28/5.53  fd_pseudo_cond:                         0
% 39.28/5.53  ac_symbols:                             0
% 39.28/5.53  
% 39.28/5.53  ------ Propositional Solver
% 39.28/5.53  
% 39.28/5.53  prop_solver_calls:                      35
% 39.28/5.53  prop_fast_solver_calls:                 584
% 39.28/5.53  smt_solver_calls:                       0
% 39.28/5.53  smt_fast_solver_calls:                  0
% 39.28/5.53  prop_num_of_clauses:                    16921
% 39.28/5.53  prop_preprocess_simplified:             12034
% 39.28/5.53  prop_fo_subsumed:                       7
% 39.28/5.53  prop_solver_time:                       0.
% 39.28/5.53  smt_solver_time:                        0.
% 39.28/5.53  smt_fast_solver_time:                   0.
% 39.28/5.53  prop_fast_solver_time:                  0.
% 39.28/5.53  prop_unsat_core_time:                   0.002
% 39.28/5.53  
% 39.28/5.53  ------ QBF
% 39.28/5.53  
% 39.28/5.53  qbf_q_res:                              0
% 39.28/5.53  qbf_num_tautologies:                    0
% 39.28/5.53  qbf_prep_cycles:                        0
% 39.28/5.53  
% 39.28/5.53  ------ BMC1
% 39.28/5.53  
% 39.28/5.53  bmc1_current_bound:                     -1
% 39.28/5.53  bmc1_last_solved_bound:                 -1
% 39.28/5.53  bmc1_unsat_core_size:                   -1
% 39.28/5.53  bmc1_unsat_core_parents_size:           -1
% 39.28/5.53  bmc1_merge_next_fun:                    0
% 39.28/5.53  bmc1_unsat_core_clauses_time:           0.
% 39.28/5.53  
% 39.28/5.53  ------ Instantiation
% 39.28/5.53  
% 39.28/5.53  inst_num_of_clauses:                    2449
% 39.28/5.53  inst_num_in_passive:                    525
% 39.28/5.53  inst_num_in_active:                     1051
% 39.28/5.53  inst_num_in_unprocessed:                873
% 39.28/5.53  inst_num_of_loops:                      1240
% 39.28/5.53  inst_num_of_learning_restarts:          0
% 39.28/5.53  inst_num_moves_active_passive:          183
% 39.28/5.53  inst_lit_activity:                      0
% 39.28/5.53  inst_lit_activity_moves:                0
% 39.28/5.53  inst_num_tautologies:                   0
% 39.28/5.53  inst_num_prop_implied:                  0
% 39.28/5.53  inst_num_existing_simplified:           0
% 39.28/5.53  inst_num_eq_res_simplified:             0
% 39.28/5.53  inst_num_child_elim:                    0
% 39.28/5.53  inst_num_of_dismatching_blockings:      1039
% 39.28/5.53  inst_num_of_non_proper_insts:           2477
% 39.28/5.53  inst_num_of_duplicates:                 0
% 39.28/5.53  inst_inst_num_from_inst_to_res:         0
% 39.28/5.53  inst_dismatching_checking_time:         0.
% 39.28/5.53  
% 39.28/5.53  ------ Resolution
% 39.28/5.53  
% 39.28/5.53  res_num_of_clauses:                     0
% 39.28/5.53  res_num_in_passive:                     0
% 39.28/5.53  res_num_in_active:                      0
% 39.28/5.53  res_num_of_loops:                       74
% 39.28/5.53  res_forward_subset_subsumed:            228
% 39.28/5.53  res_backward_subset_subsumed:           0
% 39.28/5.53  res_forward_subsumed:                   0
% 39.28/5.53  res_backward_subsumed:                  0
% 39.28/5.53  res_forward_subsumption_resolution:     0
% 39.28/5.53  res_backward_subsumption_resolution:    0
% 39.28/5.53  res_clause_to_clause_subsumption:       49676
% 39.28/5.53  res_orphan_elimination:                 0
% 39.28/5.53  res_tautology_del:                      230
% 39.28/5.53  res_num_eq_res_simplified:              0
% 39.28/5.53  res_num_sel_changes:                    0
% 39.28/5.53  res_moves_from_active_to_pass:          0
% 39.28/5.53  
% 39.28/5.53  ------ Superposition
% 39.28/5.53  
% 39.28/5.53  sup_time_total:                         0.
% 39.28/5.53  sup_time_generating:                    0.
% 39.28/5.53  sup_time_sim_full:                      0.
% 39.28/5.53  sup_time_sim_immed:                     0.
% 39.28/5.53  
% 39.28/5.53  sup_num_of_clauses:                     4221
% 39.28/5.53  sup_num_in_active:                      179
% 39.28/5.53  sup_num_in_passive:                     4042
% 39.28/5.53  sup_num_of_loops:                       247
% 39.28/5.53  sup_fw_superposition:                   9479
% 39.28/5.53  sup_bw_superposition:                   14943
% 39.28/5.53  sup_immediate_simplified:               18322
% 39.28/5.53  sup_given_eliminated:                   47
% 39.28/5.53  comparisons_done:                       0
% 39.28/5.53  comparisons_avoided:                    0
% 39.28/5.53  
% 39.28/5.53  ------ Simplifications
% 39.28/5.53  
% 39.28/5.53  
% 39.28/5.53  sim_fw_subset_subsumed:                 257
% 39.28/5.53  sim_bw_subset_subsumed:                 5
% 39.28/5.53  sim_fw_subsumed:                        1965
% 39.28/5.53  sim_bw_subsumed:                        96
% 39.28/5.53  sim_fw_subsumption_res:                 0
% 39.28/5.53  sim_bw_subsumption_res:                 0
% 39.28/5.53  sim_tautology_del:                      224
% 39.28/5.53  sim_eq_tautology_del:                   9059
% 39.28/5.53  sim_eq_res_simp:                        0
% 39.28/5.53  sim_fw_demodulated:                     20689
% 39.28/5.53  sim_bw_demodulated:                     672
% 39.28/5.53  sim_light_normalised:                   6401
% 39.28/5.53  sim_joinable_taut:                      0
% 39.28/5.53  sim_joinable_simp:                      0
% 39.28/5.53  sim_ac_normalised:                      0
% 39.28/5.53  sim_smt_subsumption:                    0
% 39.28/5.53  
%------------------------------------------------------------------------------
