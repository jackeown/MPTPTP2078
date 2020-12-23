%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:49 EST 2020

% Result     : Theorem 15.67s
% Output     : CNFRefutation 15.67s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 307 expanded)
%              Number of clauses        :   51 ( 113 expanded)
%              Number of leaves         :   12 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  142 ( 487 expanded)
%              Number of equality atoms :   73 ( 247 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f32,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f30,f26,f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_521,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_671,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_521])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_516,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_617,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_516])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_520,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_976,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_617,c_520])).

cnf(c_8,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_518,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1311,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_518])).

cnf(c_57877,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X1,X3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1311])).

cnf(c_59011,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_xboole_0(X0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_57877])).

cnf(c_59968,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_59011])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8068,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | r1_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8069,plain,
    ( r1_xboole_0(sK2,sK0) != iProver_top
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8068])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_519,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_837,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_519])).

cnf(c_2098,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_837])).

cnf(c_4333,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_2098])).

cnf(c_4951,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_4333,c_520])).

cnf(c_827,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_4137,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_827])).

cnf(c_5334,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_4951,c_4137])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_523,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3035,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_617,c_523])).

cnf(c_3084,plain,
    ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3035,c_976])).

cnf(c_3037,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_671,c_523])).

cnf(c_3076,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3037,c_1])).

cnf(c_983,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_976,c_8])).

cnf(c_1051,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) ),
    inference(superposition,[status(thm)],[c_1,c_983])).

cnf(c_1058,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k5_xboole_0(sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1051,c_976])).

cnf(c_3199,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3076,c_1058])).

cnf(c_3207,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3199,c_3076])).

cnf(c_5373,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5334,c_3084,c_3207])).

cnf(c_974,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_521,c_520])).

cnf(c_5374,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5373,c_974])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_78,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_195,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_78,c_10])).

cnf(c_196,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_197,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
    | r1_xboole_0(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59968,c_8069,c_5374,c_197])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.67/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.67/2.49  
% 15.67/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.67/2.49  
% 15.67/2.49  ------  iProver source info
% 15.67/2.49  
% 15.67/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.67/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.67/2.49  git: non_committed_changes: false
% 15.67/2.49  git: last_make_outside_of_git: false
% 15.67/2.49  
% 15.67/2.49  ------ 
% 15.67/2.49  
% 15.67/2.49  ------ Input Options
% 15.67/2.49  
% 15.67/2.49  --out_options                           all
% 15.67/2.49  --tptp_safe_out                         true
% 15.67/2.49  --problem_path                          ""
% 15.67/2.49  --include_path                          ""
% 15.67/2.49  --clausifier                            res/vclausify_rel
% 15.67/2.49  --clausifier_options                    ""
% 15.67/2.49  --stdin                                 false
% 15.67/2.49  --stats_out                             all
% 15.67/2.49  
% 15.67/2.49  ------ General Options
% 15.67/2.49  
% 15.67/2.49  --fof                                   false
% 15.67/2.49  --time_out_real                         305.
% 15.67/2.49  --time_out_virtual                      -1.
% 15.67/2.49  --symbol_type_check                     false
% 15.67/2.49  --clausify_out                          false
% 15.67/2.49  --sig_cnt_out                           false
% 15.67/2.49  --trig_cnt_out                          false
% 15.67/2.49  --trig_cnt_out_tolerance                1.
% 15.67/2.49  --trig_cnt_out_sk_spl                   false
% 15.67/2.49  --abstr_cl_out                          false
% 15.67/2.49  
% 15.67/2.49  ------ Global Options
% 15.67/2.49  
% 15.67/2.49  --schedule                              default
% 15.67/2.49  --add_important_lit                     false
% 15.67/2.49  --prop_solver_per_cl                    1000
% 15.67/2.49  --min_unsat_core                        false
% 15.67/2.49  --soft_assumptions                      false
% 15.67/2.49  --soft_lemma_size                       3
% 15.67/2.49  --prop_impl_unit_size                   0
% 15.67/2.49  --prop_impl_unit                        []
% 15.67/2.49  --share_sel_clauses                     true
% 15.67/2.49  --reset_solvers                         false
% 15.67/2.49  --bc_imp_inh                            [conj_cone]
% 15.67/2.49  --conj_cone_tolerance                   3.
% 15.67/2.49  --extra_neg_conj                        none
% 15.67/2.49  --large_theory_mode                     true
% 15.67/2.49  --prolific_symb_bound                   200
% 15.67/2.49  --lt_threshold                          2000
% 15.67/2.49  --clause_weak_htbl                      true
% 15.67/2.49  --gc_record_bc_elim                     false
% 15.67/2.49  
% 15.67/2.49  ------ Preprocessing Options
% 15.67/2.49  
% 15.67/2.49  --preprocessing_flag                    true
% 15.67/2.49  --time_out_prep_mult                    0.1
% 15.67/2.49  --splitting_mode                        input
% 15.67/2.49  --splitting_grd                         true
% 15.67/2.49  --splitting_cvd                         false
% 15.67/2.49  --splitting_cvd_svl                     false
% 15.67/2.49  --splitting_nvd                         32
% 15.67/2.49  --sub_typing                            true
% 15.67/2.49  --prep_gs_sim                           true
% 15.67/2.49  --prep_unflatten                        true
% 15.67/2.49  --prep_res_sim                          true
% 15.67/2.49  --prep_upred                            true
% 15.67/2.49  --prep_sem_filter                       exhaustive
% 15.67/2.49  --prep_sem_filter_out                   false
% 15.67/2.49  --pred_elim                             true
% 15.67/2.49  --res_sim_input                         true
% 15.67/2.49  --eq_ax_congr_red                       true
% 15.67/2.49  --pure_diseq_elim                       true
% 15.67/2.49  --brand_transform                       false
% 15.67/2.49  --non_eq_to_eq                          false
% 15.67/2.49  --prep_def_merge                        true
% 15.67/2.49  --prep_def_merge_prop_impl              false
% 15.67/2.49  --prep_def_merge_mbd                    true
% 15.67/2.49  --prep_def_merge_tr_red                 false
% 15.67/2.49  --prep_def_merge_tr_cl                  false
% 15.67/2.49  --smt_preprocessing                     true
% 15.67/2.49  --smt_ac_axioms                         fast
% 15.67/2.49  --preprocessed_out                      false
% 15.67/2.49  --preprocessed_stats                    false
% 15.67/2.49  
% 15.67/2.49  ------ Abstraction refinement Options
% 15.67/2.49  
% 15.67/2.49  --abstr_ref                             []
% 15.67/2.49  --abstr_ref_prep                        false
% 15.67/2.49  --abstr_ref_until_sat                   false
% 15.67/2.49  --abstr_ref_sig_restrict                funpre
% 15.67/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.67/2.49  --abstr_ref_under                       []
% 15.67/2.49  
% 15.67/2.49  ------ SAT Options
% 15.67/2.49  
% 15.67/2.49  --sat_mode                              false
% 15.67/2.49  --sat_fm_restart_options                ""
% 15.67/2.49  --sat_gr_def                            false
% 15.67/2.49  --sat_epr_types                         true
% 15.67/2.49  --sat_non_cyclic_types                  false
% 15.67/2.49  --sat_finite_models                     false
% 15.67/2.49  --sat_fm_lemmas                         false
% 15.67/2.49  --sat_fm_prep                           false
% 15.67/2.49  --sat_fm_uc_incr                        true
% 15.67/2.49  --sat_out_model                         small
% 15.67/2.49  --sat_out_clauses                       false
% 15.67/2.49  
% 15.67/2.49  ------ QBF Options
% 15.67/2.49  
% 15.67/2.49  --qbf_mode                              false
% 15.67/2.49  --qbf_elim_univ                         false
% 15.67/2.49  --qbf_dom_inst                          none
% 15.67/2.49  --qbf_dom_pre_inst                      false
% 15.67/2.49  --qbf_sk_in                             false
% 15.67/2.49  --qbf_pred_elim                         true
% 15.67/2.49  --qbf_split                             512
% 15.67/2.49  
% 15.67/2.49  ------ BMC1 Options
% 15.67/2.49  
% 15.67/2.49  --bmc1_incremental                      false
% 15.67/2.49  --bmc1_axioms                           reachable_all
% 15.67/2.49  --bmc1_min_bound                        0
% 15.67/2.49  --bmc1_max_bound                        -1
% 15.67/2.49  --bmc1_max_bound_default                -1
% 15.67/2.49  --bmc1_symbol_reachability              true
% 15.67/2.49  --bmc1_property_lemmas                  false
% 15.67/2.49  --bmc1_k_induction                      false
% 15.67/2.49  --bmc1_non_equiv_states                 false
% 15.67/2.49  --bmc1_deadlock                         false
% 15.67/2.49  --bmc1_ucm                              false
% 15.67/2.49  --bmc1_add_unsat_core                   none
% 15.67/2.49  --bmc1_unsat_core_children              false
% 15.67/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.67/2.49  --bmc1_out_stat                         full
% 15.67/2.49  --bmc1_ground_init                      false
% 15.67/2.49  --bmc1_pre_inst_next_state              false
% 15.67/2.49  --bmc1_pre_inst_state                   false
% 15.67/2.49  --bmc1_pre_inst_reach_state             false
% 15.67/2.49  --bmc1_out_unsat_core                   false
% 15.67/2.49  --bmc1_aig_witness_out                  false
% 15.67/2.49  --bmc1_verbose                          false
% 15.67/2.49  --bmc1_dump_clauses_tptp                false
% 15.67/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.67/2.49  --bmc1_dump_file                        -
% 15.67/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.67/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.67/2.49  --bmc1_ucm_extend_mode                  1
% 15.67/2.49  --bmc1_ucm_init_mode                    2
% 15.67/2.49  --bmc1_ucm_cone_mode                    none
% 15.67/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.67/2.49  --bmc1_ucm_relax_model                  4
% 15.67/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.67/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.67/2.49  --bmc1_ucm_layered_model                none
% 15.67/2.49  --bmc1_ucm_max_lemma_size               10
% 15.67/2.49  
% 15.67/2.49  ------ AIG Options
% 15.67/2.49  
% 15.67/2.49  --aig_mode                              false
% 15.67/2.49  
% 15.67/2.49  ------ Instantiation Options
% 15.67/2.49  
% 15.67/2.49  --instantiation_flag                    true
% 15.67/2.49  --inst_sos_flag                         true
% 15.67/2.49  --inst_sos_phase                        true
% 15.67/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.67/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.67/2.49  --inst_lit_sel_side                     num_symb
% 15.67/2.49  --inst_solver_per_active                1400
% 15.67/2.49  --inst_solver_calls_frac                1.
% 15.67/2.49  --inst_passive_queue_type               priority_queues
% 15.67/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.67/2.49  --inst_passive_queues_freq              [25;2]
% 15.67/2.49  --inst_dismatching                      true
% 15.67/2.49  --inst_eager_unprocessed_to_passive     true
% 15.67/2.49  --inst_prop_sim_given                   true
% 15.67/2.49  --inst_prop_sim_new                     false
% 15.67/2.49  --inst_subs_new                         false
% 15.67/2.49  --inst_eq_res_simp                      false
% 15.67/2.49  --inst_subs_given                       false
% 15.67/2.49  --inst_orphan_elimination               true
% 15.67/2.49  --inst_learning_loop_flag               true
% 15.67/2.49  --inst_learning_start                   3000
% 15.67/2.49  --inst_learning_factor                  2
% 15.67/2.49  --inst_start_prop_sim_after_learn       3
% 15.67/2.49  --inst_sel_renew                        solver
% 15.67/2.49  --inst_lit_activity_flag                true
% 15.67/2.49  --inst_restr_to_given                   false
% 15.67/2.49  --inst_activity_threshold               500
% 15.67/2.49  --inst_out_proof                        true
% 15.67/2.49  
% 15.67/2.49  ------ Resolution Options
% 15.67/2.49  
% 15.67/2.49  --resolution_flag                       true
% 15.67/2.49  --res_lit_sel                           adaptive
% 15.67/2.49  --res_lit_sel_side                      none
% 15.67/2.49  --res_ordering                          kbo
% 15.67/2.49  --res_to_prop_solver                    active
% 15.67/2.49  --res_prop_simpl_new                    false
% 15.67/2.49  --res_prop_simpl_given                  true
% 15.67/2.49  --res_passive_queue_type                priority_queues
% 15.67/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.67/2.49  --res_passive_queues_freq               [15;5]
% 15.67/2.49  --res_forward_subs                      full
% 15.67/2.49  --res_backward_subs                     full
% 15.67/2.49  --res_forward_subs_resolution           true
% 15.67/2.49  --res_backward_subs_resolution          true
% 15.67/2.49  --res_orphan_elimination                true
% 15.67/2.49  --res_time_limit                        2.
% 15.67/2.49  --res_out_proof                         true
% 15.67/2.49  
% 15.67/2.49  ------ Superposition Options
% 15.67/2.49  
% 15.67/2.49  --superposition_flag                    true
% 15.67/2.49  --sup_passive_queue_type                priority_queues
% 15.67/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.67/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.67/2.49  --demod_completeness_check              fast
% 15.67/2.49  --demod_use_ground                      true
% 15.67/2.49  --sup_to_prop_solver                    passive
% 15.67/2.49  --sup_prop_simpl_new                    true
% 15.67/2.49  --sup_prop_simpl_given                  true
% 15.67/2.49  --sup_fun_splitting                     true
% 15.67/2.49  --sup_smt_interval                      50000
% 15.67/2.49  
% 15.67/2.49  ------ Superposition Simplification Setup
% 15.67/2.49  
% 15.67/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.67/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.67/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.67/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.67/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.67/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.67/2.49  --sup_immed_triv                        [TrivRules]
% 15.67/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.49  --sup_immed_bw_main                     []
% 15.67/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.67/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.67/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.49  --sup_input_bw                          []
% 15.67/2.49  
% 15.67/2.49  ------ Combination Options
% 15.67/2.49  
% 15.67/2.49  --comb_res_mult                         3
% 15.67/2.49  --comb_sup_mult                         2
% 15.67/2.49  --comb_inst_mult                        10
% 15.67/2.49  
% 15.67/2.49  ------ Debug Options
% 15.67/2.49  
% 15.67/2.49  --dbg_backtrace                         false
% 15.67/2.49  --dbg_dump_prop_clauses                 false
% 15.67/2.49  --dbg_dump_prop_clauses_file            -
% 15.67/2.49  --dbg_out_stat                          false
% 15.67/2.49  ------ Parsing...
% 15.67/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.67/2.49  
% 15.67/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.67/2.49  
% 15.67/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.67/2.49  
% 15.67/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.67/2.49  ------ Proving...
% 15.67/2.49  ------ Problem Properties 
% 15.67/2.49  
% 15.67/2.49  
% 15.67/2.49  clauses                                 12
% 15.67/2.49  conjectures                             2
% 15.67/2.49  EPR                                     2
% 15.67/2.49  Horn                                    12
% 15.67/2.49  unary                                   6
% 15.67/2.49  binary                                  6
% 15.67/2.49  lits                                    18
% 15.67/2.49  lits eq                                 6
% 15.67/2.49  fd_pure                                 0
% 15.67/2.49  fd_pseudo                               0
% 15.67/2.49  fd_cond                                 0
% 15.67/2.49  fd_pseudo_cond                          0
% 15.67/2.49  AC symbols                              0
% 15.67/2.49  
% 15.67/2.49  ------ Schedule dynamic 5 is on 
% 15.67/2.49  
% 15.67/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.67/2.49  
% 15.67/2.49  
% 15.67/2.49  ------ 
% 15.67/2.49  Current options:
% 15.67/2.49  ------ 
% 15.67/2.49  
% 15.67/2.49  ------ Input Options
% 15.67/2.49  
% 15.67/2.49  --out_options                           all
% 15.67/2.49  --tptp_safe_out                         true
% 15.67/2.49  --problem_path                          ""
% 15.67/2.49  --include_path                          ""
% 15.67/2.49  --clausifier                            res/vclausify_rel
% 15.67/2.49  --clausifier_options                    ""
% 15.67/2.49  --stdin                                 false
% 15.67/2.49  --stats_out                             all
% 15.67/2.49  
% 15.67/2.49  ------ General Options
% 15.67/2.49  
% 15.67/2.49  --fof                                   false
% 15.67/2.49  --time_out_real                         305.
% 15.67/2.49  --time_out_virtual                      -1.
% 15.67/2.49  --symbol_type_check                     false
% 15.67/2.49  --clausify_out                          false
% 15.67/2.49  --sig_cnt_out                           false
% 15.67/2.49  --trig_cnt_out                          false
% 15.67/2.49  --trig_cnt_out_tolerance                1.
% 15.67/2.49  --trig_cnt_out_sk_spl                   false
% 15.67/2.49  --abstr_cl_out                          false
% 15.67/2.49  
% 15.67/2.49  ------ Global Options
% 15.67/2.49  
% 15.67/2.49  --schedule                              default
% 15.67/2.49  --add_important_lit                     false
% 15.67/2.49  --prop_solver_per_cl                    1000
% 15.67/2.49  --min_unsat_core                        false
% 15.67/2.49  --soft_assumptions                      false
% 15.67/2.49  --soft_lemma_size                       3
% 15.67/2.49  --prop_impl_unit_size                   0
% 15.67/2.49  --prop_impl_unit                        []
% 15.67/2.49  --share_sel_clauses                     true
% 15.67/2.49  --reset_solvers                         false
% 15.67/2.49  --bc_imp_inh                            [conj_cone]
% 15.67/2.49  --conj_cone_tolerance                   3.
% 15.67/2.49  --extra_neg_conj                        none
% 15.67/2.49  --large_theory_mode                     true
% 15.67/2.49  --prolific_symb_bound                   200
% 15.67/2.49  --lt_threshold                          2000
% 15.67/2.49  --clause_weak_htbl                      true
% 15.67/2.49  --gc_record_bc_elim                     false
% 15.67/2.49  
% 15.67/2.49  ------ Preprocessing Options
% 15.67/2.49  
% 15.67/2.49  --preprocessing_flag                    true
% 15.67/2.49  --time_out_prep_mult                    0.1
% 15.67/2.49  --splitting_mode                        input
% 15.67/2.49  --splitting_grd                         true
% 15.67/2.49  --splitting_cvd                         false
% 15.67/2.49  --splitting_cvd_svl                     false
% 15.67/2.49  --splitting_nvd                         32
% 15.67/2.49  --sub_typing                            true
% 15.67/2.49  --prep_gs_sim                           true
% 15.67/2.49  --prep_unflatten                        true
% 15.67/2.49  --prep_res_sim                          true
% 15.67/2.49  --prep_upred                            true
% 15.67/2.49  --prep_sem_filter                       exhaustive
% 15.67/2.49  --prep_sem_filter_out                   false
% 15.67/2.49  --pred_elim                             true
% 15.67/2.49  --res_sim_input                         true
% 15.67/2.49  --eq_ax_congr_red                       true
% 15.67/2.49  --pure_diseq_elim                       true
% 15.67/2.49  --brand_transform                       false
% 15.67/2.49  --non_eq_to_eq                          false
% 15.67/2.49  --prep_def_merge                        true
% 15.67/2.49  --prep_def_merge_prop_impl              false
% 15.67/2.49  --prep_def_merge_mbd                    true
% 15.67/2.49  --prep_def_merge_tr_red                 false
% 15.67/2.49  --prep_def_merge_tr_cl                  false
% 15.67/2.49  --smt_preprocessing                     true
% 15.67/2.49  --smt_ac_axioms                         fast
% 15.67/2.49  --preprocessed_out                      false
% 15.67/2.49  --preprocessed_stats                    false
% 15.67/2.49  
% 15.67/2.49  ------ Abstraction refinement Options
% 15.67/2.49  
% 15.67/2.49  --abstr_ref                             []
% 15.67/2.49  --abstr_ref_prep                        false
% 15.67/2.49  --abstr_ref_until_sat                   false
% 15.67/2.49  --abstr_ref_sig_restrict                funpre
% 15.67/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.67/2.49  --abstr_ref_under                       []
% 15.67/2.49  
% 15.67/2.49  ------ SAT Options
% 15.67/2.49  
% 15.67/2.49  --sat_mode                              false
% 15.67/2.49  --sat_fm_restart_options                ""
% 15.67/2.49  --sat_gr_def                            false
% 15.67/2.49  --sat_epr_types                         true
% 15.67/2.49  --sat_non_cyclic_types                  false
% 15.67/2.49  --sat_finite_models                     false
% 15.67/2.49  --sat_fm_lemmas                         false
% 15.67/2.49  --sat_fm_prep                           false
% 15.67/2.49  --sat_fm_uc_incr                        true
% 15.67/2.49  --sat_out_model                         small
% 15.67/2.49  --sat_out_clauses                       false
% 15.67/2.49  
% 15.67/2.49  ------ QBF Options
% 15.67/2.49  
% 15.67/2.49  --qbf_mode                              false
% 15.67/2.49  --qbf_elim_univ                         false
% 15.67/2.49  --qbf_dom_inst                          none
% 15.67/2.49  --qbf_dom_pre_inst                      false
% 15.67/2.49  --qbf_sk_in                             false
% 15.67/2.49  --qbf_pred_elim                         true
% 15.67/2.49  --qbf_split                             512
% 15.67/2.49  
% 15.67/2.49  ------ BMC1 Options
% 15.67/2.49  
% 15.67/2.49  --bmc1_incremental                      false
% 15.67/2.49  --bmc1_axioms                           reachable_all
% 15.67/2.49  --bmc1_min_bound                        0
% 15.67/2.49  --bmc1_max_bound                        -1
% 15.67/2.49  --bmc1_max_bound_default                -1
% 15.67/2.49  --bmc1_symbol_reachability              true
% 15.67/2.49  --bmc1_property_lemmas                  false
% 15.67/2.49  --bmc1_k_induction                      false
% 15.67/2.49  --bmc1_non_equiv_states                 false
% 15.67/2.49  --bmc1_deadlock                         false
% 15.67/2.49  --bmc1_ucm                              false
% 15.67/2.49  --bmc1_add_unsat_core                   none
% 15.67/2.49  --bmc1_unsat_core_children              false
% 15.67/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.67/2.49  --bmc1_out_stat                         full
% 15.67/2.49  --bmc1_ground_init                      false
% 15.67/2.49  --bmc1_pre_inst_next_state              false
% 15.67/2.49  --bmc1_pre_inst_state                   false
% 15.67/2.49  --bmc1_pre_inst_reach_state             false
% 15.67/2.49  --bmc1_out_unsat_core                   false
% 15.67/2.49  --bmc1_aig_witness_out                  false
% 15.67/2.49  --bmc1_verbose                          false
% 15.67/2.49  --bmc1_dump_clauses_tptp                false
% 15.67/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.67/2.49  --bmc1_dump_file                        -
% 15.67/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.67/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.67/2.49  --bmc1_ucm_extend_mode                  1
% 15.67/2.49  --bmc1_ucm_init_mode                    2
% 15.67/2.49  --bmc1_ucm_cone_mode                    none
% 15.67/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.67/2.49  --bmc1_ucm_relax_model                  4
% 15.67/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.67/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.67/2.49  --bmc1_ucm_layered_model                none
% 15.67/2.49  --bmc1_ucm_max_lemma_size               10
% 15.67/2.49  
% 15.67/2.49  ------ AIG Options
% 15.67/2.49  
% 15.67/2.49  --aig_mode                              false
% 15.67/2.49  
% 15.67/2.49  ------ Instantiation Options
% 15.67/2.49  
% 15.67/2.49  --instantiation_flag                    true
% 15.67/2.49  --inst_sos_flag                         true
% 15.67/2.49  --inst_sos_phase                        true
% 15.67/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.67/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.67/2.49  --inst_lit_sel_side                     none
% 15.67/2.49  --inst_solver_per_active                1400
% 15.67/2.49  --inst_solver_calls_frac                1.
% 15.67/2.49  --inst_passive_queue_type               priority_queues
% 15.67/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.67/2.49  --inst_passive_queues_freq              [25;2]
% 15.67/2.49  --inst_dismatching                      true
% 15.67/2.49  --inst_eager_unprocessed_to_passive     true
% 15.67/2.49  --inst_prop_sim_given                   true
% 15.67/2.49  --inst_prop_sim_new                     false
% 15.67/2.49  --inst_subs_new                         false
% 15.67/2.49  --inst_eq_res_simp                      false
% 15.67/2.49  --inst_subs_given                       false
% 15.67/2.49  --inst_orphan_elimination               true
% 15.67/2.49  --inst_learning_loop_flag               true
% 15.67/2.49  --inst_learning_start                   3000
% 15.67/2.49  --inst_learning_factor                  2
% 15.67/2.49  --inst_start_prop_sim_after_learn       3
% 15.67/2.49  --inst_sel_renew                        solver
% 15.67/2.49  --inst_lit_activity_flag                true
% 15.67/2.49  --inst_restr_to_given                   false
% 15.67/2.49  --inst_activity_threshold               500
% 15.67/2.49  --inst_out_proof                        true
% 15.67/2.49  
% 15.67/2.49  ------ Resolution Options
% 15.67/2.49  
% 15.67/2.49  --resolution_flag                       false
% 15.67/2.49  --res_lit_sel                           adaptive
% 15.67/2.49  --res_lit_sel_side                      none
% 15.67/2.49  --res_ordering                          kbo
% 15.67/2.49  --res_to_prop_solver                    active
% 15.67/2.49  --res_prop_simpl_new                    false
% 15.67/2.49  --res_prop_simpl_given                  true
% 15.67/2.49  --res_passive_queue_type                priority_queues
% 15.67/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.67/2.49  --res_passive_queues_freq               [15;5]
% 15.67/2.49  --res_forward_subs                      full
% 15.67/2.49  --res_backward_subs                     full
% 15.67/2.49  --res_forward_subs_resolution           true
% 15.67/2.49  --res_backward_subs_resolution          true
% 15.67/2.49  --res_orphan_elimination                true
% 15.67/2.49  --res_time_limit                        2.
% 15.67/2.49  --res_out_proof                         true
% 15.67/2.49  
% 15.67/2.49  ------ Superposition Options
% 15.67/2.49  
% 15.67/2.49  --superposition_flag                    true
% 15.67/2.49  --sup_passive_queue_type                priority_queues
% 15.67/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.67/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.67/2.49  --demod_completeness_check              fast
% 15.67/2.49  --demod_use_ground                      true
% 15.67/2.49  --sup_to_prop_solver                    passive
% 15.67/2.49  --sup_prop_simpl_new                    true
% 15.67/2.49  --sup_prop_simpl_given                  true
% 15.67/2.49  --sup_fun_splitting                     true
% 15.67/2.49  --sup_smt_interval                      50000
% 15.67/2.49  
% 15.67/2.49  ------ Superposition Simplification Setup
% 15.67/2.49  
% 15.67/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.67/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.67/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.67/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.67/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.67/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.67/2.49  --sup_immed_triv                        [TrivRules]
% 15.67/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.49  --sup_immed_bw_main                     []
% 15.67/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.67/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.67/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.49  --sup_input_bw                          []
% 15.67/2.49  
% 15.67/2.49  ------ Combination Options
% 15.67/2.49  
% 15.67/2.49  --comb_res_mult                         3
% 15.67/2.49  --comb_sup_mult                         2
% 15.67/2.49  --comb_inst_mult                        10
% 15.67/2.49  
% 15.67/2.49  ------ Debug Options
% 15.67/2.49  
% 15.67/2.49  --dbg_backtrace                         false
% 15.67/2.49  --dbg_dump_prop_clauses                 false
% 15.67/2.49  --dbg_dump_prop_clauses_file            -
% 15.67/2.49  --dbg_out_stat                          false
% 15.67/2.49  
% 15.67/2.49  
% 15.67/2.49  
% 15.67/2.49  
% 15.67/2.49  ------ Proving...
% 15.67/2.49  
% 15.67/2.49  
% 15.67/2.49  % SZS status Theorem for theBenchmark.p
% 15.67/2.49  
% 15.67/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.67/2.49  
% 15.67/2.49  fof(f2,axiom,(
% 15.67/2.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f13,plain,(
% 15.67/2.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 15.67/2.49    inference(rectify,[],[f2])).
% 15.67/2.49  
% 15.67/2.49  fof(f22,plain,(
% 15.67/2.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 15.67/2.49    inference(cnf_transformation,[],[f13])).
% 15.67/2.49  
% 15.67/2.49  fof(f6,axiom,(
% 15.67/2.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f27,plain,(
% 15.67/2.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 15.67/2.49    inference(cnf_transformation,[],[f6])).
% 15.67/2.49  
% 15.67/2.49  fof(f1,axiom,(
% 15.67/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f21,plain,(
% 15.67/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.67/2.49    inference(cnf_transformation,[],[f1])).
% 15.67/2.49  
% 15.67/2.49  fof(f11,conjecture,(
% 15.67/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f12,negated_conjecture,(
% 15.67/2.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 15.67/2.49    inference(negated_conjecture,[],[f11])).
% 15.67/2.49  
% 15.67/2.49  fof(f17,plain,(
% 15.67/2.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 15.67/2.49    inference(ennf_transformation,[],[f12])).
% 15.67/2.49  
% 15.67/2.49  fof(f19,plain,(
% 15.67/2.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 15.67/2.49    introduced(choice_axiom,[])).
% 15.67/2.49  
% 15.67/2.49  fof(f20,plain,(
% 15.67/2.49    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 15.67/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 15.67/2.49  
% 15.67/2.49  fof(f32,plain,(
% 15.67/2.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 15.67/2.49    inference(cnf_transformation,[],[f20])).
% 15.67/2.49  
% 15.67/2.49  fof(f5,axiom,(
% 15.67/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f26,plain,(
% 15.67/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.67/2.49    inference(cnf_transformation,[],[f5])).
% 15.67/2.49  
% 15.67/2.49  fof(f39,plain,(
% 15.67/2.49    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 15.67/2.49    inference(definition_unfolding,[],[f32,f26])).
% 15.67/2.49  
% 15.67/2.49  fof(f7,axiom,(
% 15.67/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f15,plain,(
% 15.67/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.67/2.49    inference(ennf_transformation,[],[f7])).
% 15.67/2.49  
% 15.67/2.49  fof(f28,plain,(
% 15.67/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.67/2.49    inference(cnf_transformation,[],[f15])).
% 15.67/2.49  
% 15.67/2.49  fof(f9,axiom,(
% 15.67/2.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f30,plain,(
% 15.67/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.67/2.49    inference(cnf_transformation,[],[f9])).
% 15.67/2.49  
% 15.67/2.49  fof(f37,plain,(
% 15.67/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 15.67/2.49    inference(definition_unfolding,[],[f30,f26,f26])).
% 15.67/2.49  
% 15.67/2.49  fof(f10,axiom,(
% 15.67/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f16,plain,(
% 15.67/2.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 15.67/2.49    inference(ennf_transformation,[],[f10])).
% 15.67/2.49  
% 15.67/2.49  fof(f31,plain,(
% 15.67/2.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.67/2.49    inference(cnf_transformation,[],[f16])).
% 15.67/2.49  
% 15.67/2.49  fof(f38,plain,(
% 15.67/2.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 15.67/2.49    inference(definition_unfolding,[],[f31,f26])).
% 15.67/2.49  
% 15.67/2.49  fof(f3,axiom,(
% 15.67/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f14,plain,(
% 15.67/2.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.67/2.49    inference(ennf_transformation,[],[f3])).
% 15.67/2.49  
% 15.67/2.49  fof(f23,plain,(
% 15.67/2.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.67/2.49    inference(cnf_transformation,[],[f14])).
% 15.67/2.49  
% 15.67/2.49  fof(f8,axiom,(
% 15.67/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f29,plain,(
% 15.67/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.67/2.49    inference(cnf_transformation,[],[f8])).
% 15.67/2.49  
% 15.67/2.49  fof(f36,plain,(
% 15.67/2.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 15.67/2.49    inference(definition_unfolding,[],[f29,f26])).
% 15.67/2.49  
% 15.67/2.49  fof(f4,axiom,(
% 15.67/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.67/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.49  
% 15.67/2.49  fof(f18,plain,(
% 15.67/2.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.67/2.49    inference(nnf_transformation,[],[f4])).
% 15.67/2.49  
% 15.67/2.49  fof(f25,plain,(
% 15.67/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.67/2.49    inference(cnf_transformation,[],[f18])).
% 15.67/2.49  
% 15.67/2.49  fof(f34,plain,(
% 15.67/2.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 15.67/2.49    inference(definition_unfolding,[],[f25,f26])).
% 15.67/2.49  
% 15.67/2.49  fof(f24,plain,(
% 15.67/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.67/2.49    inference(cnf_transformation,[],[f18])).
% 15.67/2.49  
% 15.67/2.49  fof(f35,plain,(
% 15.67/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.67/2.49    inference(definition_unfolding,[],[f24,f26])).
% 15.67/2.49  
% 15.67/2.49  fof(f33,plain,(
% 15.67/2.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 15.67/2.49    inference(cnf_transformation,[],[f20])).
% 15.67/2.49  
% 15.67/2.49  cnf(c_1,plain,
% 15.67/2.49      ( k3_xboole_0(X0,X0) = X0 ),
% 15.67/2.49      inference(cnf_transformation,[],[f22]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_5,plain,
% 15.67/2.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 15.67/2.49      inference(cnf_transformation,[],[f27]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_521,plain,
% 15.67/2.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 15.67/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_671,plain,
% 15.67/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_1,c_521]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_0,plain,
% 15.67/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.67/2.49      inference(cnf_transformation,[],[f21]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_11,negated_conjecture,
% 15.67/2.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 15.67/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_516,plain,
% 15.67/2.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 15.67/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_617,plain,
% 15.67/2.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 15.67/2.49      inference(demodulation,[status(thm)],[c_0,c_516]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_6,plain,
% 15.67/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.67/2.49      inference(cnf_transformation,[],[f28]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_520,plain,
% 15.67/2.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.67/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_976,plain,
% 15.67/2.49      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_617,c_520]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_8,plain,
% 15.67/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.67/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_9,plain,
% 15.67/2.49      ( ~ r1_tarski(X0,X1)
% 15.67/2.49      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 15.67/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_518,plain,
% 15.67/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.67/2.49      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
% 15.67/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_1311,plain,
% 15.67/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.67/2.49      | r1_xboole_0(X0,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))) = iProver_top ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_8,c_518]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_57877,plain,
% 15.67/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.67/2.49      | r1_xboole_0(X0,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X1,X3)))) = iProver_top ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_0,c_1311]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_59011,plain,
% 15.67/2.49      ( r1_tarski(X0,sK2) != iProver_top
% 15.67/2.49      | r1_xboole_0(X0,sK0) = iProver_top ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_976,c_57877]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_59968,plain,
% 15.67/2.49      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_671,c_59011]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_2,plain,
% 15.67/2.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.67/2.49      inference(cnf_transformation,[],[f23]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_8068,plain,
% 15.67/2.49      ( ~ r1_xboole_0(sK2,sK0) | r1_xboole_0(sK0,sK2) ),
% 15.67/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_8069,plain,
% 15.67/2.49      ( r1_xboole_0(sK2,sK0) != iProver_top
% 15.67/2.49      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 15.67/2.49      inference(predicate_to_equality,[status(thm)],[c_8068]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_7,plain,
% 15.67/2.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 15.67/2.49      inference(cnf_transformation,[],[f36]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_519,plain,
% 15.67/2.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 15.67/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_837,plain,
% 15.67/2.49      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_8,c_519]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_2098,plain,
% 15.67/2.49      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_0,c_837]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_4333,plain,
% 15.67/2.49      ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_976,c_2098]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_4951,plain,
% 15.67/2.49      ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_4333,c_520]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_827,plain,
% 15.67/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_4137,plain,
% 15.67/2.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_1,c_827]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_5334,plain,
% 15.67/2.49      ( k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_4951,c_4137]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_3,plain,
% 15.67/2.49      ( ~ r1_tarski(X0,X1)
% 15.67/2.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.67/2.49      inference(cnf_transformation,[],[f34]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_523,plain,
% 15.67/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 15.67/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.67/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_3035,plain,
% 15.67/2.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_617,c_523]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_3084,plain,
% 15.67/2.49      ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 15.67/2.49      inference(light_normalisation,[status(thm)],[c_3035,c_976]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_3037,plain,
% 15.67/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_671,c_523]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_3076,plain,
% 15.67/2.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.67/2.49      inference(light_normalisation,[status(thm)],[c_3037,c_1]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_983,plain,
% 15.67/2.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_976,c_8]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_1051,plain,
% 15.67/2.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_1,c_983]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_1058,plain,
% 15.67/2.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k5_xboole_0(sK0,sK0) ),
% 15.67/2.49      inference(light_normalisation,[status(thm)],[c_1051,c_976]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_3199,plain,
% 15.67/2.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
% 15.67/2.49      inference(demodulation,[status(thm)],[c_3076,c_1058]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_3207,plain,
% 15.67/2.49      ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
% 15.67/2.49      inference(demodulation,[status(thm)],[c_3199,c_3076]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_5373,plain,
% 15.67/2.49      ( k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)) = k1_xboole_0 ),
% 15.67/2.49      inference(light_normalisation,[status(thm)],[c_5334,c_3084,c_3207]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_974,plain,
% 15.67/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 15.67/2.49      inference(superposition,[status(thm)],[c_521,c_520]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_5374,plain,
% 15.67/2.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 15.67/2.49      inference(demodulation,[status(thm)],[c_5373,c_974]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_4,plain,
% 15.67/2.49      ( r1_tarski(X0,X1)
% 15.67/2.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 15.67/2.49      inference(cnf_transformation,[],[f35]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_78,plain,
% 15.67/2.49      ( r1_tarski(X0,X1)
% 15.67/2.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 15.67/2.49      inference(prop_impl,[status(thm)],[c_4]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_10,negated_conjecture,
% 15.67/2.49      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 15.67/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_195,plain,
% 15.67/2.49      ( ~ r1_xboole_0(sK0,sK2)
% 15.67/2.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 15.67/2.49      | sK1 != X1
% 15.67/2.49      | sK0 != X0 ),
% 15.67/2.49      inference(resolution_lifted,[status(thm)],[c_78,c_10]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_196,plain,
% 15.67/2.49      ( ~ r1_xboole_0(sK0,sK2)
% 15.67/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 15.67/2.49      inference(unflattening,[status(thm)],[c_195]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(c_197,plain,
% 15.67/2.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
% 15.67/2.49      | r1_xboole_0(sK0,sK2) != iProver_top ),
% 15.67/2.49      inference(predicate_to_equality,[status(thm)],[c_196]) ).
% 15.67/2.49  
% 15.67/2.49  cnf(contradiction,plain,
% 15.67/2.49      ( $false ),
% 15.67/2.49      inference(minisat,[status(thm)],[c_59968,c_8069,c_5374,c_197]) ).
% 15.67/2.49  
% 15.67/2.49  
% 15.67/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.67/2.49  
% 15.67/2.49  ------                               Statistics
% 15.67/2.49  
% 15.67/2.49  ------ General
% 15.67/2.49  
% 15.67/2.49  abstr_ref_over_cycles:                  0
% 15.67/2.49  abstr_ref_under_cycles:                 0
% 15.67/2.49  gc_basic_clause_elim:                   0
% 15.67/2.49  forced_gc_time:                         0
% 15.67/2.49  parsing_time:                           0.008
% 15.67/2.49  unif_index_cands_time:                  0.
% 15.67/2.49  unif_index_add_time:                    0.
% 15.67/2.49  orderings_time:                         0.
% 15.67/2.49  out_proof_time:                         0.008
% 15.67/2.49  total_time:                             1.754
% 15.67/2.49  num_of_symbols:                         39
% 15.67/2.49  num_of_terms:                           67018
% 15.67/2.49  
% 15.67/2.49  ------ Preprocessing
% 15.67/2.49  
% 15.67/2.49  num_of_splits:                          0
% 15.67/2.49  num_of_split_atoms:                     0
% 15.67/2.49  num_of_reused_defs:                     0
% 15.67/2.49  num_eq_ax_congr_red:                    0
% 15.67/2.49  num_of_sem_filtered_clauses:            1
% 15.67/2.49  num_of_subtypes:                        0
% 15.67/2.49  monotx_restored_types:                  0
% 15.67/2.49  sat_num_of_epr_types:                   0
% 15.67/2.49  sat_num_of_non_cyclic_types:            0
% 15.67/2.49  sat_guarded_non_collapsed_types:        0
% 15.67/2.49  num_pure_diseq_elim:                    0
% 15.67/2.49  simp_replaced_by:                       0
% 15.67/2.49  res_preprocessed:                       49
% 15.67/2.49  prep_upred:                             0
% 15.67/2.49  prep_unflattend:                        22
% 15.67/2.49  smt_new_axioms:                         0
% 15.67/2.49  pred_elim_cands:                        2
% 15.67/2.49  pred_elim:                              0
% 15.67/2.49  pred_elim_cl:                           0
% 15.67/2.49  pred_elim_cycles:                       1
% 15.67/2.49  merged_defs:                            6
% 15.67/2.49  merged_defs_ncl:                        0
% 15.67/2.49  bin_hyper_res:                          6
% 15.67/2.49  prep_cycles:                            3
% 15.67/2.49  pred_elim_time:                         0.002
% 15.67/2.49  splitting_time:                         0.
% 15.67/2.49  sem_filter_time:                        0.
% 15.67/2.49  monotx_time:                            0.
% 15.67/2.49  subtype_inf_time:                       0.
% 15.67/2.49  
% 15.67/2.49  ------ Problem properties
% 15.67/2.49  
% 15.67/2.49  clauses:                                12
% 15.67/2.49  conjectures:                            2
% 15.67/2.49  epr:                                    2
% 15.67/2.49  horn:                                   12
% 15.67/2.49  ground:                                 2
% 15.67/2.49  unary:                                  6
% 15.67/2.49  binary:                                 6
% 15.67/2.49  lits:                                   18
% 15.67/2.49  lits_eq:                                6
% 15.67/2.49  fd_pure:                                0
% 15.67/2.49  fd_pseudo:                              0
% 15.67/2.49  fd_cond:                                0
% 15.67/2.49  fd_pseudo_cond:                         0
% 15.67/2.49  ac_symbols:                             0
% 15.67/2.49  
% 15.67/2.49  ------ Propositional Solver
% 15.67/2.49  
% 15.67/2.49  prop_solver_calls:                      30
% 15.67/2.49  prop_fast_solver_calls:                 539
% 15.67/2.49  smt_solver_calls:                       0
% 15.67/2.49  smt_fast_solver_calls:                  0
% 15.67/2.49  prop_num_of_clauses:                    19031
% 15.67/2.49  prop_preprocess_simplified:             17496
% 15.67/2.49  prop_fo_subsumed:                       0
% 15.67/2.49  prop_solver_time:                       0.
% 15.67/2.49  smt_solver_time:                        0.
% 15.67/2.49  smt_fast_solver_time:                   0.
% 15.67/2.49  prop_fast_solver_time:                  0.
% 15.67/2.49  prop_unsat_core_time:                   0.002
% 15.67/2.49  
% 15.67/2.49  ------ QBF
% 15.67/2.49  
% 15.67/2.49  qbf_q_res:                              0
% 15.67/2.49  qbf_num_tautologies:                    0
% 15.67/2.49  qbf_prep_cycles:                        0
% 15.67/2.49  
% 15.67/2.49  ------ BMC1
% 15.67/2.49  
% 15.67/2.49  bmc1_current_bound:                     -1
% 15.67/2.49  bmc1_last_solved_bound:                 -1
% 15.67/2.49  bmc1_unsat_core_size:                   -1
% 15.67/2.49  bmc1_unsat_core_parents_size:           -1
% 15.67/2.49  bmc1_merge_next_fun:                    0
% 15.67/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.67/2.49  
% 15.67/2.49  ------ Instantiation
% 15.67/2.49  
% 15.67/2.49  inst_num_of_clauses:                    3098
% 15.67/2.49  inst_num_in_passive:                    1016
% 15.67/2.49  inst_num_in_active:                     1184
% 15.67/2.49  inst_num_in_unprocessed:                903
% 15.67/2.49  inst_num_of_loops:                      1370
% 15.67/2.49  inst_num_of_learning_restarts:          0
% 15.67/2.49  inst_num_moves_active_passive:          179
% 15.67/2.49  inst_lit_activity:                      0
% 15.67/2.49  inst_lit_activity_moves:                0
% 15.67/2.49  inst_num_tautologies:                   0
% 15.67/2.49  inst_num_prop_implied:                  0
% 15.67/2.49  inst_num_existing_simplified:           0
% 15.67/2.49  inst_num_eq_res_simplified:             0
% 15.67/2.49  inst_num_child_elim:                    0
% 15.67/2.49  inst_num_of_dismatching_blockings:      4890
% 15.67/2.49  inst_num_of_non_proper_insts:           4402
% 15.67/2.49  inst_num_of_duplicates:                 0
% 15.67/2.49  inst_inst_num_from_inst_to_res:         0
% 15.67/2.49  inst_dismatching_checking_time:         0.
% 15.67/2.49  
% 15.67/2.49  ------ Resolution
% 15.67/2.49  
% 15.67/2.49  res_num_of_clauses:                     0
% 15.67/2.49  res_num_in_passive:                     0
% 15.67/2.49  res_num_in_active:                      0
% 15.67/2.49  res_num_of_loops:                       52
% 15.67/2.49  res_forward_subset_subsumed:            835
% 15.67/2.49  res_backward_subset_subsumed:           58
% 15.67/2.49  res_forward_subsumed:                   0
% 15.67/2.49  res_backward_subsumed:                  0
% 15.67/2.49  res_forward_subsumption_resolution:     0
% 15.67/2.49  res_backward_subsumption_resolution:    0
% 15.67/2.49  res_clause_to_clause_subsumption:       67091
% 15.67/2.49  res_orphan_elimination:                 0
% 15.67/2.49  res_tautology_del:                      510
% 15.67/2.49  res_num_eq_res_simplified:              0
% 15.67/2.49  res_num_sel_changes:                    0
% 15.67/2.49  res_moves_from_active_to_pass:          0
% 15.67/2.49  
% 15.67/2.49  ------ Superposition
% 15.67/2.49  
% 15.67/2.49  sup_time_total:                         0.
% 15.67/2.49  sup_time_generating:                    0.
% 15.67/2.49  sup_time_sim_full:                      0.
% 15.67/2.49  sup_time_sim_immed:                     0.
% 15.67/2.49  
% 15.67/2.49  sup_num_of_clauses:                     5333
% 15.67/2.49  sup_num_in_active:                      226
% 15.67/2.49  sup_num_in_passive:                     5107
% 15.67/2.49  sup_num_of_loops:                       272
% 15.67/2.49  sup_fw_superposition:                   11217
% 15.67/2.49  sup_bw_superposition:                   11532
% 15.67/2.49  sup_immediate_simplified:               6911
% 15.67/2.49  sup_given_eliminated:                   13
% 15.67/2.49  comparisons_done:                       0
% 15.67/2.49  comparisons_avoided:                    0
% 15.67/2.49  
% 15.67/2.49  ------ Simplifications
% 15.67/2.49  
% 15.67/2.49  
% 15.67/2.49  sim_fw_subset_subsumed:                 43
% 15.67/2.49  sim_bw_subset_subsumed:                 0
% 15.67/2.49  sim_fw_subsumed:                        750
% 15.67/2.49  sim_bw_subsumed:                        94
% 15.67/2.49  sim_fw_subsumption_res:                 0
% 15.67/2.49  sim_bw_subsumption_res:                 0
% 15.67/2.49  sim_tautology_del:                      0
% 15.67/2.49  sim_eq_tautology_del:                   1033
% 15.67/2.49  sim_eq_res_simp:                        53
% 15.67/2.49  sim_fw_demodulated:                     4177
% 15.67/2.49  sim_bw_demodulated:                     318
% 15.67/2.49  sim_light_normalised:                   2783
% 15.67/2.49  sim_joinable_taut:                      0
% 15.67/2.49  sim_joinable_simp:                      0
% 15.67/2.49  sim_ac_normalised:                      0
% 15.67/2.49  sim_smt_subsumption:                    0
% 15.67/2.49  
%------------------------------------------------------------------------------
