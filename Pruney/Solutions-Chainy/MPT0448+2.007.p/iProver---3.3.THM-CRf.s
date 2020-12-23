%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:19 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 201 expanded)
%              Number of clauses        :   17 (  19 expanded)
%              Number of leaves         :   14 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 238 expanded)
%              Number of equality atoms :   70 ( 206 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f37])).

fof(f39,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f46,plain,(
    ! [X0] :
      ( k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_tarski(X1,X3) = k2_relat_1(X4)
          & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X2) = k1_relat_1(X4)
      | k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(definition_unfolding,[],[f34,f39,f39])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X2) = k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_tarski(X1,X3) = k2_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_enumset1(X1,X1,X1,X1,X1,X3) = k2_relat_1(X4)
      | k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(definition_unfolding,[],[f35,f39,f39])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_enumset1(X1,X1,X1,X1,X1,X3) = k2_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f24,f39])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f22,f40,f41])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f14,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f15])).

fof(f20,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f36,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k3_relat_1(k4_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f36,f39,f41])).

cnf(c_3,plain,
    ( v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_127,plain,
    ( v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_128,plain,
    ( k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_204,plain,
    ( k3_tarski(k4_enumset1(k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k2_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))))) = k3_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(superposition,[status(thm)],[c_127,c_128])).

cnf(c_5,plain,
    ( ~ v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
    | k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k4_enumset1(X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,plain,
    ( k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k4_enumset1(X0,X0,X0,X0,X0,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_3])).

cnf(c_4,plain,
    ( ~ v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
    | k2_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k4_enumset1(X1,X1,X1,X1,X1,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34,plain,
    ( k2_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k4_enumset1(X1,X1,X1,X1,X1,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_3])).

cnf(c_391,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X2,X2,X3))) = k3_relat_1(k4_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_204,c_30,c_34])).

cnf(c_0,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_398,plain,
    ( k3_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1))) = k4_enumset1(X0,X0,X0,X0,X2,X1) ),
    inference(superposition,[status(thm)],[c_391,c_0])).

cnf(c_6,negated_conjecture,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k3_relat_1(k4_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_573,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_398,c_6])).

cnf(c_66,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_164,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_573,c_164])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.06  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n017.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 13:26:31 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 1.73/0.82  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/0.82  
% 1.73/0.82  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.73/0.82  
% 1.73/0.82  ------  iProver source info
% 1.73/0.82  
% 1.73/0.82  git: date: 2020-06-30 10:37:57 +0100
% 1.73/0.82  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.73/0.82  git: non_committed_changes: false
% 1.73/0.82  git: last_make_outside_of_git: false
% 1.73/0.82  
% 1.73/0.82  ------ 
% 1.73/0.82  
% 1.73/0.82  ------ Input Options
% 1.73/0.82  
% 1.73/0.82  --out_options                           all
% 1.73/0.82  --tptp_safe_out                         true
% 1.73/0.82  --problem_path                          ""
% 1.73/0.82  --include_path                          ""
% 1.73/0.82  --clausifier                            res/vclausify_rel
% 1.73/0.82  --clausifier_options                    --mode clausify
% 1.73/0.82  --stdin                                 false
% 1.73/0.82  --stats_out                             all
% 1.73/0.82  
% 1.73/0.82  ------ General Options
% 1.73/0.82  
% 1.73/0.82  --fof                                   false
% 1.73/0.82  --time_out_real                         305.
% 1.73/0.82  --time_out_virtual                      -1.
% 1.73/0.82  --symbol_type_check                     false
% 1.73/0.82  --clausify_out                          false
% 1.73/0.82  --sig_cnt_out                           false
% 1.73/0.82  --trig_cnt_out                          false
% 1.73/0.82  --trig_cnt_out_tolerance                1.
% 1.73/0.82  --trig_cnt_out_sk_spl                   false
% 1.73/0.82  --abstr_cl_out                          false
% 1.73/0.82  
% 1.73/0.82  ------ Global Options
% 1.73/0.82  
% 1.73/0.82  --schedule                              default
% 1.73/0.82  --add_important_lit                     false
% 1.73/0.82  --prop_solver_per_cl                    1000
% 1.73/0.82  --min_unsat_core                        false
% 1.73/0.82  --soft_assumptions                      false
% 1.73/0.82  --soft_lemma_size                       3
% 1.73/0.82  --prop_impl_unit_size                   0
% 1.73/0.82  --prop_impl_unit                        []
% 1.73/0.82  --share_sel_clauses                     true
% 1.73/0.82  --reset_solvers                         false
% 1.73/0.82  --bc_imp_inh                            [conj_cone]
% 1.73/0.82  --conj_cone_tolerance                   3.
% 1.73/0.82  --extra_neg_conj                        none
% 1.73/0.82  --large_theory_mode                     true
% 1.73/0.82  --prolific_symb_bound                   200
% 1.73/0.82  --lt_threshold                          2000
% 1.73/0.82  --clause_weak_htbl                      true
% 1.73/0.82  --gc_record_bc_elim                     false
% 1.73/0.82  
% 1.73/0.82  ------ Preprocessing Options
% 1.73/0.82  
% 1.73/0.82  --preprocessing_flag                    true
% 1.73/0.82  --time_out_prep_mult                    0.1
% 1.73/0.82  --splitting_mode                        input
% 1.73/0.82  --splitting_grd                         true
% 1.73/0.82  --splitting_cvd                         false
% 1.73/0.82  --splitting_cvd_svl                     false
% 1.73/0.82  --splitting_nvd                         32
% 1.73/0.82  --sub_typing                            true
% 1.73/0.82  --prep_gs_sim                           true
% 1.73/0.82  --prep_unflatten                        true
% 1.73/0.82  --prep_res_sim                          true
% 1.73/0.82  --prep_upred                            true
% 1.73/0.82  --prep_sem_filter                       exhaustive
% 1.73/0.82  --prep_sem_filter_out                   false
% 1.73/0.82  --pred_elim                             true
% 1.73/0.82  --res_sim_input                         true
% 1.73/0.82  --eq_ax_congr_red                       true
% 1.73/0.82  --pure_diseq_elim                       true
% 1.73/0.82  --brand_transform                       false
% 1.73/0.82  --non_eq_to_eq                          false
% 1.73/0.82  --prep_def_merge                        true
% 1.73/0.82  --prep_def_merge_prop_impl              false
% 1.73/0.82  --prep_def_merge_mbd                    true
% 1.73/0.82  --prep_def_merge_tr_red                 false
% 1.73/0.82  --prep_def_merge_tr_cl                  false
% 1.73/0.82  --smt_preprocessing                     true
% 1.73/0.82  --smt_ac_axioms                         fast
% 1.73/0.82  --preprocessed_out                      false
% 1.73/0.82  --preprocessed_stats                    false
% 1.73/0.82  
% 1.73/0.82  ------ Abstraction refinement Options
% 1.73/0.82  
% 1.73/0.82  --abstr_ref                             []
% 1.73/0.82  --abstr_ref_prep                        false
% 1.73/0.82  --abstr_ref_until_sat                   false
% 1.73/0.82  --abstr_ref_sig_restrict                funpre
% 1.73/0.82  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/0.82  --abstr_ref_under                       []
% 1.73/0.82  
% 1.73/0.82  ------ SAT Options
% 1.73/0.82  
% 1.73/0.82  --sat_mode                              false
% 1.73/0.82  --sat_fm_restart_options                ""
% 1.73/0.82  --sat_gr_def                            false
% 1.73/0.82  --sat_epr_types                         true
% 1.73/0.82  --sat_non_cyclic_types                  false
% 1.73/0.82  --sat_finite_models                     false
% 1.73/0.82  --sat_fm_lemmas                         false
% 1.73/0.82  --sat_fm_prep                           false
% 1.73/0.82  --sat_fm_uc_incr                        true
% 1.73/0.82  --sat_out_model                         small
% 1.73/0.82  --sat_out_clauses                       false
% 1.73/0.82  
% 1.73/0.82  ------ QBF Options
% 1.73/0.82  
% 1.73/0.82  --qbf_mode                              false
% 1.73/0.82  --qbf_elim_univ                         false
% 1.73/0.82  --qbf_dom_inst                          none
% 1.73/0.82  --qbf_dom_pre_inst                      false
% 1.73/0.82  --qbf_sk_in                             false
% 1.73/0.82  --qbf_pred_elim                         true
% 1.73/0.82  --qbf_split                             512
% 1.73/0.82  
% 1.73/0.82  ------ BMC1 Options
% 1.73/0.82  
% 1.73/0.82  --bmc1_incremental                      false
% 1.73/0.82  --bmc1_axioms                           reachable_all
% 1.73/0.82  --bmc1_min_bound                        0
% 1.73/0.82  --bmc1_max_bound                        -1
% 1.73/0.82  --bmc1_max_bound_default                -1
% 1.73/0.82  --bmc1_symbol_reachability              true
% 1.73/0.82  --bmc1_property_lemmas                  false
% 1.73/0.82  --bmc1_k_induction                      false
% 1.73/0.82  --bmc1_non_equiv_states                 false
% 1.73/0.82  --bmc1_deadlock                         false
% 1.73/0.82  --bmc1_ucm                              false
% 1.73/0.82  --bmc1_add_unsat_core                   none
% 1.73/0.82  --bmc1_unsat_core_children              false
% 1.73/0.82  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/0.82  --bmc1_out_stat                         full
% 1.73/0.82  --bmc1_ground_init                      false
% 1.73/0.82  --bmc1_pre_inst_next_state              false
% 1.73/0.82  --bmc1_pre_inst_state                   false
% 1.73/0.82  --bmc1_pre_inst_reach_state             false
% 1.73/0.82  --bmc1_out_unsat_core                   false
% 1.73/0.82  --bmc1_aig_witness_out                  false
% 1.73/0.82  --bmc1_verbose                          false
% 1.73/0.82  --bmc1_dump_clauses_tptp                false
% 1.73/0.82  --bmc1_dump_unsat_core_tptp             false
% 1.73/0.82  --bmc1_dump_file                        -
% 1.73/0.82  --bmc1_ucm_expand_uc_limit              128
% 1.73/0.82  --bmc1_ucm_n_expand_iterations          6
% 1.73/0.82  --bmc1_ucm_extend_mode                  1
% 1.73/0.82  --bmc1_ucm_init_mode                    2
% 1.73/0.82  --bmc1_ucm_cone_mode                    none
% 1.73/0.82  --bmc1_ucm_reduced_relation_type        0
% 1.73/0.82  --bmc1_ucm_relax_model                  4
% 1.73/0.82  --bmc1_ucm_full_tr_after_sat            true
% 1.73/0.82  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/0.82  --bmc1_ucm_layered_model                none
% 1.73/0.82  --bmc1_ucm_max_lemma_size               10
% 1.73/0.82  
% 1.73/0.82  ------ AIG Options
% 1.73/0.82  
% 1.73/0.82  --aig_mode                              false
% 1.73/0.82  
% 1.73/0.82  ------ Instantiation Options
% 1.73/0.82  
% 1.73/0.82  --instantiation_flag                    true
% 1.73/0.82  --inst_sos_flag                         false
% 1.73/0.82  --inst_sos_phase                        true
% 1.73/0.82  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/0.82  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/0.82  --inst_lit_sel_side                     num_symb
% 1.73/0.82  --inst_solver_per_active                1400
% 1.73/0.82  --inst_solver_calls_frac                1.
% 1.73/0.82  --inst_passive_queue_type               priority_queues
% 1.73/0.82  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/0.82  --inst_passive_queues_freq              [25;2]
% 1.73/0.82  --inst_dismatching                      true
% 1.73/0.82  --inst_eager_unprocessed_to_passive     true
% 1.73/0.82  --inst_prop_sim_given                   true
% 1.73/0.82  --inst_prop_sim_new                     false
% 1.73/0.82  --inst_subs_new                         false
% 1.73/0.82  --inst_eq_res_simp                      false
% 1.73/0.82  --inst_subs_given                       false
% 1.73/0.82  --inst_orphan_elimination               true
% 1.73/0.82  --inst_learning_loop_flag               true
% 1.73/0.82  --inst_learning_start                   3000
% 1.73/0.82  --inst_learning_factor                  2
% 1.73/0.82  --inst_start_prop_sim_after_learn       3
% 1.73/0.82  --inst_sel_renew                        solver
% 1.73/0.82  --inst_lit_activity_flag                true
% 1.73/0.82  --inst_restr_to_given                   false
% 1.73/0.82  --inst_activity_threshold               500
% 1.73/0.82  --inst_out_proof                        true
% 1.73/0.82  
% 1.73/0.82  ------ Resolution Options
% 1.73/0.82  
% 1.73/0.82  --resolution_flag                       true
% 1.73/0.82  --res_lit_sel                           adaptive
% 1.73/0.82  --res_lit_sel_side                      none
% 1.73/0.82  --res_ordering                          kbo
% 1.73/0.82  --res_to_prop_solver                    active
% 1.73/0.82  --res_prop_simpl_new                    false
% 1.73/0.82  --res_prop_simpl_given                  true
% 1.73/0.82  --res_passive_queue_type                priority_queues
% 1.73/0.82  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/0.82  --res_passive_queues_freq               [15;5]
% 1.73/0.82  --res_forward_subs                      full
% 1.73/0.82  --res_backward_subs                     full
% 1.73/0.82  --res_forward_subs_resolution           true
% 1.73/0.82  --res_backward_subs_resolution          true
% 1.73/0.82  --res_orphan_elimination                true
% 1.73/0.82  --res_time_limit                        2.
% 1.73/0.82  --res_out_proof                         true
% 1.73/0.82  
% 1.73/0.82  ------ Superposition Options
% 1.73/0.82  
% 1.73/0.82  --superposition_flag                    true
% 1.73/0.82  --sup_passive_queue_type                priority_queues
% 1.73/0.82  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/0.82  --sup_passive_queues_freq               [8;1;4]
% 1.73/0.82  --demod_completeness_check              fast
% 1.73/0.82  --demod_use_ground                      true
% 1.73/0.82  --sup_to_prop_solver                    passive
% 1.73/0.82  --sup_prop_simpl_new                    true
% 1.73/0.82  --sup_prop_simpl_given                  true
% 1.73/0.82  --sup_fun_splitting                     false
% 1.73/0.82  --sup_smt_interval                      50000
% 1.73/0.82  
% 1.73/0.82  ------ Superposition Simplification Setup
% 1.73/0.82  
% 1.73/0.82  --sup_indices_passive                   []
% 1.73/0.82  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.82  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.82  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.82  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/0.82  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.82  --sup_full_bw                           [BwDemod]
% 1.73/0.82  --sup_immed_triv                        [TrivRules]
% 1.73/0.82  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/0.82  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.82  --sup_immed_bw_main                     []
% 1.73/0.82  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.82  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/0.82  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.82  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.82  
% 1.73/0.82  ------ Combination Options
% 1.73/0.82  
% 1.73/0.82  --comb_res_mult                         3
% 1.73/0.82  --comb_sup_mult                         2
% 1.73/0.82  --comb_inst_mult                        10
% 1.73/0.82  
% 1.73/0.82  ------ Debug Options
% 1.73/0.82  
% 1.73/0.82  --dbg_backtrace                         false
% 1.73/0.82  --dbg_dump_prop_clauses                 false
% 1.73/0.82  --dbg_dump_prop_clauses_file            -
% 1.73/0.82  --dbg_out_stat                          false
% 1.73/0.82  ------ Parsing...
% 1.73/0.82  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.73/0.82  
% 1.73/0.82  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.73/0.82  
% 1.73/0.82  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.73/0.82  
% 1.73/0.82  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.73/0.82  ------ Proving...
% 1.73/0.82  ------ Problem Properties 
% 1.73/0.82  
% 1.73/0.82  
% 1.73/0.82  clauses                                 7
% 1.73/0.82  conjectures                             1
% 1.73/0.82  EPR                                     0
% 1.73/0.82  Horn                                    7
% 1.73/0.82  unary                                   6
% 1.73/0.82  binary                                  1
% 1.73/0.82  lits                                    8
% 1.73/0.82  lits eq                                 6
% 1.73/0.82  fd_pure                                 0
% 1.73/0.82  fd_pseudo                               0
% 1.73/0.82  fd_cond                                 0
% 1.73/0.82  fd_pseudo_cond                          0
% 1.73/0.82  AC symbols                              0
% 1.73/0.82  
% 1.73/0.82  ------ Schedule dynamic 5 is on 
% 1.73/0.82  
% 1.73/0.82  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.73/0.82  
% 1.73/0.82  
% 1.73/0.82  ------ 
% 1.73/0.82  Current options:
% 1.73/0.82  ------ 
% 1.73/0.82  
% 1.73/0.82  ------ Input Options
% 1.73/0.82  
% 1.73/0.82  --out_options                           all
% 1.73/0.82  --tptp_safe_out                         true
% 1.73/0.82  --problem_path                          ""
% 1.73/0.82  --include_path                          ""
% 1.73/0.82  --clausifier                            res/vclausify_rel
% 1.73/0.82  --clausifier_options                    --mode clausify
% 1.73/0.82  --stdin                                 false
% 1.73/0.82  --stats_out                             all
% 1.73/0.82  
% 1.73/0.82  ------ General Options
% 1.73/0.82  
% 1.73/0.82  --fof                                   false
% 1.73/0.82  --time_out_real                         305.
% 1.73/0.82  --time_out_virtual                      -1.
% 1.73/0.82  --symbol_type_check                     false
% 1.73/0.82  --clausify_out                          false
% 1.73/0.82  --sig_cnt_out                           false
% 1.73/0.82  --trig_cnt_out                          false
% 1.73/0.82  --trig_cnt_out_tolerance                1.
% 1.73/0.82  --trig_cnt_out_sk_spl                   false
% 1.73/0.82  --abstr_cl_out                          false
% 1.73/0.82  
% 1.73/0.82  ------ Global Options
% 1.73/0.82  
% 1.73/0.82  --schedule                              default
% 1.73/0.82  --add_important_lit                     false
% 1.73/0.82  --prop_solver_per_cl                    1000
% 1.73/0.82  --min_unsat_core                        false
% 1.73/0.82  --soft_assumptions                      false
% 1.73/0.82  --soft_lemma_size                       3
% 1.73/0.82  --prop_impl_unit_size                   0
% 1.73/0.82  --prop_impl_unit                        []
% 1.73/0.82  --share_sel_clauses                     true
% 1.73/0.82  --reset_solvers                         false
% 1.73/0.82  --bc_imp_inh                            [conj_cone]
% 1.73/0.82  --conj_cone_tolerance                   3.
% 1.73/0.82  --extra_neg_conj                        none
% 1.73/0.82  --large_theory_mode                     true
% 1.73/0.82  --prolific_symb_bound                   200
% 1.73/0.82  --lt_threshold                          2000
% 1.73/0.82  --clause_weak_htbl                      true
% 1.73/0.82  --gc_record_bc_elim                     false
% 1.73/0.82  
% 1.73/0.82  ------ Preprocessing Options
% 1.73/0.82  
% 1.73/0.82  --preprocessing_flag                    true
% 1.73/0.82  --time_out_prep_mult                    0.1
% 1.73/0.82  --splitting_mode                        input
% 1.73/0.82  --splitting_grd                         true
% 1.73/0.82  --splitting_cvd                         false
% 1.73/0.82  --splitting_cvd_svl                     false
% 1.73/0.82  --splitting_nvd                         32
% 1.73/0.82  --sub_typing                            true
% 1.73/0.82  --prep_gs_sim                           true
% 1.73/0.82  --prep_unflatten                        true
% 1.73/0.82  --prep_res_sim                          true
% 1.73/0.82  --prep_upred                            true
% 1.73/0.82  --prep_sem_filter                       exhaustive
% 1.73/0.82  --prep_sem_filter_out                   false
% 1.73/0.82  --pred_elim                             true
% 1.73/0.82  --res_sim_input                         true
% 1.73/0.82  --eq_ax_congr_red                       true
% 1.73/0.82  --pure_diseq_elim                       true
% 1.73/0.82  --brand_transform                       false
% 1.73/0.82  --non_eq_to_eq                          false
% 1.73/0.82  --prep_def_merge                        true
% 1.73/0.82  --prep_def_merge_prop_impl              false
% 1.73/0.82  --prep_def_merge_mbd                    true
% 1.73/0.82  --prep_def_merge_tr_red                 false
% 1.73/0.82  --prep_def_merge_tr_cl                  false
% 1.73/0.82  --smt_preprocessing                     true
% 1.73/0.82  --smt_ac_axioms                         fast
% 1.73/0.82  --preprocessed_out                      false
% 1.73/0.82  --preprocessed_stats                    false
% 1.73/0.82  
% 1.73/0.82  ------ Abstraction refinement Options
% 1.73/0.82  
% 1.73/0.82  --abstr_ref                             []
% 1.73/0.82  --abstr_ref_prep                        false
% 1.73/0.82  --abstr_ref_until_sat                   false
% 1.73/0.82  --abstr_ref_sig_restrict                funpre
% 1.73/0.82  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/0.82  --abstr_ref_under                       []
% 1.73/0.82  
% 1.73/0.82  ------ SAT Options
% 1.73/0.82  
% 1.73/0.82  --sat_mode                              false
% 1.73/0.82  --sat_fm_restart_options                ""
% 1.73/0.82  --sat_gr_def                            false
% 1.73/0.82  --sat_epr_types                         true
% 1.73/0.82  --sat_non_cyclic_types                  false
% 1.73/0.82  --sat_finite_models                     false
% 1.73/0.82  --sat_fm_lemmas                         false
% 1.73/0.82  --sat_fm_prep                           false
% 1.73/0.82  --sat_fm_uc_incr                        true
% 1.73/0.82  --sat_out_model                         small
% 1.73/0.82  --sat_out_clauses                       false
% 1.73/0.82  
% 1.73/0.82  ------ QBF Options
% 1.73/0.82  
% 1.73/0.82  --qbf_mode                              false
% 1.73/0.82  --qbf_elim_univ                         false
% 1.73/0.82  --qbf_dom_inst                          none
% 1.73/0.82  --qbf_dom_pre_inst                      false
% 1.73/0.82  --qbf_sk_in                             false
% 1.73/0.82  --qbf_pred_elim                         true
% 1.73/0.82  --qbf_split                             512
% 1.73/0.82  
% 1.73/0.82  ------ BMC1 Options
% 1.73/0.82  
% 1.73/0.82  --bmc1_incremental                      false
% 1.73/0.82  --bmc1_axioms                           reachable_all
% 1.73/0.82  --bmc1_min_bound                        0
% 1.73/0.82  --bmc1_max_bound                        -1
% 1.73/0.82  --bmc1_max_bound_default                -1
% 1.73/0.82  --bmc1_symbol_reachability              true
% 1.73/0.82  --bmc1_property_lemmas                  false
% 1.73/0.82  --bmc1_k_induction                      false
% 1.73/0.82  --bmc1_non_equiv_states                 false
% 1.73/0.82  --bmc1_deadlock                         false
% 1.73/0.82  --bmc1_ucm                              false
% 1.73/0.82  --bmc1_add_unsat_core                   none
% 1.73/0.82  --bmc1_unsat_core_children              false
% 1.73/0.82  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/0.82  --bmc1_out_stat                         full
% 1.73/0.82  --bmc1_ground_init                      false
% 1.73/0.82  --bmc1_pre_inst_next_state              false
% 1.73/0.82  --bmc1_pre_inst_state                   false
% 1.73/0.82  --bmc1_pre_inst_reach_state             false
% 1.73/0.82  --bmc1_out_unsat_core                   false
% 1.73/0.82  --bmc1_aig_witness_out                  false
% 1.73/0.82  --bmc1_verbose                          false
% 1.73/0.82  --bmc1_dump_clauses_tptp                false
% 1.73/0.82  --bmc1_dump_unsat_core_tptp             false
% 1.73/0.82  --bmc1_dump_file                        -
% 1.73/0.82  --bmc1_ucm_expand_uc_limit              128
% 1.73/0.82  --bmc1_ucm_n_expand_iterations          6
% 1.73/0.82  --bmc1_ucm_extend_mode                  1
% 1.73/0.82  --bmc1_ucm_init_mode                    2
% 1.73/0.82  --bmc1_ucm_cone_mode                    none
% 1.73/0.82  --bmc1_ucm_reduced_relation_type        0
% 1.73/0.82  --bmc1_ucm_relax_model                  4
% 1.73/0.82  --bmc1_ucm_full_tr_after_sat            true
% 1.73/0.82  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/0.82  --bmc1_ucm_layered_model                none
% 1.73/0.82  --bmc1_ucm_max_lemma_size               10
% 1.73/0.82  
% 1.73/0.82  ------ AIG Options
% 1.73/0.82  
% 1.73/0.82  --aig_mode                              false
% 1.73/0.82  
% 1.73/0.82  ------ Instantiation Options
% 1.73/0.82  
% 1.73/0.82  --instantiation_flag                    true
% 1.73/0.82  --inst_sos_flag                         false
% 1.73/0.82  --inst_sos_phase                        true
% 1.73/0.82  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/0.82  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/0.82  --inst_lit_sel_side                     none
% 1.73/0.82  --inst_solver_per_active                1400
% 1.73/0.82  --inst_solver_calls_frac                1.
% 1.73/0.82  --inst_passive_queue_type               priority_queues
% 1.73/0.82  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/0.82  --inst_passive_queues_freq              [25;2]
% 1.73/0.82  --inst_dismatching                      true
% 1.73/0.82  --inst_eager_unprocessed_to_passive     true
% 1.73/0.82  --inst_prop_sim_given                   true
% 1.73/0.82  --inst_prop_sim_new                     false
% 1.73/0.82  --inst_subs_new                         false
% 1.73/0.82  --inst_eq_res_simp                      false
% 1.73/0.82  --inst_subs_given                       false
% 1.73/0.82  --inst_orphan_elimination               true
% 1.73/0.82  --inst_learning_loop_flag               true
% 1.73/0.82  --inst_learning_start                   3000
% 1.73/0.82  --inst_learning_factor                  2
% 1.73/0.82  --inst_start_prop_sim_after_learn       3
% 1.73/0.82  --inst_sel_renew                        solver
% 1.73/0.82  --inst_lit_activity_flag                true
% 1.73/0.82  --inst_restr_to_given                   false
% 1.73/0.82  --inst_activity_threshold               500
% 1.73/0.82  --inst_out_proof                        true
% 1.73/0.82  
% 1.73/0.82  ------ Resolution Options
% 1.73/0.82  
% 1.73/0.82  --resolution_flag                       false
% 1.73/0.82  --res_lit_sel                           adaptive
% 1.73/0.82  --res_lit_sel_side                      none
% 1.73/0.82  --res_ordering                          kbo
% 1.73/0.82  --res_to_prop_solver                    active
% 1.73/0.82  --res_prop_simpl_new                    false
% 1.73/0.82  --res_prop_simpl_given                  true
% 1.73/0.82  --res_passive_queue_type                priority_queues
% 1.73/0.82  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/0.82  --res_passive_queues_freq               [15;5]
% 1.73/0.82  --res_forward_subs                      full
% 1.73/0.82  --res_backward_subs                     full
% 1.73/0.82  --res_forward_subs_resolution           true
% 1.73/0.82  --res_backward_subs_resolution          true
% 1.73/0.82  --res_orphan_elimination                true
% 1.73/0.82  --res_time_limit                        2.
% 1.73/0.82  --res_out_proof                         true
% 1.73/0.82  
% 1.73/0.82  ------ Superposition Options
% 1.73/0.82  
% 1.73/0.82  --superposition_flag                    true
% 1.73/0.82  --sup_passive_queue_type                priority_queues
% 1.73/0.82  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/0.82  --sup_passive_queues_freq               [8;1;4]
% 1.73/0.82  --demod_completeness_check              fast
% 1.73/0.82  --demod_use_ground                      true
% 1.73/0.82  --sup_to_prop_solver                    passive
% 1.73/0.82  --sup_prop_simpl_new                    true
% 1.73/0.82  --sup_prop_simpl_given                  true
% 1.73/0.82  --sup_fun_splitting                     false
% 1.73/0.82  --sup_smt_interval                      50000
% 1.73/0.82  
% 1.73/0.82  ------ Superposition Simplification Setup
% 1.73/0.82  
% 1.73/0.82  --sup_indices_passive                   []
% 1.73/0.82  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.82  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.82  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.82  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/0.82  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.82  --sup_full_bw                           [BwDemod]
% 1.73/0.82  --sup_immed_triv                        [TrivRules]
% 1.73/0.82  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/0.82  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.82  --sup_immed_bw_main                     []
% 1.73/0.82  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.82  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/0.82  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.82  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.82  
% 1.73/0.82  ------ Combination Options
% 1.73/0.82  
% 1.73/0.82  --comb_res_mult                         3
% 1.73/0.82  --comb_sup_mult                         2
% 1.73/0.82  --comb_inst_mult                        10
% 1.73/0.82  
% 1.73/0.82  ------ Debug Options
% 1.73/0.82  
% 1.73/0.82  --dbg_backtrace                         false
% 1.73/0.82  --dbg_dump_prop_clauses                 false
% 1.73/0.82  --dbg_dump_prop_clauses_file            -
% 1.73/0.82  --dbg_out_stat                          false
% 1.73/0.82  
% 1.73/0.82  
% 1.73/0.82  
% 1.73/0.82  
% 1.73/0.82  ------ Proving...
% 1.73/0.82  
% 1.73/0.82  
% 1.73/0.82  % SZS status Theorem for theBenchmark.p
% 1.73/0.82  
% 1.73/0.82  % SZS output start CNFRefutation for theBenchmark.p
% 1.73/0.82  
% 1.73/0.82  fof(f12,axiom,(
% 1.73/0.82    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f33,plain,(
% 1.73/0.82    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.73/0.82    inference(cnf_transformation,[],[f12])).
% 1.73/0.82  
% 1.73/0.82  fof(f4,axiom,(
% 1.73/0.82    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f25,plain,(
% 1.73/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f4])).
% 1.73/0.82  
% 1.73/0.82  fof(f5,axiom,(
% 1.73/0.82    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f26,plain,(
% 1.73/0.82    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f5])).
% 1.73/0.82  
% 1.73/0.82  fof(f6,axiom,(
% 1.73/0.82    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f27,plain,(
% 1.73/0.82    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f6])).
% 1.73/0.82  
% 1.73/0.82  fof(f7,axiom,(
% 1.73/0.82    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f28,plain,(
% 1.73/0.82    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f7])).
% 1.73/0.82  
% 1.73/0.82  fof(f37,plain,(
% 1.73/0.82    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.73/0.82    inference(definition_unfolding,[],[f27,f28])).
% 1.73/0.82  
% 1.73/0.82  fof(f38,plain,(
% 1.73/0.82    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.73/0.82    inference(definition_unfolding,[],[f26,f37])).
% 1.73/0.82  
% 1.73/0.82  fof(f39,plain,(
% 1.73/0.82    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.73/0.82    inference(definition_unfolding,[],[f25,f38])).
% 1.73/0.82  
% 1.73/0.82  fof(f47,plain,(
% 1.73/0.82    ( ! [X2,X0,X3,X1] : (v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.73/0.82    inference(definition_unfolding,[],[f33,f39])).
% 1.73/0.82  
% 1.73/0.82  fof(f11,axiom,(
% 1.73/0.82    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f16,plain,(
% 1.73/0.82    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.82    inference(ennf_transformation,[],[f11])).
% 1.73/0.82  
% 1.73/0.82  fof(f32,plain,(
% 1.73/0.82    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f16])).
% 1.73/0.82  
% 1.73/0.82  fof(f10,axiom,(
% 1.73/0.82    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f31,plain,(
% 1.73/0.82    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.73/0.82    inference(cnf_transformation,[],[f10])).
% 1.73/0.82  
% 1.73/0.82  fof(f40,plain,(
% 1.73/0.82    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.73/0.82    inference(definition_unfolding,[],[f31,f39])).
% 1.73/0.82  
% 1.73/0.82  fof(f46,plain,(
% 1.73/0.82    ( ! [X0] : (k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.82    inference(definition_unfolding,[],[f32,f40])).
% 1.73/0.82  
% 1.73/0.82  fof(f13,axiom,(
% 1.73/0.82    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_tarski(X1,X3) = k2_relat_1(X4) & k2_tarski(X0,X2) = k1_relat_1(X4))))),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f17,plain,(
% 1.73/0.82    ! [X0,X1,X2,X3,X4] : (((k2_tarski(X1,X3) = k2_relat_1(X4) & k2_tarski(X0,X2) = k1_relat_1(X4)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 1.73/0.82    inference(ennf_transformation,[],[f13])).
% 1.73/0.82  
% 1.73/0.82  fof(f18,plain,(
% 1.73/0.82    ! [X0,X1,X2,X3,X4] : ((k2_tarski(X1,X3) = k2_relat_1(X4) & k2_tarski(X0,X2) = k1_relat_1(X4)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 1.73/0.82    inference(flattening,[],[f17])).
% 1.73/0.82  
% 1.73/0.82  fof(f34,plain,(
% 1.73/0.82    ( ! [X4,X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(X4) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f18])).
% 1.73/0.82  
% 1.73/0.82  fof(f49,plain,(
% 1.73/0.82    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X2) = k1_relat_1(X4) | k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.73/0.82    inference(definition_unfolding,[],[f34,f39,f39])).
% 1.73/0.82  
% 1.73/0.82  fof(f52,plain,(
% 1.73/0.82    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X2) = k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.73/0.82    inference(equality_resolution,[],[f49])).
% 1.73/0.82  
% 1.73/0.82  fof(f35,plain,(
% 1.73/0.82    ( ! [X4,X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(X4) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f18])).
% 1.73/0.82  
% 1.73/0.82  fof(f48,plain,(
% 1.73/0.82    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X1,X1,X1,X1,X1,X3) = k2_relat_1(X4) | k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.73/0.82    inference(definition_unfolding,[],[f35,f39,f39])).
% 1.73/0.82  
% 1.73/0.82  fof(f51,plain,(
% 1.73/0.82    ( ! [X2,X0,X3,X1] : (k4_enumset1(X1,X1,X1,X1,X1,X3) = k2_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.73/0.82    inference(equality_resolution,[],[f48])).
% 1.73/0.82  
% 1.73/0.82  fof(f8,axiom,(
% 1.73/0.82    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f29,plain,(
% 1.73/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f8])).
% 1.73/0.82  
% 1.73/0.82  fof(f1,axiom,(
% 1.73/0.82    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f22,plain,(
% 1.73/0.82    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 1.73/0.82    inference(cnf_transformation,[],[f1])).
% 1.73/0.82  
% 1.73/0.82  fof(f3,axiom,(
% 1.73/0.82    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f24,plain,(
% 1.73/0.82    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.73/0.82    inference(cnf_transformation,[],[f3])).
% 1.73/0.82  
% 1.73/0.82  fof(f41,plain,(
% 1.73/0.82    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 1.73/0.82    inference(definition_unfolding,[],[f24,f39])).
% 1.73/0.82  
% 1.73/0.82  fof(f42,plain,(
% 1.73/0.82    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6)))) )),
% 1.73/0.82    inference(definition_unfolding,[],[f22,f40,f41])).
% 1.73/0.82  
% 1.73/0.82  fof(f44,plain,(
% 1.73/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 1.73/0.82    inference(definition_unfolding,[],[f29,f42])).
% 1.73/0.82  
% 1.73/0.82  fof(f14,conjecture,(
% 1.73/0.82    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.73/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.82  
% 1.73/0.82  fof(f15,negated_conjecture,(
% 1.73/0.82    ~! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.73/0.82    inference(negated_conjecture,[],[f14])).
% 1.73/0.82  
% 1.73/0.82  fof(f19,plain,(
% 1.73/0.82    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.73/0.82    inference(ennf_transformation,[],[f15])).
% 1.73/0.82  
% 1.73/0.82  fof(f20,plain,(
% 1.73/0.82    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.73/0.82    introduced(choice_axiom,[])).
% 1.73/0.82  
% 1.73/0.82  fof(f21,plain,(
% 1.73/0.82    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.73/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 1.73/0.82  
% 1.73/0.82  fof(f36,plain,(
% 1.73/0.82    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.73/0.82    inference(cnf_transformation,[],[f21])).
% 1.73/0.82  
% 1.73/0.82  fof(f50,plain,(
% 1.73/0.82    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k3_relat_1(k4_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 1.73/0.82    inference(definition_unfolding,[],[f36,f39,f41])).
% 1.73/0.82  
% 1.73/0.82  cnf(c_3,plain,
% 1.73/0.82      ( v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
% 1.73/0.82      inference(cnf_transformation,[],[f47]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_127,plain,
% 1.73/0.82      ( v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = iProver_top ),
% 1.73/0.82      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_2,plain,
% 1.73/0.82      ( ~ v1_relat_1(X0)
% 1.73/0.82      | k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 1.73/0.82      inference(cnf_transformation,[],[f46]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_128,plain,
% 1.73/0.82      ( k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 1.73/0.82      | v1_relat_1(X0) != iProver_top ),
% 1.73/0.82      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_204,plain,
% 1.73/0.82      ( k3_tarski(k4_enumset1(k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k2_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))))) = k3_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
% 1.73/0.82      inference(superposition,[status(thm)],[c_127,c_128]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_5,plain,
% 1.73/0.82      ( ~ v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
% 1.73/0.82      | k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k4_enumset1(X0,X0,X0,X0,X0,X2) ),
% 1.73/0.82      inference(cnf_transformation,[],[f52]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_30,plain,
% 1.73/0.82      ( k1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k4_enumset1(X0,X0,X0,X0,X0,X2) ),
% 1.73/0.82      inference(global_propositional_subsumption,[status(thm)],[c_5,c_3]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_4,plain,
% 1.73/0.82      ( ~ v1_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
% 1.73/0.82      | k2_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k4_enumset1(X1,X1,X1,X1,X1,X3) ),
% 1.73/0.82      inference(cnf_transformation,[],[f51]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_34,plain,
% 1.73/0.82      ( k2_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k4_enumset1(X1,X1,X1,X1,X1,X3) ),
% 1.73/0.82      inference(global_propositional_subsumption,[status(thm)],[c_4,c_3]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_391,plain,
% 1.73/0.82      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X2,X2,X3))) = k3_relat_1(k4_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X3))) ),
% 1.73/0.82      inference(light_normalisation,[status(thm)],[c_204,c_30,c_34]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_0,plain,
% 1.73/0.82      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 1.73/0.82      inference(cnf_transformation,[],[f44]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_398,plain,
% 1.73/0.82      ( k3_relat_1(k4_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1))) = k4_enumset1(X0,X0,X0,X0,X2,X1) ),
% 1.73/0.82      inference(superposition,[status(thm)],[c_391,c_0]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_6,negated_conjecture,
% 1.73/0.82      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k3_relat_1(k4_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
% 1.73/0.82      inference(cnf_transformation,[],[f50]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_573,plain,
% 1.73/0.82      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
% 1.73/0.82      inference(demodulation,[status(thm)],[c_398,c_6]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_66,plain,( X0 = X0 ),theory(equality) ).
% 1.73/0.82  
% 1.73/0.82  cnf(c_164,plain,
% 1.73/0.82      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
% 1.73/0.82      inference(instantiation,[status(thm)],[c_66]) ).
% 1.73/0.82  
% 1.73/0.82  cnf(contradiction,plain,
% 1.73/0.82      ( $false ),
% 1.73/0.82      inference(minisat,[status(thm)],[c_573,c_164]) ).
% 1.73/0.82  
% 1.73/0.82  
% 1.73/0.82  % SZS output end CNFRefutation for theBenchmark.p
% 1.73/0.82  
% 1.73/0.82  ------                               Statistics
% 1.73/0.82  
% 1.73/0.82  ------ General
% 1.73/0.82  
% 1.73/0.82  abstr_ref_over_cycles:                  0
% 1.73/0.82  abstr_ref_under_cycles:                 0
% 1.73/0.82  gc_basic_clause_elim:                   0
% 1.73/0.82  forced_gc_time:                         0
% 1.73/0.82  parsing_time:                           0.007
% 1.73/0.82  unif_index_cands_time:                  0.
% 1.73/0.82  unif_index_add_time:                    0.
% 1.73/0.82  orderings_time:                         0.
% 1.73/0.82  out_proof_time:                         0.007
% 1.73/0.82  total_time:                             0.05
% 1.73/0.82  num_of_symbols:                         40
% 1.73/0.82  num_of_terms:                           1170
% 1.73/0.82  
% 1.73/0.82  ------ Preprocessing
% 1.73/0.82  
% 1.73/0.82  num_of_splits:                          0
% 1.73/0.82  num_of_split_atoms:                     0
% 1.73/0.82  num_of_reused_defs:                     0
% 1.73/0.82  num_eq_ax_congr_red:                    0
% 1.73/0.82  num_of_sem_filtered_clauses:            1
% 1.73/0.82  num_of_subtypes:                        1
% 1.73/0.82  monotx_restored_types:                  0
% 1.73/0.82  sat_num_of_epr_types:                   0
% 1.73/0.82  sat_num_of_non_cyclic_types:            0
% 1.73/0.82  sat_guarded_non_collapsed_types:        0
% 1.73/0.82  num_pure_diseq_elim:                    0
% 1.73/0.82  simp_replaced_by:                       0
% 1.73/0.82  res_preprocessed:                       40
% 1.73/0.82  prep_upred:                             0
% 1.73/0.82  prep_unflattend:                        1
% 1.73/0.82  smt_new_axioms:                         0
% 1.73/0.82  pred_elim_cands:                        1
% 1.73/0.82  pred_elim:                              0
% 1.73/0.82  pred_elim_cl:                           0
% 1.73/0.82  pred_elim_cycles:                       1
% 1.73/0.82  merged_defs:                            0
% 1.73/0.82  merged_defs_ncl:                        0
% 1.73/0.82  bin_hyper_res:                          0
% 1.73/0.82  prep_cycles:                            3
% 1.73/0.82  pred_elim_time:                         0.
% 1.73/0.82  splitting_time:                         0.
% 1.73/0.82  sem_filter_time:                        0.
% 1.73/0.82  monotx_time:                            0.
% 1.73/0.82  subtype_inf_time:                       0.
% 1.73/0.82  
% 1.73/0.82  ------ Problem properties
% 1.73/0.82  
% 1.73/0.82  clauses:                                7
% 1.73/0.82  conjectures:                            1
% 1.73/0.82  epr:                                    0
% 1.73/0.82  horn:                                   7
% 1.73/0.82  ground:                                 1
% 1.73/0.82  unary:                                  6
% 1.73/0.82  binary:                                 1
% 1.73/0.82  lits:                                   8
% 1.73/0.82  lits_eq:                                6
% 1.73/0.82  fd_pure:                                0
% 1.73/0.82  fd_pseudo:                              0
% 1.73/0.82  fd_cond:                                0
% 1.73/0.82  fd_pseudo_cond:                         0
% 1.73/0.82  ac_symbols:                             0
% 1.73/0.82  
% 1.73/0.82  ------ Propositional Solver
% 1.73/0.82  
% 1.73/0.82  prop_solver_calls:                      23
% 1.73/0.82  prop_fast_solver_calls:                 168
% 1.73/0.82  smt_solver_calls:                       0
% 1.73/0.82  smt_fast_solver_calls:                  0
% 1.73/0.82  prop_num_of_clauses:                    247
% 1.73/0.82  prop_preprocess_simplified:             1052
% 1.73/0.82  prop_fo_subsumed:                       2
% 1.73/0.82  prop_solver_time:                       0.
% 1.73/0.82  smt_solver_time:                        0.
% 1.73/0.82  smt_fast_solver_time:                   0.
% 1.73/0.82  prop_fast_solver_time:                  0.
% 1.73/0.82  prop_unsat_core_time:                   0.
% 1.73/0.82  
% 1.73/0.82  ------ QBF
% 1.73/0.82  
% 1.73/0.82  qbf_q_res:                              0
% 1.73/0.82  qbf_num_tautologies:                    0
% 1.73/0.82  qbf_prep_cycles:                        0
% 1.73/0.82  
% 1.73/0.82  ------ BMC1
% 1.73/0.82  
% 1.73/0.82  bmc1_current_bound:                     -1
% 1.73/0.82  bmc1_last_solved_bound:                 -1
% 1.73/0.82  bmc1_unsat_core_size:                   -1
% 1.73/0.82  bmc1_unsat_core_parents_size:           -1
% 1.73/0.82  bmc1_merge_next_fun:                    0
% 1.73/0.82  bmc1_unsat_core_clauses_time:           0.
% 1.73/0.82  
% 1.73/0.82  ------ Instantiation
% 1.73/0.82  
% 1.73/0.82  inst_num_of_clauses:                    104
% 1.73/0.82  inst_num_in_passive:                    19
% 1.73/0.82  inst_num_in_active:                     57
% 1.73/0.82  inst_num_in_unprocessed:                28
% 1.73/0.82  inst_num_of_loops:                      60
% 1.73/0.82  inst_num_of_learning_restarts:          0
% 1.73/0.82  inst_num_moves_active_passive:          0
% 1.73/0.82  inst_lit_activity:                      0
% 1.73/0.82  inst_lit_activity_moves:                0
% 1.73/0.82  inst_num_tautologies:                   0
% 1.73/0.82  inst_num_prop_implied:                  0
% 1.73/0.82  inst_num_existing_simplified:           0
% 1.73/0.82  inst_num_eq_res_simplified:             0
% 1.73/0.82  inst_num_child_elim:                    0
% 1.73/0.82  inst_num_of_dismatching_blockings:      16
% 1.73/0.82  inst_num_of_non_proper_insts:           67
% 1.73/0.82  inst_num_of_duplicates:                 0
% 1.73/0.82  inst_inst_num_from_inst_to_res:         0
% 1.73/0.82  inst_dismatching_checking_time:         0.
% 1.73/0.82  
% 1.73/0.82  ------ Resolution
% 1.73/0.82  
% 1.73/0.82  res_num_of_clauses:                     0
% 1.73/0.82  res_num_in_passive:                     0
% 1.73/0.82  res_num_in_active:                      0
% 1.73/0.82  res_num_of_loops:                       43
% 1.73/0.82  res_forward_subset_subsumed:            12
% 1.73/0.82  res_backward_subset_subsumed:           0
% 1.73/0.82  res_forward_subsumed:                   0
% 1.73/0.82  res_backward_subsumed:                  0
% 1.73/0.82  res_forward_subsumption_resolution:     0
% 1.73/0.82  res_backward_subsumption_resolution:    0
% 1.73/0.82  res_clause_to_clause_subsumption:       146
% 1.73/0.82  res_orphan_elimination:                 0
% 1.73/0.82  res_tautology_del:                      10
% 1.73/0.82  res_num_eq_res_simplified:              0
% 1.73/0.82  res_num_sel_changes:                    0
% 1.73/0.82  res_moves_from_active_to_pass:          0
% 1.73/0.82  
% 1.73/0.82  ------ Superposition
% 1.73/0.82  
% 1.73/0.82  sup_time_total:                         0.
% 1.73/0.82  sup_time_generating:                    0.
% 1.73/0.82  sup_time_sim_full:                      0.
% 1.73/0.82  sup_time_sim_immed:                     0.
% 1.73/0.82  
% 1.73/0.82  sup_num_of_clauses:                     31
% 1.73/0.82  sup_num_in_active:                      8
% 1.73/0.82  sup_num_in_passive:                     23
% 1.73/0.82  sup_num_of_loops:                       10
% 1.73/0.82  sup_fw_superposition:                   14
% 1.73/0.82  sup_bw_superposition:                   61
% 1.73/0.82  sup_immediate_simplified:               6
% 1.73/0.82  sup_given_eliminated:                   1
% 1.73/0.82  comparisons_done:                       0
% 1.73/0.82  comparisons_avoided:                    0
% 1.73/0.82  
% 1.73/0.82  ------ Simplifications
% 1.73/0.82  
% 1.73/0.82  
% 1.73/0.82  sim_fw_subset_subsumed:                 0
% 1.73/0.82  sim_bw_subset_subsumed:                 0
% 1.73/0.82  sim_fw_subsumed:                        1
% 1.73/0.82  sim_bw_subsumed:                        0
% 1.73/0.82  sim_fw_subsumption_res:                 0
% 1.73/0.82  sim_bw_subsumption_res:                 0
% 1.73/0.82  sim_tautology_del:                      0
% 1.73/0.82  sim_eq_tautology_del:                   0
% 1.73/0.82  sim_eq_res_simp:                        0
% 1.73/0.82  sim_fw_demodulated:                     2
% 1.73/0.82  sim_bw_demodulated:                     4
% 1.73/0.82  sim_light_normalised:                   3
% 1.73/0.82  sim_joinable_taut:                      0
% 1.73/0.82  sim_joinable_simp:                      0
% 1.73/0.82  sim_ac_normalised:                      0
% 1.73/0.82  sim_smt_subsumption:                    0
% 1.73/0.82  
%------------------------------------------------------------------------------
