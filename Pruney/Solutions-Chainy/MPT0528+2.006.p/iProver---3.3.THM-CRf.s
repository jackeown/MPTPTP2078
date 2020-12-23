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
% DateTime   : Thu Dec  3 11:45:31 EST 2020

% Result     : Theorem 14.75s
% Output     : CNFRefutation 14.75s
% Verified   : 
% Statistics : Number of formulae       :  180 (270277 expanded)
%              Number of clauses        :  161 (127840 expanded)
%              Number of leaves         :   10 (47486 expanded)
%              Depth                    :   58
%              Number of atoms          :  248 (485736 expanded)
%              Number of equality atoms :  213 (248033 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,plain,(
    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_65,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_190,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k3_xboole_0(X1,X2),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_67,plain,
    ( ~ v1_relat_1(X0_34)
    | k8_relat_1(k3_xboole_0(X0_35,X1_35),X0_34) = k8_relat_1(X0_35,k8_relat_1(X1_35,X0_34)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_189,plain,
    ( k8_relat_1(k3_xboole_0(X0_35,X1_35),X0_34) = k8_relat_1(X0_35,k8_relat_1(X1_35,X0_34))
    | v1_relat_1(X0_34) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_367,plain,
    ( k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)) = k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1) ),
    inference(superposition,[status(thm)],[c_190,c_189])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_68,plain,
    ( ~ v1_relat_1(X0_34)
    | k8_relat_1(k2_relat_1(X0_34),X0_34) = X0_34 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_188,plain,
    ( k8_relat_1(k2_relat_1(X0_34),X0_34) = X0_34
    | v1_relat_1(X0_34) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_245,plain,
    ( k8_relat_1(k2_relat_1(sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_190,c_188])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_70,plain,
    ( ~ v1_relat_1(X0_34)
    | v1_relat_1(k8_relat_1(X0_35,X0_34)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_186,plain,
    ( v1_relat_1(X0_34) != iProver_top
    | v1_relat_1(k8_relat_1(X0_35,X0_34)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_246,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,X0_34)),k8_relat_1(X0_35,X0_34)) = k8_relat_1(X0_35,X0_34)
    | v1_relat_1(X0_34) != iProver_top ),
    inference(superposition,[status(thm)],[c_186,c_188])).

cnf(c_482,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X0_35,sK1)) = k8_relat_1(X0_35,sK1) ),
    inference(superposition,[status(thm)],[c_190,c_246])).

cnf(c_628,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1) ),
    inference(superposition,[status(thm)],[c_367,c_482])).

cnf(c_632,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_628,c_367])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_69,plain,
    ( ~ v1_relat_1(X0_34)
    | k3_xboole_0(k2_relat_1(X0_34),X0_35) = k2_relat_1(k8_relat_1(X0_35,X0_34)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_187,plain,
    ( k3_xboole_0(k2_relat_1(X0_34),X0_35) = k2_relat_1(k8_relat_1(X0_35,X0_34))
    | v1_relat_1(X0_34) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_306,plain,
    ( k3_xboole_0(k2_relat_1(sK1),X0_35) = k2_relat_1(k8_relat_1(X0_35,sK1)) ),
    inference(superposition,[status(thm)],[c_190,c_187])).

cnf(c_496,plain,
    ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_367,c_186])).

cnf(c_6,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_636,plain,
    ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_6])).

cnf(c_647,plain,
    ( k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))) = k8_relat_1(k3_xboole_0(X0_35,X1_35),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
    inference(superposition,[status(thm)],[c_636,c_189])).

cnf(c_1566,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) ),
    inference(superposition,[status(thm)],[c_306,c_647])).

cnf(c_4714,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
    inference(superposition,[status(thm)],[c_245,c_1566])).

cnf(c_648,plain,
    ( k3_xboole_0(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),X2_35) = k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
    inference(superposition,[status(thm)],[c_636,c_187])).

cnf(c_746,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) ),
    inference(superposition,[status(thm)],[c_648,c_367])).

cnf(c_2675,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(k3_xboole_0(X2_35,X3_35),sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))))),sK1) ),
    inference(superposition,[status(thm)],[c_647,c_746])).

cnf(c_2790,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_2675,c_367])).

cnf(c_7225,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X3_35,X4_35),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))))),sK1) ),
    inference(superposition,[status(thm)],[c_647,c_2790])).

cnf(c_7426,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) ),
    inference(demodulation,[status(thm)],[c_7225,c_367])).

cnf(c_14710,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k3_xboole_0(X4_35,X5_35),sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X5_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))))))),sK1) ),
    inference(superposition,[status(thm)],[c_647,c_7426])).

cnf(c_15012,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X5_35,sK1))))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X4_35,k8_relat_1(X5_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))) ),
    inference(demodulation,[status(thm)],[c_14710,c_367])).

cnf(c_27621,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),sK1))))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))))),sK1) ),
    inference(superposition,[status(thm)],[c_4714,c_15012])).

cnf(c_28081,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_27621,c_245])).

cnf(c_28724,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),sK1))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))))),sK1) ),
    inference(superposition,[status(thm)],[c_245,c_28081])).

cnf(c_29109,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
    inference(light_normalisation,[status(thm)],[c_28724,c_245,c_1566])).

cnf(c_29256,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))),sK1) ),
    inference(superposition,[status(thm)],[c_4714,c_29109])).

cnf(c_29679,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_29256,c_245])).

cnf(c_30098,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))))),sK1) ),
    inference(superposition,[status(thm)],[c_29679,c_29109])).

cnf(c_7234,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X1_35,X2_35),sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))),sK1) ),
    inference(superposition,[status(thm)],[c_367,c_2790])).

cnf(c_7399,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_7234,c_367])).

cnf(c_7427,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_7426,c_7399])).

cnf(c_744,plain,
    ( k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),sK1)))) = k3_xboole_0(k2_relat_1(k8_relat_1(X1_35,sK1)),X0_35) ),
    inference(superposition,[status(thm)],[c_245,c_648])).

cnf(c_753,plain,
    ( k3_xboole_0(k2_relat_1(k8_relat_1(X0_35,sK1)),X1_35) = k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_744,c_245])).

cnf(c_1081,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))),sK1) ),
    inference(superposition,[status(thm)],[c_753,c_367])).

cnf(c_495,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_306,c_367])).

cnf(c_1039,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),sK1) ),
    inference(superposition,[status(thm)],[c_367,c_495])).

cnf(c_1067,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),sK1) ),
    inference(light_normalisation,[status(thm)],[c_1039,c_367])).

cnf(c_2018,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,sK1)),k8_relat_1(X0_35,sK1)) ),
    inference(demodulation,[status(thm)],[c_1081,c_1067])).

cnf(c_7231,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))))),sK1) ),
    inference(superposition,[status(thm)],[c_2018,c_2790])).

cnf(c_7406,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_7231,c_7399])).

cnf(c_643,plain,
    ( v1_relat_1(k8_relat_1(X0_35,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_482,c_636])).

cnf(c_766,plain,
    ( k8_relat_1(k3_xboole_0(X0_35,X1_35),k8_relat_1(X2_35,sK1)) = k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) ),
    inference(superposition,[status(thm)],[c_643,c_189])).

cnf(c_1525,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
    inference(superposition,[status(thm)],[c_306,c_766])).

cnf(c_7408,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_7406,c_1525])).

cnf(c_7433,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_7427,c_7408])).

cnf(c_7436,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_7433,c_245])).

cnf(c_30305,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),sK1))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_30098,c_7436,c_28081])).

cnf(c_4815,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X1_35,X2_35),sK1))) ),
    inference(superposition,[status(thm)],[c_367,c_4714])).

cnf(c_4845,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) ),
    inference(demodulation,[status(thm)],[c_4815,c_367])).

cnf(c_6677,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k3_xboole_0(X2_35,X3_35),sK1)))) ),
    inference(superposition,[status(thm)],[c_367,c_4845])).

cnf(c_6709,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))) ),
    inference(demodulation,[status(thm)],[c_6677,c_367])).

cnf(c_645,plain,
    ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_367,c_636])).

cnf(c_861,plain,
    ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_367,c_645])).

cnf(c_881,plain,
    ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_367,c_861])).

cnf(c_1192,plain,
    ( k3_xboole_0(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))),X5_35) = k2_relat_1(k8_relat_1(X5_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))))))) ),
    inference(superposition,[status(thm)],[c_881,c_187])).

cnf(c_6106,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))),k8_relat_1(X5_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X5_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))))))),sK1) ),
    inference(superposition,[status(thm)],[c_1192,c_367])).

cnf(c_21136,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),k8_relat_1(k2_relat_1(sK1),sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) ),
    inference(superposition,[status(thm)],[c_6709,c_6106])).

cnf(c_21162,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),sK1)))))),k8_relat_1(X4_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) ),
    inference(superposition,[status(thm)],[c_245,c_6106])).

cnf(c_10881,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(superposition,[status(thm)],[c_766,c_7436])).

cnf(c_10885,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k3_xboole_0(X1_35,X2_35),k8_relat_1(X0_35,sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(superposition,[status(thm)],[c_367,c_7436])).

cnf(c_11069,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_10885,c_766])).

cnf(c_2681,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),sK1))),k8_relat_1(X1_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))),sK1) ),
    inference(superposition,[status(thm)],[c_245,c_746])).

cnf(c_2772,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_2681,c_245,c_1525])).

cnf(c_10889,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X0_35,sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(superposition,[status(thm)],[c_2772,c_7436])).

cnf(c_7222,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) ),
    inference(superposition,[status(thm)],[c_4714,c_2790])).

cnf(c_7446,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_7222,c_245,c_2772])).

cnf(c_10891,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(superposition,[status(thm)],[c_7446,c_7436])).

cnf(c_10901,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X2_35,sK1)) ),
    inference(superposition,[status(thm)],[c_245,c_7436])).

cnf(c_11017,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))),k8_relat_1(X2_35,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_10901,c_245])).

cnf(c_2023,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X1_35,X2_35),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))),k8_relat_1(X0_35,sK1)) ),
    inference(superposition,[status(thm)],[c_367,c_2018])).

cnf(c_2072,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))),k8_relat_1(X0_35,sK1)) ),
    inference(demodulation,[status(thm)],[c_2023,c_367])).

cnf(c_5267,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k3_xboole_0(X2_35,X3_35),sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))),k8_relat_1(X0_35,sK1)) ),
    inference(superposition,[status(thm)],[c_367,c_2072])).

cnf(c_5366,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) ),
    inference(demodulation,[status(thm)],[c_5267,c_367])).

cnf(c_11018,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))) ),
    inference(demodulation,[status(thm)],[c_11017,c_2072,c_5366])).

cnf(c_11045,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_10891,c_11018])).

cnf(c_11051,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_10889,c_11045])).

cnf(c_11053,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X1_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_11051,c_2072])).

cnf(c_11070,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_11069,c_11053])).

cnf(c_11090,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X2_35,X1_35),sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_10881,c_11070])).

cnf(c_11092,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_11090,c_367])).

cnf(c_17044,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X3_35,sK1)) ),
    inference(superposition,[status(thm)],[c_245,c_11092])).

cnf(c_17253,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X1_35,sK1))))) ),
    inference(light_normalisation,[status(thm)],[c_17044,c_245,c_5366])).

cnf(c_17642,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X3_35,X4_35),sK1))))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X0_35,sK1)) ),
    inference(superposition,[status(thm)],[c_766,c_17253])).

cnf(c_9660,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X3_35,X4_35),sK1))))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))))),k8_relat_1(X0_35,sK1)) ),
    inference(superposition,[status(thm)],[c_367,c_5366])).

cnf(c_9839,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))))),k8_relat_1(X0_35,sK1)) ),
    inference(demodulation,[status(thm)],[c_9660,c_367])).

cnf(c_17943,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))),k8_relat_1(X4_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X3_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))) ),
    inference(demodulation,[status(thm)],[c_17642,c_367,c_9839])).

cnf(c_21496,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X2_35,sK1)))))),sK1) ),
    inference(light_normalisation,[status(thm)],[c_21162,c_245,c_17943])).

cnf(c_21570,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),k8_relat_1(k2_relat_1(sK1),sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X3_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))) ),
    inference(demodulation,[status(thm)],[c_21136,c_21496])).

cnf(c_7641,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1))) ),
    inference(superposition,[status(thm)],[c_766,c_7446])).

cnf(c_7818,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
    inference(light_normalisation,[status(thm)],[c_7641,c_367])).

cnf(c_7852,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X1_35,X2_35),sK1)))) ),
    inference(superposition,[status(thm)],[c_766,c_7818])).

cnf(c_8027,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) ),
    inference(demodulation,[status(thm)],[c_7852,c_367])).

cnf(c_21572,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))) ),
    inference(light_normalisation,[status(thm)],[c_21570,c_245,c_8027])).

cnf(c_21948,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,k8_relat_1(X2_35,sK1))))) ),
    inference(superposition,[status(thm)],[c_245,c_21572])).

cnf(c_22046,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,k8_relat_1(X2_35,sK1)))) ),
    inference(light_normalisation,[status(thm)],[c_21948,c_245])).

cnf(c_30306,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,k8_relat_1(X2_35,sK1)))) ),
    inference(light_normalisation,[status(thm)],[c_30305,c_245,c_1566,c_22046])).

cnf(c_30470,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))),k8_relat_1(X0_35,k8_relat_1(X2_35,sK1))) ),
    inference(superposition,[status(thm)],[c_29679,c_30306])).

cnf(c_30782,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),sK1))))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
    inference(demodulation,[status(thm)],[c_30470,c_245,c_1566,c_7436,c_17253])).

cnf(c_30783,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
    inference(light_normalisation,[status(thm)],[c_30782,c_245])).

cnf(c_32651,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),sK1)))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))))) ),
    inference(superposition,[status(thm)],[c_632,c_30783])).

cnf(c_32653,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,sK1))))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(k2_relat_1(k8_relat_1(X1_35,sK1)),sK1)))) ),
    inference(superposition,[status(thm)],[c_1566,c_30783])).

cnf(c_32698,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))) ),
    inference(superposition,[status(thm)],[c_30783,c_6709])).

cnf(c_32827,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(k8_relat_1(X2_35,sK1)),sK1)))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))) ),
    inference(demodulation,[status(thm)],[c_32653,c_30783,c_32698])).

cnf(c_32829,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))) ),
    inference(demodulation,[status(thm)],[c_32827,c_495])).

cnf(c_32852,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),sK1)))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))) ),
    inference(demodulation,[status(thm)],[c_32651,c_32829])).

cnf(c_32854,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))) ),
    inference(demodulation,[status(thm)],[c_32852,c_2772])).

cnf(c_32855,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))) ),
    inference(light_normalisation,[status(thm)],[c_32854,c_245])).

cnf(c_34978,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),sK1))))) ),
    inference(superposition,[status(thm)],[c_32855,c_8027])).

cnf(c_35013,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
    inference(light_normalisation,[status(thm)],[c_34978,c_245])).

cnf(c_36553,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X0_35,sK1))) ),
    inference(superposition,[status(thm)],[c_245,c_35013])).

cnf(c_2034,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X0_35,sK1))) = k8_relat_1(X0_35,sK1) ),
    inference(superposition,[status(thm)],[c_2018,c_482])).

cnf(c_37738,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),sK1) = k8_relat_1(X0_35,sK1) ),
    inference(light_normalisation,[status(thm)],[c_36553,c_245,c_2034])).

cnf(c_38326,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) = k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1) ),
    inference(superposition,[status(thm)],[c_367,c_37738])).

cnf(c_38704,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) = k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_38326,c_367,c_7446])).

cnf(c_38332,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),sK1) ),
    inference(superposition,[status(thm)],[c_7446,c_37738])).

cnf(c_38691,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_38332,c_4714,c_7446])).

cnf(c_38705,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)) ),
    inference(demodulation,[status(thm)],[c_38704,c_38691])).

cnf(c_38378,plain,
    ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1))),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,sK1)),k8_relat_1(X0_35,sK1)) ),
    inference(superposition,[status(thm)],[c_37738,c_2018])).

cnf(c_38584,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))) ),
    inference(demodulation,[status(thm)],[c_38378,c_37738])).

cnf(c_38709,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1)) = k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)) ),
    inference(demodulation,[status(thm)],[c_38705,c_38584])).

cnf(c_38724,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1)) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_38709])).

cnf(c_74,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_269,plain,
    ( k8_relat_1(X0_35,X0_34) != X1_34
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != X1_34
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,X0_34) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_321,plain,
    ( k8_relat_1(X0_35,X0_34) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,X0_34)
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_777,plain,
    ( k8_relat_1(X0_35,k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_999,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_222,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != X0_34
    | k8_relat_1(sK0,sK1) != X0_34
    | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_233,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(X0_35,X0_34)
    | k8_relat_1(sK0,sK1) != k8_relat_1(X0_35,X0_34)
    | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_337,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(X0_35,k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,sK1) != k8_relat_1(X0_35,k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_439,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,sK1) != k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_76,plain,
    ( X0_35 != X1_35
    | X0_34 != X1_34
    | k8_relat_1(X0_35,X0_34) = k8_relat_1(X1_35,X1_34) ),
    theory(equality)).

cnf(c_270,plain,
    ( sK0 != X0_35
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,X0_34)
    | k8_relat_1(sK0,sK1) != X0_34 ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_297,plain,
    ( sK0 != X0_35
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_298,plain,
    ( sK0 != sK0
    | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_232,plain,
    ( X0_34 != X1_34
    | k8_relat_1(sK0,sK1) != X1_34
    | k8_relat_1(sK0,sK1) = X0_34 ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_266,plain,
    ( X0_34 != k8_relat_1(sK0,sK1)
    | k8_relat_1(sK0,sK1) = X0_34
    | k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_282,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,sK1)
    | k8_relat_1(sK0,sK1) = k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1))
    | k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_254,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1)) = k8_relat_1(sK0,sK1)
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_4,negated_conjecture,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_66,negated_conjecture,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_73,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_86,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_72,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_85,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_80,plain,
    ( sK0 != sK0
    | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38724,c_999,c_439,c_298,c_282,c_254,c_66,c_86,c_85,c_80,c_6])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:28:03 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 14.75/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.75/2.51  
% 14.75/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.75/2.51  
% 14.75/2.51  ------  iProver source info
% 14.75/2.51  
% 14.75/2.51  git: date: 2020-06-30 10:37:57 +0100
% 14.75/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.75/2.51  git: non_committed_changes: false
% 14.75/2.51  git: last_make_outside_of_git: false
% 14.75/2.51  
% 14.75/2.51  ------ 
% 14.75/2.51  
% 14.75/2.51  ------ Input Options
% 14.75/2.51  
% 14.75/2.51  --out_options                           all
% 14.75/2.51  --tptp_safe_out                         true
% 14.75/2.51  --problem_path                          ""
% 14.75/2.51  --include_path                          ""
% 14.75/2.51  --clausifier                            res/vclausify_rel
% 14.75/2.51  --clausifier_options                    --mode clausify
% 14.75/2.51  --stdin                                 false
% 14.75/2.51  --stats_out                             all
% 14.75/2.51  
% 14.75/2.51  ------ General Options
% 14.75/2.51  
% 14.75/2.51  --fof                                   false
% 14.75/2.51  --time_out_real                         305.
% 14.75/2.51  --time_out_virtual                      -1.
% 14.75/2.51  --symbol_type_check                     false
% 14.75/2.51  --clausify_out                          false
% 14.75/2.51  --sig_cnt_out                           false
% 14.75/2.51  --trig_cnt_out                          false
% 14.75/2.51  --trig_cnt_out_tolerance                1.
% 14.75/2.51  --trig_cnt_out_sk_spl                   false
% 14.75/2.51  --abstr_cl_out                          false
% 14.75/2.51  
% 14.75/2.51  ------ Global Options
% 14.75/2.51  
% 14.75/2.51  --schedule                              default
% 14.75/2.51  --add_important_lit                     false
% 14.75/2.51  --prop_solver_per_cl                    1000
% 14.75/2.51  --min_unsat_core                        false
% 14.75/2.51  --soft_assumptions                      false
% 14.75/2.51  --soft_lemma_size                       3
% 14.75/2.51  --prop_impl_unit_size                   0
% 14.75/2.51  --prop_impl_unit                        []
% 14.75/2.51  --share_sel_clauses                     true
% 14.75/2.51  --reset_solvers                         false
% 14.75/2.51  --bc_imp_inh                            [conj_cone]
% 14.75/2.51  --conj_cone_tolerance                   3.
% 14.75/2.51  --extra_neg_conj                        none
% 14.75/2.51  --large_theory_mode                     true
% 14.75/2.51  --prolific_symb_bound                   200
% 14.75/2.51  --lt_threshold                          2000
% 14.75/2.51  --clause_weak_htbl                      true
% 14.75/2.51  --gc_record_bc_elim                     false
% 14.75/2.51  
% 14.75/2.51  ------ Preprocessing Options
% 14.75/2.51  
% 14.75/2.51  --preprocessing_flag                    true
% 14.75/2.51  --time_out_prep_mult                    0.1
% 14.75/2.51  --splitting_mode                        input
% 14.75/2.51  --splitting_grd                         true
% 14.75/2.51  --splitting_cvd                         false
% 14.75/2.51  --splitting_cvd_svl                     false
% 14.75/2.51  --splitting_nvd                         32
% 14.75/2.51  --sub_typing                            true
% 14.75/2.51  --prep_gs_sim                           true
% 14.75/2.51  --prep_unflatten                        true
% 14.75/2.51  --prep_res_sim                          true
% 14.75/2.51  --prep_upred                            true
% 14.75/2.51  --prep_sem_filter                       exhaustive
% 14.75/2.51  --prep_sem_filter_out                   false
% 14.75/2.51  --pred_elim                             true
% 14.75/2.51  --res_sim_input                         true
% 14.75/2.51  --eq_ax_congr_red                       true
% 14.75/2.51  --pure_diseq_elim                       true
% 14.75/2.51  --brand_transform                       false
% 14.75/2.51  --non_eq_to_eq                          false
% 14.75/2.51  --prep_def_merge                        true
% 14.75/2.51  --prep_def_merge_prop_impl              false
% 14.75/2.51  --prep_def_merge_mbd                    true
% 14.75/2.51  --prep_def_merge_tr_red                 false
% 14.75/2.51  --prep_def_merge_tr_cl                  false
% 14.75/2.51  --smt_preprocessing                     true
% 14.75/2.51  --smt_ac_axioms                         fast
% 14.75/2.51  --preprocessed_out                      false
% 14.75/2.51  --preprocessed_stats                    false
% 14.75/2.51  
% 14.75/2.51  ------ Abstraction refinement Options
% 14.75/2.51  
% 14.75/2.51  --abstr_ref                             []
% 14.75/2.51  --abstr_ref_prep                        false
% 14.75/2.51  --abstr_ref_until_sat                   false
% 14.75/2.51  --abstr_ref_sig_restrict                funpre
% 14.75/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 14.75/2.51  --abstr_ref_under                       []
% 14.75/2.51  
% 14.75/2.51  ------ SAT Options
% 14.75/2.51  
% 14.75/2.51  --sat_mode                              false
% 14.75/2.51  --sat_fm_restart_options                ""
% 14.75/2.51  --sat_gr_def                            false
% 14.75/2.51  --sat_epr_types                         true
% 14.75/2.51  --sat_non_cyclic_types                  false
% 14.75/2.51  --sat_finite_models                     false
% 14.75/2.51  --sat_fm_lemmas                         false
% 14.75/2.51  --sat_fm_prep                           false
% 14.75/2.51  --sat_fm_uc_incr                        true
% 14.75/2.51  --sat_out_model                         small
% 14.75/2.51  --sat_out_clauses                       false
% 14.75/2.51  
% 14.75/2.51  ------ QBF Options
% 14.75/2.51  
% 14.75/2.51  --qbf_mode                              false
% 14.75/2.51  --qbf_elim_univ                         false
% 14.75/2.51  --qbf_dom_inst                          none
% 14.75/2.51  --qbf_dom_pre_inst                      false
% 14.75/2.51  --qbf_sk_in                             false
% 14.75/2.51  --qbf_pred_elim                         true
% 14.75/2.51  --qbf_split                             512
% 14.75/2.51  
% 14.75/2.51  ------ BMC1 Options
% 14.75/2.51  
% 14.75/2.51  --bmc1_incremental                      false
% 14.75/2.51  --bmc1_axioms                           reachable_all
% 14.75/2.51  --bmc1_min_bound                        0
% 14.75/2.51  --bmc1_max_bound                        -1
% 14.75/2.51  --bmc1_max_bound_default                -1
% 14.75/2.51  --bmc1_symbol_reachability              true
% 14.75/2.51  --bmc1_property_lemmas                  false
% 14.75/2.51  --bmc1_k_induction                      false
% 14.75/2.51  --bmc1_non_equiv_states                 false
% 14.75/2.51  --bmc1_deadlock                         false
% 14.75/2.51  --bmc1_ucm                              false
% 14.75/2.51  --bmc1_add_unsat_core                   none
% 14.75/2.51  --bmc1_unsat_core_children              false
% 14.75/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 14.75/2.51  --bmc1_out_stat                         full
% 14.75/2.51  --bmc1_ground_init                      false
% 14.75/2.51  --bmc1_pre_inst_next_state              false
% 14.75/2.51  --bmc1_pre_inst_state                   false
% 14.75/2.51  --bmc1_pre_inst_reach_state             false
% 14.75/2.51  --bmc1_out_unsat_core                   false
% 14.75/2.51  --bmc1_aig_witness_out                  false
% 14.75/2.51  --bmc1_verbose                          false
% 14.75/2.51  --bmc1_dump_clauses_tptp                false
% 14.75/2.51  --bmc1_dump_unsat_core_tptp             false
% 14.75/2.51  --bmc1_dump_file                        -
% 14.75/2.51  --bmc1_ucm_expand_uc_limit              128
% 14.75/2.51  --bmc1_ucm_n_expand_iterations          6
% 14.75/2.51  --bmc1_ucm_extend_mode                  1
% 14.75/2.51  --bmc1_ucm_init_mode                    2
% 14.75/2.51  --bmc1_ucm_cone_mode                    none
% 14.75/2.51  --bmc1_ucm_reduced_relation_type        0
% 14.75/2.51  --bmc1_ucm_relax_model                  4
% 14.75/2.51  --bmc1_ucm_full_tr_after_sat            true
% 14.75/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 14.75/2.51  --bmc1_ucm_layered_model                none
% 14.75/2.51  --bmc1_ucm_max_lemma_size               10
% 14.75/2.51  
% 14.75/2.51  ------ AIG Options
% 14.75/2.51  
% 14.75/2.51  --aig_mode                              false
% 14.75/2.51  
% 14.75/2.51  ------ Instantiation Options
% 14.75/2.51  
% 14.75/2.51  --instantiation_flag                    true
% 14.75/2.51  --inst_sos_flag                         false
% 14.75/2.51  --inst_sos_phase                        true
% 14.75/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.75/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.75/2.51  --inst_lit_sel_side                     num_symb
% 14.75/2.51  --inst_solver_per_active                1400
% 14.75/2.51  --inst_solver_calls_frac                1.
% 14.75/2.51  --inst_passive_queue_type               priority_queues
% 14.75/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.75/2.51  --inst_passive_queues_freq              [25;2]
% 14.75/2.51  --inst_dismatching                      true
% 14.75/2.51  --inst_eager_unprocessed_to_passive     true
% 14.75/2.51  --inst_prop_sim_given                   true
% 14.75/2.51  --inst_prop_sim_new                     false
% 14.75/2.51  --inst_subs_new                         false
% 14.75/2.51  --inst_eq_res_simp                      false
% 14.75/2.51  --inst_subs_given                       false
% 14.75/2.51  --inst_orphan_elimination               true
% 14.75/2.51  --inst_learning_loop_flag               true
% 14.75/2.51  --inst_learning_start                   3000
% 14.75/2.51  --inst_learning_factor                  2
% 14.75/2.51  --inst_start_prop_sim_after_learn       3
% 14.75/2.51  --inst_sel_renew                        solver
% 14.75/2.51  --inst_lit_activity_flag                true
% 14.75/2.51  --inst_restr_to_given                   false
% 14.75/2.51  --inst_activity_threshold               500
% 14.75/2.51  --inst_out_proof                        true
% 14.75/2.51  
% 14.75/2.51  ------ Resolution Options
% 14.75/2.51  
% 14.75/2.51  --resolution_flag                       true
% 14.75/2.51  --res_lit_sel                           adaptive
% 14.75/2.51  --res_lit_sel_side                      none
% 14.75/2.51  --res_ordering                          kbo
% 14.75/2.51  --res_to_prop_solver                    active
% 14.75/2.51  --res_prop_simpl_new                    false
% 14.75/2.51  --res_prop_simpl_given                  true
% 14.75/2.51  --res_passive_queue_type                priority_queues
% 14.75/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.75/2.51  --res_passive_queues_freq               [15;5]
% 14.75/2.51  --res_forward_subs                      full
% 14.75/2.51  --res_backward_subs                     full
% 14.75/2.51  --res_forward_subs_resolution           true
% 14.75/2.51  --res_backward_subs_resolution          true
% 14.75/2.51  --res_orphan_elimination                true
% 14.75/2.51  --res_time_limit                        2.
% 14.75/2.51  --res_out_proof                         true
% 14.75/2.51  
% 14.75/2.51  ------ Superposition Options
% 14.75/2.51  
% 14.75/2.51  --superposition_flag                    true
% 14.75/2.51  --sup_passive_queue_type                priority_queues
% 14.75/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.75/2.51  --sup_passive_queues_freq               [8;1;4]
% 14.75/2.51  --demod_completeness_check              fast
% 14.75/2.51  --demod_use_ground                      true
% 14.75/2.51  --sup_to_prop_solver                    passive
% 14.75/2.51  --sup_prop_simpl_new                    true
% 14.75/2.51  --sup_prop_simpl_given                  true
% 14.75/2.51  --sup_fun_splitting                     false
% 14.75/2.51  --sup_smt_interval                      50000
% 14.75/2.51  
% 14.75/2.51  ------ Superposition Simplification Setup
% 14.75/2.51  
% 14.75/2.51  --sup_indices_passive                   []
% 14.75/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.75/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.75/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.75/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 14.75/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.75/2.51  --sup_full_bw                           [BwDemod]
% 14.75/2.51  --sup_immed_triv                        [TrivRules]
% 14.75/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.75/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.75/2.51  --sup_immed_bw_main                     []
% 14.75/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.75/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 14.75/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.75/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.75/2.51  
% 14.75/2.51  ------ Combination Options
% 14.75/2.51  
% 14.75/2.51  --comb_res_mult                         3
% 14.75/2.51  --comb_sup_mult                         2
% 14.75/2.51  --comb_inst_mult                        10
% 14.75/2.51  
% 14.75/2.51  ------ Debug Options
% 14.75/2.51  
% 14.75/2.51  --dbg_backtrace                         false
% 14.75/2.51  --dbg_dump_prop_clauses                 false
% 14.75/2.51  --dbg_dump_prop_clauses_file            -
% 14.75/2.51  --dbg_out_stat                          false
% 14.75/2.51  ------ Parsing...
% 14.75/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.75/2.51  
% 14.75/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 14.75/2.51  
% 14.75/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.75/2.51  
% 14.75/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.75/2.51  ------ Proving...
% 14.75/2.51  ------ Problem Properties 
% 14.75/2.51  
% 14.75/2.51  
% 14.75/2.51  clauses                                 6
% 14.75/2.51  conjectures                             2
% 14.75/2.51  EPR                                     1
% 14.75/2.51  Horn                                    6
% 14.75/2.51  unary                                   2
% 14.75/2.51  binary                                  4
% 14.75/2.51  lits                                    10
% 14.75/2.51  lits eq                                 4
% 14.75/2.51  fd_pure                                 0
% 14.75/2.51  fd_pseudo                               0
% 14.75/2.51  fd_cond                                 0
% 14.75/2.51  fd_pseudo_cond                          0
% 14.75/2.51  AC symbols                              0
% 14.75/2.51  
% 14.75/2.51  ------ Schedule dynamic 5 is on 
% 14.75/2.51  
% 14.75/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 14.75/2.51  
% 14.75/2.51  
% 14.75/2.51  ------ 
% 14.75/2.51  Current options:
% 14.75/2.51  ------ 
% 14.75/2.51  
% 14.75/2.51  ------ Input Options
% 14.75/2.51  
% 14.75/2.51  --out_options                           all
% 14.75/2.51  --tptp_safe_out                         true
% 14.75/2.51  --problem_path                          ""
% 14.75/2.51  --include_path                          ""
% 14.75/2.51  --clausifier                            res/vclausify_rel
% 14.75/2.51  --clausifier_options                    --mode clausify
% 14.75/2.51  --stdin                                 false
% 14.75/2.51  --stats_out                             all
% 14.75/2.51  
% 14.75/2.51  ------ General Options
% 14.75/2.51  
% 14.75/2.51  --fof                                   false
% 14.75/2.51  --time_out_real                         305.
% 14.75/2.51  --time_out_virtual                      -1.
% 14.75/2.51  --symbol_type_check                     false
% 14.75/2.51  --clausify_out                          false
% 14.75/2.51  --sig_cnt_out                           false
% 14.75/2.51  --trig_cnt_out                          false
% 14.75/2.51  --trig_cnt_out_tolerance                1.
% 14.75/2.51  --trig_cnt_out_sk_spl                   false
% 14.75/2.51  --abstr_cl_out                          false
% 14.75/2.51  
% 14.75/2.51  ------ Global Options
% 14.75/2.51  
% 14.75/2.51  --schedule                              default
% 14.75/2.51  --add_important_lit                     false
% 14.75/2.51  --prop_solver_per_cl                    1000
% 14.75/2.51  --min_unsat_core                        false
% 14.75/2.51  --soft_assumptions                      false
% 14.75/2.51  --soft_lemma_size                       3
% 14.75/2.51  --prop_impl_unit_size                   0
% 14.75/2.51  --prop_impl_unit                        []
% 14.75/2.51  --share_sel_clauses                     true
% 14.75/2.51  --reset_solvers                         false
% 14.75/2.51  --bc_imp_inh                            [conj_cone]
% 14.75/2.51  --conj_cone_tolerance                   3.
% 14.75/2.51  --extra_neg_conj                        none
% 14.75/2.51  --large_theory_mode                     true
% 14.75/2.51  --prolific_symb_bound                   200
% 14.75/2.51  --lt_threshold                          2000
% 14.75/2.51  --clause_weak_htbl                      true
% 14.75/2.51  --gc_record_bc_elim                     false
% 14.75/2.51  
% 14.75/2.51  ------ Preprocessing Options
% 14.75/2.51  
% 14.75/2.51  --preprocessing_flag                    true
% 14.75/2.51  --time_out_prep_mult                    0.1
% 14.75/2.51  --splitting_mode                        input
% 14.75/2.51  --splitting_grd                         true
% 14.75/2.51  --splitting_cvd                         false
% 14.75/2.51  --splitting_cvd_svl                     false
% 14.75/2.51  --splitting_nvd                         32
% 14.75/2.51  --sub_typing                            true
% 14.75/2.51  --prep_gs_sim                           true
% 14.75/2.51  --prep_unflatten                        true
% 14.75/2.51  --prep_res_sim                          true
% 14.75/2.51  --prep_upred                            true
% 14.75/2.51  --prep_sem_filter                       exhaustive
% 14.75/2.51  --prep_sem_filter_out                   false
% 14.75/2.51  --pred_elim                             true
% 14.75/2.51  --res_sim_input                         true
% 14.75/2.51  --eq_ax_congr_red                       true
% 14.75/2.51  --pure_diseq_elim                       true
% 14.75/2.51  --brand_transform                       false
% 14.75/2.51  --non_eq_to_eq                          false
% 14.75/2.51  --prep_def_merge                        true
% 14.75/2.51  --prep_def_merge_prop_impl              false
% 14.75/2.51  --prep_def_merge_mbd                    true
% 14.75/2.51  --prep_def_merge_tr_red                 false
% 14.75/2.51  --prep_def_merge_tr_cl                  false
% 14.75/2.51  --smt_preprocessing                     true
% 14.75/2.51  --smt_ac_axioms                         fast
% 14.75/2.51  --preprocessed_out                      false
% 14.75/2.51  --preprocessed_stats                    false
% 14.75/2.51  
% 14.75/2.51  ------ Abstraction refinement Options
% 14.75/2.51  
% 14.75/2.51  --abstr_ref                             []
% 14.75/2.51  --abstr_ref_prep                        false
% 14.75/2.51  --abstr_ref_until_sat                   false
% 14.75/2.51  --abstr_ref_sig_restrict                funpre
% 14.75/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 14.75/2.51  --abstr_ref_under                       []
% 14.75/2.51  
% 14.75/2.51  ------ SAT Options
% 14.75/2.51  
% 14.75/2.51  --sat_mode                              false
% 14.75/2.51  --sat_fm_restart_options                ""
% 14.75/2.51  --sat_gr_def                            false
% 14.75/2.51  --sat_epr_types                         true
% 14.75/2.51  --sat_non_cyclic_types                  false
% 14.75/2.51  --sat_finite_models                     false
% 14.75/2.51  --sat_fm_lemmas                         false
% 14.75/2.51  --sat_fm_prep                           false
% 14.75/2.51  --sat_fm_uc_incr                        true
% 14.75/2.51  --sat_out_model                         small
% 14.75/2.51  --sat_out_clauses                       false
% 14.75/2.51  
% 14.75/2.51  ------ QBF Options
% 14.75/2.51  
% 14.75/2.51  --qbf_mode                              false
% 14.75/2.51  --qbf_elim_univ                         false
% 14.75/2.51  --qbf_dom_inst                          none
% 14.75/2.51  --qbf_dom_pre_inst                      false
% 14.75/2.51  --qbf_sk_in                             false
% 14.75/2.51  --qbf_pred_elim                         true
% 14.75/2.51  --qbf_split                             512
% 14.75/2.51  
% 14.75/2.51  ------ BMC1 Options
% 14.75/2.51  
% 14.75/2.51  --bmc1_incremental                      false
% 14.75/2.51  --bmc1_axioms                           reachable_all
% 14.75/2.51  --bmc1_min_bound                        0
% 14.75/2.51  --bmc1_max_bound                        -1
% 14.75/2.51  --bmc1_max_bound_default                -1
% 14.75/2.51  --bmc1_symbol_reachability              true
% 14.75/2.51  --bmc1_property_lemmas                  false
% 14.75/2.51  --bmc1_k_induction                      false
% 14.75/2.51  --bmc1_non_equiv_states                 false
% 14.75/2.51  --bmc1_deadlock                         false
% 14.75/2.51  --bmc1_ucm                              false
% 14.75/2.51  --bmc1_add_unsat_core                   none
% 14.75/2.51  --bmc1_unsat_core_children              false
% 14.75/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 14.75/2.51  --bmc1_out_stat                         full
% 14.75/2.51  --bmc1_ground_init                      false
% 14.75/2.51  --bmc1_pre_inst_next_state              false
% 14.75/2.51  --bmc1_pre_inst_state                   false
% 14.75/2.51  --bmc1_pre_inst_reach_state             false
% 14.75/2.51  --bmc1_out_unsat_core                   false
% 14.75/2.51  --bmc1_aig_witness_out                  false
% 14.75/2.51  --bmc1_verbose                          false
% 14.75/2.51  --bmc1_dump_clauses_tptp                false
% 14.75/2.51  --bmc1_dump_unsat_core_tptp             false
% 14.75/2.51  --bmc1_dump_file                        -
% 14.75/2.51  --bmc1_ucm_expand_uc_limit              128
% 14.75/2.51  --bmc1_ucm_n_expand_iterations          6
% 14.75/2.51  --bmc1_ucm_extend_mode                  1
% 14.75/2.51  --bmc1_ucm_init_mode                    2
% 14.75/2.51  --bmc1_ucm_cone_mode                    none
% 14.75/2.51  --bmc1_ucm_reduced_relation_type        0
% 14.75/2.51  --bmc1_ucm_relax_model                  4
% 14.75/2.51  --bmc1_ucm_full_tr_after_sat            true
% 14.75/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 14.75/2.51  --bmc1_ucm_layered_model                none
% 14.75/2.51  --bmc1_ucm_max_lemma_size               10
% 14.75/2.51  
% 14.75/2.51  ------ AIG Options
% 14.75/2.51  
% 14.75/2.51  --aig_mode                              false
% 14.75/2.51  
% 14.75/2.51  ------ Instantiation Options
% 14.75/2.51  
% 14.75/2.51  --instantiation_flag                    true
% 14.75/2.51  --inst_sos_flag                         false
% 14.75/2.51  --inst_sos_phase                        true
% 14.75/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.75/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.75/2.51  --inst_lit_sel_side                     none
% 14.75/2.51  --inst_solver_per_active                1400
% 14.75/2.51  --inst_solver_calls_frac                1.
% 14.75/2.51  --inst_passive_queue_type               priority_queues
% 14.75/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.75/2.51  --inst_passive_queues_freq              [25;2]
% 14.75/2.51  --inst_dismatching                      true
% 14.75/2.51  --inst_eager_unprocessed_to_passive     true
% 14.75/2.51  --inst_prop_sim_given                   true
% 14.75/2.51  --inst_prop_sim_new                     false
% 14.75/2.51  --inst_subs_new                         false
% 14.75/2.51  --inst_eq_res_simp                      false
% 14.75/2.51  --inst_subs_given                       false
% 14.75/2.51  --inst_orphan_elimination               true
% 14.75/2.51  --inst_learning_loop_flag               true
% 14.75/2.51  --inst_learning_start                   3000
% 14.75/2.51  --inst_learning_factor                  2
% 14.75/2.51  --inst_start_prop_sim_after_learn       3
% 14.75/2.51  --inst_sel_renew                        solver
% 14.75/2.51  --inst_lit_activity_flag                true
% 14.75/2.51  --inst_restr_to_given                   false
% 14.75/2.51  --inst_activity_threshold               500
% 14.75/2.51  --inst_out_proof                        true
% 14.75/2.51  
% 14.75/2.51  ------ Resolution Options
% 14.75/2.51  
% 14.75/2.51  --resolution_flag                       false
% 14.75/2.51  --res_lit_sel                           adaptive
% 14.75/2.51  --res_lit_sel_side                      none
% 14.75/2.51  --res_ordering                          kbo
% 14.75/2.51  --res_to_prop_solver                    active
% 14.75/2.51  --res_prop_simpl_new                    false
% 14.75/2.51  --res_prop_simpl_given                  true
% 14.75/2.51  --res_passive_queue_type                priority_queues
% 14.75/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.75/2.51  --res_passive_queues_freq               [15;5]
% 14.75/2.51  --res_forward_subs                      full
% 14.75/2.51  --res_backward_subs                     full
% 14.75/2.51  --res_forward_subs_resolution           true
% 14.75/2.51  --res_backward_subs_resolution          true
% 14.75/2.51  --res_orphan_elimination                true
% 14.75/2.51  --res_time_limit                        2.
% 14.75/2.51  --res_out_proof                         true
% 14.75/2.51  
% 14.75/2.51  ------ Superposition Options
% 14.75/2.51  
% 14.75/2.51  --superposition_flag                    true
% 14.75/2.51  --sup_passive_queue_type                priority_queues
% 14.75/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.75/2.51  --sup_passive_queues_freq               [8;1;4]
% 14.75/2.51  --demod_completeness_check              fast
% 14.75/2.51  --demod_use_ground                      true
% 14.75/2.51  --sup_to_prop_solver                    passive
% 14.75/2.51  --sup_prop_simpl_new                    true
% 14.75/2.51  --sup_prop_simpl_given                  true
% 14.75/2.51  --sup_fun_splitting                     false
% 14.75/2.51  --sup_smt_interval                      50000
% 14.75/2.51  
% 14.75/2.51  ------ Superposition Simplification Setup
% 14.75/2.51  
% 14.75/2.51  --sup_indices_passive                   []
% 14.75/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.75/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.75/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.75/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 14.75/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.75/2.51  --sup_full_bw                           [BwDemod]
% 14.75/2.51  --sup_immed_triv                        [TrivRules]
% 14.75/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.75/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.75/2.51  --sup_immed_bw_main                     []
% 14.75/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.75/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 14.75/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.75/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.75/2.51  
% 14.75/2.51  ------ Combination Options
% 14.75/2.51  
% 14.75/2.51  --comb_res_mult                         3
% 14.75/2.51  --comb_sup_mult                         2
% 14.75/2.51  --comb_inst_mult                        10
% 14.75/2.51  
% 14.75/2.51  ------ Debug Options
% 14.75/2.51  
% 14.75/2.51  --dbg_backtrace                         false
% 14.75/2.51  --dbg_dump_prop_clauses                 false
% 14.75/2.51  --dbg_dump_prop_clauses_file            -
% 14.75/2.51  --dbg_out_stat                          false
% 14.75/2.51  
% 14.75/2.51  
% 14.75/2.51  
% 14.75/2.51  
% 14.75/2.51  ------ Proving...
% 14.75/2.51  
% 14.75/2.51  
% 14.75/2.51  % SZS status Theorem for theBenchmark.p
% 14.75/2.51  
% 14.75/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 14.75/2.51  
% 14.75/2.51  fof(f5,conjecture,(
% 14.75/2.51    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 14.75/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.75/2.51  
% 14.75/2.51  fof(f6,negated_conjecture,(
% 14.75/2.51    ~! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 14.75/2.51    inference(negated_conjecture,[],[f5])).
% 14.75/2.51  
% 14.75/2.51  fof(f11,plain,(
% 14.75/2.51    ? [X0,X1] : (k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1)) & v1_relat_1(X1))),
% 14.75/2.51    inference(ennf_transformation,[],[f6])).
% 14.75/2.51  
% 14.75/2.51  fof(f12,plain,(
% 14.75/2.51    ? [X0,X1] : (k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1)) & v1_relat_1(X1)) => (k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) & v1_relat_1(sK1))),
% 14.75/2.51    introduced(choice_axiom,[])).
% 14.75/2.51  
% 14.75/2.51  fof(f13,plain,(
% 14.75/2.51    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) & v1_relat_1(sK1)),
% 14.75/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 14.75/2.51  
% 14.75/2.51  fof(f18,plain,(
% 14.75/2.51    v1_relat_1(sK1)),
% 14.75/2.51    inference(cnf_transformation,[],[f13])).
% 14.75/2.51  
% 14.75/2.51  fof(f4,axiom,(
% 14.75/2.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 14.75/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.75/2.51  
% 14.75/2.51  fof(f10,plain,(
% 14.75/2.51    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 14.75/2.51    inference(ennf_transformation,[],[f4])).
% 14.75/2.51  
% 14.75/2.51  fof(f17,plain,(
% 14.75/2.51    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 14.75/2.51    inference(cnf_transformation,[],[f10])).
% 14.75/2.51  
% 14.75/2.51  fof(f3,axiom,(
% 14.75/2.51    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 14.75/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.75/2.51  
% 14.75/2.51  fof(f9,plain,(
% 14.75/2.51    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 14.75/2.51    inference(ennf_transformation,[],[f3])).
% 14.75/2.51  
% 14.75/2.51  fof(f16,plain,(
% 14.75/2.51    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 14.75/2.51    inference(cnf_transformation,[],[f9])).
% 14.75/2.51  
% 14.75/2.51  fof(f1,axiom,(
% 14.75/2.51    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 14.75/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.75/2.51  
% 14.75/2.51  fof(f7,plain,(
% 14.75/2.51    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 14.75/2.52    inference(ennf_transformation,[],[f1])).
% 14.75/2.52  
% 14.75/2.52  fof(f14,plain,(
% 14.75/2.52    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 14.75/2.52    inference(cnf_transformation,[],[f7])).
% 14.75/2.52  
% 14.75/2.52  fof(f2,axiom,(
% 14.75/2.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 14.75/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.75/2.52  
% 14.75/2.52  fof(f8,plain,(
% 14.75/2.52    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 14.75/2.52    inference(ennf_transformation,[],[f2])).
% 14.75/2.52  
% 14.75/2.52  fof(f15,plain,(
% 14.75/2.52    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 14.75/2.52    inference(cnf_transformation,[],[f8])).
% 14.75/2.52  
% 14.75/2.52  fof(f19,plain,(
% 14.75/2.52    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))),
% 14.75/2.52    inference(cnf_transformation,[],[f13])).
% 14.75/2.52  
% 14.75/2.52  cnf(c_5,negated_conjecture,
% 14.75/2.52      ( v1_relat_1(sK1) ),
% 14.75/2.52      inference(cnf_transformation,[],[f18]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_65,negated_conjecture,
% 14.75/2.52      ( v1_relat_1(sK1) ),
% 14.75/2.52      inference(subtyping,[status(esa)],[c_5]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_190,plain,
% 14.75/2.52      ( v1_relat_1(sK1) = iProver_top ),
% 14.75/2.52      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_3,plain,
% 14.75/2.52      ( ~ v1_relat_1(X0)
% 14.75/2.52      | k8_relat_1(k3_xboole_0(X1,X2),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
% 14.75/2.52      inference(cnf_transformation,[],[f17]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_67,plain,
% 14.75/2.52      ( ~ v1_relat_1(X0_34)
% 14.75/2.52      | k8_relat_1(k3_xboole_0(X0_35,X1_35),X0_34) = k8_relat_1(X0_35,k8_relat_1(X1_35,X0_34)) ),
% 14.75/2.52      inference(subtyping,[status(esa)],[c_3]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_189,plain,
% 14.75/2.52      ( k8_relat_1(k3_xboole_0(X0_35,X1_35),X0_34) = k8_relat_1(X0_35,k8_relat_1(X1_35,X0_34))
% 14.75/2.52      | v1_relat_1(X0_34) != iProver_top ),
% 14.75/2.52      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_367,plain,
% 14.75/2.52      ( k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)) = k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_190,c_189]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2,plain,
% 14.75/2.52      ( ~ v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
% 14.75/2.52      inference(cnf_transformation,[],[f16]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_68,plain,
% 14.75/2.52      ( ~ v1_relat_1(X0_34)
% 14.75/2.52      | k8_relat_1(k2_relat_1(X0_34),X0_34) = X0_34 ),
% 14.75/2.52      inference(subtyping,[status(esa)],[c_2]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_188,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(X0_34),X0_34) = X0_34
% 14.75/2.52      | v1_relat_1(X0_34) != iProver_top ),
% 14.75/2.52      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_245,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),sK1) = sK1 ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_190,c_188]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_0,plain,
% 14.75/2.52      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 14.75/2.52      inference(cnf_transformation,[],[f14]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_70,plain,
% 14.75/2.52      ( ~ v1_relat_1(X0_34) | v1_relat_1(k8_relat_1(X0_35,X0_34)) ),
% 14.75/2.52      inference(subtyping,[status(esa)],[c_0]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_186,plain,
% 14.75/2.52      ( v1_relat_1(X0_34) != iProver_top
% 14.75/2.52      | v1_relat_1(k8_relat_1(X0_35,X0_34)) = iProver_top ),
% 14.75/2.52      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_246,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,X0_34)),k8_relat_1(X0_35,X0_34)) = k8_relat_1(X0_35,X0_34)
% 14.75/2.52      | v1_relat_1(X0_34) != iProver_top ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_186,c_188]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_482,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X0_35,sK1)) = k8_relat_1(X0_35,sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_190,c_246]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_628,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_482]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_632,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_628,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_1,plain,
% 14.75/2.52      ( ~ v1_relat_1(X0)
% 14.75/2.52      | k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 14.75/2.52      inference(cnf_transformation,[],[f15]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_69,plain,
% 14.75/2.52      ( ~ v1_relat_1(X0_34)
% 14.75/2.52      | k3_xboole_0(k2_relat_1(X0_34),X0_35) = k2_relat_1(k8_relat_1(X0_35,X0_34)) ),
% 14.75/2.52      inference(subtyping,[status(esa)],[c_1]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_187,plain,
% 14.75/2.52      ( k3_xboole_0(k2_relat_1(X0_34),X0_35) = k2_relat_1(k8_relat_1(X0_35,X0_34))
% 14.75/2.52      | v1_relat_1(X0_34) != iProver_top ),
% 14.75/2.52      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_306,plain,
% 14.75/2.52      ( k3_xboole_0(k2_relat_1(sK1),X0_35) = k2_relat_1(k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_190,c_187]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_496,plain,
% 14.75/2.52      ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = iProver_top
% 14.75/2.52      | v1_relat_1(sK1) != iProver_top ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_186]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_6,plain,
% 14.75/2.52      ( v1_relat_1(sK1) = iProver_top ),
% 14.75/2.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_636,plain,
% 14.75/2.52      ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = iProver_top ),
% 14.75/2.52      inference(global_propositional_subsumption,
% 14.75/2.52                [status(thm)],
% 14.75/2.52                [c_496,c_6]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_647,plain,
% 14.75/2.52      ( k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))) = k8_relat_1(k3_xboole_0(X0_35,X1_35),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_636,c_189]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_1566,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_306,c_647]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_4714,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_1566]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_648,plain,
% 14.75/2.52      ( k3_xboole_0(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),X2_35) = k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_636,c_187]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_746,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_648,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2675,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(k3_xboole_0(X2_35,X3_35),sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_647,c_746]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2790,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_2675,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7225,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X3_35,X4_35),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_647,c_2790]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7426,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_7225,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_14710,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k3_xboole_0(X4_35,X5_35),sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X5_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_647,c_7426]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_15012,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X5_35,sK1))))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X4_35,k8_relat_1(X5_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_14710,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_27621,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),sK1))))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_4714,c_15012]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_28081,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_27621,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_28724,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),sK1))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_28081]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_29109,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_28724,c_245,c_1566]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_29256,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_4714,c_29109]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_29679,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_29256,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_30098,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_29679,c_29109]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7234,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X1_35,X2_35),sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_2790]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7399,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_7234,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7427,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_7426,c_7399]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_744,plain,
% 14.75/2.52      ( k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),sK1)))) = k3_xboole_0(k2_relat_1(k8_relat_1(X1_35,sK1)),X0_35) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_648]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_753,plain,
% 14.75/2.52      ( k3_xboole_0(k2_relat_1(k8_relat_1(X0_35,sK1)),X1_35) = k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_744,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_1081,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_753,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_495,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_306,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_1039,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_495]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_1067,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),sK1) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_1039,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2018,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,sK1)),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_1081,c_1067]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7231,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_2018,c_2790]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7406,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_7231,c_7399]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_643,plain,
% 14.75/2.52      ( v1_relat_1(k8_relat_1(X0_35,sK1)) = iProver_top ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_482,c_636]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_766,plain,
% 14.75/2.52      ( k8_relat_1(k3_xboole_0(X0_35,X1_35),k8_relat_1(X2_35,sK1)) = k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_643,c_189]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_1525,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_306,c_766]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7408,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_7406,c_1525]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7433,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_7427,c_7408]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7436,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))),k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_7433,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_30305,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),sK1))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_30098,c_7436,c_28081]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_4815,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X1_35,X2_35),sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_4714]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_4845,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_4815,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_6677,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k3_xboole_0(X2_35,X3_35),sK1)))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_4845]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_6709,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_6677,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_645,plain,
% 14.75/2.52      ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) = iProver_top ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_636]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_861,plain,
% 14.75/2.52      ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))) = iProver_top ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_645]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_881,plain,
% 14.75/2.52      ( v1_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))) = iProver_top ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_861]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_1192,plain,
% 14.75/2.52      ( k3_xboole_0(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))),X5_35) = k2_relat_1(k8_relat_1(X5_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))))))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_881,c_187]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_6106,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))),k8_relat_1(X5_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X5_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_1192,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_21136,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),k8_relat_1(k2_relat_1(sK1),sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_6709,c_6106]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_21162,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),sK1)))))),k8_relat_1(X4_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_6106]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_10881,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_766,c_7436]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_10885,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k3_xboole_0(X1_35,X2_35),k8_relat_1(X0_35,sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_7436]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11069,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_10885,c_766]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2681,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),sK1))),k8_relat_1(X1_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_746]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2772,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_2681,c_245,c_1525]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_10889,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X0_35,sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_2772,c_7436]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7222,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_4714,c_2790]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7446,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_7222,c_245,c_2772]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_10891,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_7446,c_7436]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_10901,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X2_35,sK1)) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_7436]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11017,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))),k8_relat_1(X2_35,sK1)) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_10901,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2023,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X1_35,X2_35),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_2018]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2072,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_2023,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_5267,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k3_xboole_0(X2_35,X3_35),sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_2072]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_5366,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_5267,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11018,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_11017,c_2072,c_5366]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11045,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_10891,c_11018]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11051,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))),k8_relat_1(X2_35,sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_10889,c_11045]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11053,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X1_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_11051,c_2072]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11070,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_11069,c_11053]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11090,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X2_35,X1_35),sK1))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_10881,c_11070]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_11092,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_11090,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_17044,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,k8_relat_1(k2_relat_1(sK1),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X1_35,sK1)))),k8_relat_1(X3_35,sK1)) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_11092]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_17253,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))),k8_relat_1(X3_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X1_35,sK1))))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_17044,c_245,c_5366]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_17642,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X3_35,X4_35),sK1))))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X2_35,sK1))))),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_766,c_17253]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_9660,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X3_35,X4_35),sK1))))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))))),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_5366]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_9839,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1))))),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_9660,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_17943,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))),k8_relat_1(X4_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X4_35,k8_relat_1(X0_35,k8_relat_1(X3_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_17642,c_367,c_9839]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_21496,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,k8_relat_1(X4_35,sK1)))))) = k8_relat_1(k2_relat_1(k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X3_35,k8_relat_1(X4_35,k8_relat_1(X2_35,sK1)))))),sK1) ),
% 14.75/2.52      inference(light_normalisation,
% 14.75/2.52                [status(thm)],
% 14.75/2.52                [c_21162,c_245,c_17943]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_21570,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),k8_relat_1(k2_relat_1(sK1),sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X3_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1)))))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_21136,c_21496]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7641,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_766,c_7446]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7818,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_7641,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_7852,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(k3_xboole_0(X1_35,X2_35),sK1)))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_766,c_7818]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_8027,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_7852,c_367]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_21572,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,k8_relat_1(X2_35,k8_relat_1(X3_35,sK1))))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_21570,c_245,c_8027]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_21948,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,k8_relat_1(X2_35,sK1))))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_21572]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_22046,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,k8_relat_1(X2_35,sK1)))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_21948,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_30306,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),k8_relat_1(X1_35,k8_relat_1(X2_35,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,k8_relat_1(X2_35,sK1)))) ),
% 14.75/2.52      inference(light_normalisation,
% 14.75/2.52                [status(thm)],
% 14.75/2.52                [c_30305,c_245,c_1566,c_22046]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_30470,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))),k8_relat_1(X2_35,sK1)))) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))),k8_relat_1(X0_35,k8_relat_1(X2_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_29679,c_30306]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_30782,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(k2_relat_1(sK1),sK1))))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(demodulation,
% 14.75/2.52                [status(thm)],
% 14.75/2.52                [c_30470,c_245,c_1566,c_7436,c_17253]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_30783,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_30782,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_32651,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),sK1)))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_632,c_30783]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_32653,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,sK1))))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X0_35,k8_relat_1(k2_relat_1(k8_relat_1(X1_35,sK1)),sK1)))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_1566,c_30783]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_32698,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1)))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_30783,c_6709]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_32827,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(k8_relat_1(X2_35,sK1)),sK1)))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_32653,c_30783,c_32698]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_32829,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X2_35,k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_32827,c_495]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_32852,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),sK1)))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_32651,c_32829]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_32854,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),sK1)))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_32852,c_2772]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_32855,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_32854,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_34978,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X0_35,k8_relat_1(X1_35,k8_relat_1(k2_relat_1(sK1),sK1))))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_32855,c_8027]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_35013,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_34978,c_245]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_36553,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),sK1))))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X0_35,sK1))) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_245,c_35013]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_2034,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X0_35,sK1))) = k8_relat_1(X0_35,sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_2018,c_482]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_37738,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,sK1))),sK1) = k8_relat_1(X0_35,sK1) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_36553,c_245,c_2034]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38326,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) = k8_relat_1(k3_xboole_0(X0_35,X1_35),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_367,c_37738]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38704,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) = k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)) ),
% 14.75/2.52      inference(light_normalisation,[status(thm)],[c_38326,c_367,c_7446]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38332,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))))),sK1) = k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)))),sK1) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_7446,c_37738]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38691,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)))),sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) ),
% 14.75/2.52      inference(light_normalisation,
% 14.75/2.52                [status(thm)],
% 14.75/2.52                [c_38332,c_4714,c_7446]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38705,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(X1_35,sK1))) = k8_relat_1(X0_35,k8_relat_1(X1_35,sK1)) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_38704,c_38691]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38378,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0_35,k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,sK1))),sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1_35,sK1)),k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(superposition,[status(thm)],[c_37738,c_2018]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38584,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1_35,k8_relat_1(X0_35,sK1))) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_38378,c_37738]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38709,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(X0_35,sK1)),k8_relat_1(X1_35,sK1)) = k8_relat_1(X1_35,k8_relat_1(X0_35,sK1)) ),
% 14.75/2.52      inference(demodulation,[status(thm)],[c_38705,c_38584]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_38724,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1)) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_38709]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_74,plain,
% 14.75/2.52      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 14.75/2.52      theory(equality) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_269,plain,
% 14.75/2.52      ( k8_relat_1(X0_35,X0_34) != X1_34
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != X1_34
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,X0_34) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_74]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_321,plain,
% 14.75/2.52      ( k8_relat_1(X0_35,X0_34) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,X0_34)
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_269]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_777,plain,
% 14.75/2.52      ( k8_relat_1(X0_35,k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_321]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_999,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_777]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_222,plain,
% 14.75/2.52      ( k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != X0_34
% 14.75/2.52      | k8_relat_1(sK0,sK1) != X0_34
% 14.75/2.52      | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_74]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_233,plain,
% 14.75/2.52      ( k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(X0_35,X0_34)
% 14.75/2.52      | k8_relat_1(sK0,sK1) != k8_relat_1(X0_35,X0_34)
% 14.75/2.52      | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_222]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_337,plain,
% 14.75/2.52      ( k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(X0_35,k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,sK1) != k8_relat_1(X0_35,k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_233]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_439,plain,
% 14.75/2.52      ( k8_relat_1(sK0,k8_relat_1(sK0,sK1)) != k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,sK1) != k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_337]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_76,plain,
% 14.75/2.52      ( X0_35 != X1_35
% 14.75/2.52      | X0_34 != X1_34
% 14.75/2.52      | k8_relat_1(X0_35,X0_34) = k8_relat_1(X1_35,X1_34) ),
% 14.75/2.52      theory(equality) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_270,plain,
% 14.75/2.52      ( sK0 != X0_35
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,X0_34)
% 14.75/2.52      | k8_relat_1(sK0,sK1) != X0_34 ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_76]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_297,plain,
% 14.75/2.52      ( sK0 != X0_35
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(X0_35,k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_270]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_298,plain,
% 14.75/2.52      ( sK0 != sK0
% 14.75/2.52      | k8_relat_1(sK0,k8_relat_1(sK0,sK1)) = k8_relat_1(sK0,k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_297]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_232,plain,
% 14.75/2.52      ( X0_34 != X1_34
% 14.75/2.52      | k8_relat_1(sK0,sK1) != X1_34
% 14.75/2.52      | k8_relat_1(sK0,sK1) = X0_34 ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_74]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_266,plain,
% 14.75/2.52      ( X0_34 != k8_relat_1(sK0,sK1)
% 14.75/2.52      | k8_relat_1(sK0,sK1) = X0_34
% 14.75/2.52      | k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_232]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_282,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1)) != k8_relat_1(sK0,sK1)
% 14.75/2.52      | k8_relat_1(sK0,sK1) = k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1))
% 14.75/2.52      | k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_266]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_254,plain,
% 14.75/2.52      ( k8_relat_1(k2_relat_1(k8_relat_1(sK0,sK1)),k8_relat_1(sK0,sK1)) = k8_relat_1(sK0,sK1)
% 14.75/2.52      | v1_relat_1(sK1) != iProver_top ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_246]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_4,negated_conjecture,
% 14.75/2.52      ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(cnf_transformation,[],[f19]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_66,negated_conjecture,
% 14.75/2.52      ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
% 14.75/2.52      inference(subtyping,[status(esa)],[c_4]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_73,plain,( X0_35 = X0_35 ),theory(equality) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_86,plain,
% 14.75/2.52      ( sK0 = sK0 ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_73]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_72,plain,( X0_34 = X0_34 ),theory(equality) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_85,plain,
% 14.75/2.52      ( sK1 = sK1 ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_72]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(c_80,plain,
% 14.75/2.52      ( sK0 != sK0
% 14.75/2.52      | k8_relat_1(sK0,sK1) = k8_relat_1(sK0,sK1)
% 14.75/2.52      | sK1 != sK1 ),
% 14.75/2.52      inference(instantiation,[status(thm)],[c_76]) ).
% 14.75/2.52  
% 14.75/2.52  cnf(contradiction,plain,
% 14.75/2.52      ( $false ),
% 14.75/2.52      inference(minisat,
% 14.75/2.52                [status(thm)],
% 14.75/2.52                [c_38724,c_999,c_439,c_298,c_282,c_254,c_66,c_86,c_85,
% 14.75/2.52                 c_80,c_6]) ).
% 14.75/2.52  
% 14.75/2.52  
% 14.75/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 14.75/2.52  
% 14.75/2.52  ------                               Statistics
% 14.75/2.52  
% 14.75/2.52  ------ General
% 14.75/2.52  
% 14.75/2.52  abstr_ref_over_cycles:                  0
% 14.75/2.52  abstr_ref_under_cycles:                 0
% 14.75/2.52  gc_basic_clause_elim:                   0
% 14.75/2.52  forced_gc_time:                         0
% 14.75/2.52  parsing_time:                           0.006
% 14.75/2.52  unif_index_cands_time:                  0.
% 14.75/2.52  unif_index_add_time:                    0.
% 14.75/2.52  orderings_time:                         0.
% 14.75/2.52  out_proof_time:                         0.01
% 14.75/2.52  total_time:                             1.615
% 14.75/2.52  num_of_symbols:                         39
% 14.75/2.52  num_of_terms:                           55925
% 14.75/2.52  
% 14.75/2.52  ------ Preprocessing
% 14.75/2.52  
% 14.75/2.52  num_of_splits:                          0
% 14.75/2.52  num_of_split_atoms:                     0
% 14.75/2.52  num_of_reused_defs:                     0
% 14.75/2.52  num_eq_ax_congr_red:                    2
% 14.75/2.52  num_of_sem_filtered_clauses:            1
% 14.75/2.52  num_of_subtypes:                        2
% 14.75/2.52  monotx_restored_types:                  0
% 14.75/2.52  sat_num_of_epr_types:                   0
% 14.75/2.52  sat_num_of_non_cyclic_types:            0
% 14.75/2.52  sat_guarded_non_collapsed_types:        1
% 14.75/2.52  num_pure_diseq_elim:                    0
% 14.75/2.52  simp_replaced_by:                       0
% 14.75/2.52  res_preprocessed:                       35
% 14.75/2.52  prep_upred:                             0
% 14.75/2.52  prep_unflattend:                        0
% 14.75/2.52  smt_new_axioms:                         0
% 14.75/2.52  pred_elim_cands:                        1
% 14.75/2.52  pred_elim:                              0
% 14.75/2.52  pred_elim_cl:                           0
% 14.75/2.52  pred_elim_cycles:                       1
% 14.75/2.52  merged_defs:                            0
% 14.75/2.52  merged_defs_ncl:                        0
% 14.75/2.52  bin_hyper_res:                          0
% 14.75/2.52  prep_cycles:                            3
% 14.75/2.52  pred_elim_time:                         0.
% 14.75/2.52  splitting_time:                         0.
% 14.75/2.52  sem_filter_time:                        0.
% 14.75/2.52  monotx_time:                            0.
% 14.75/2.52  subtype_inf_time:                       0.
% 14.75/2.52  
% 14.75/2.52  ------ Problem properties
% 14.75/2.52  
% 14.75/2.52  clauses:                                6
% 14.75/2.52  conjectures:                            2
% 14.75/2.52  epr:                                    1
% 14.75/2.52  horn:                                   6
% 14.75/2.52  ground:                                 2
% 14.75/2.52  unary:                                  2
% 14.75/2.52  binary:                                 4
% 14.75/2.52  lits:                                   10
% 14.75/2.52  lits_eq:                                4
% 14.75/2.52  fd_pure:                                0
% 14.75/2.52  fd_pseudo:                              0
% 14.75/2.52  fd_cond:                                0
% 14.75/2.52  fd_pseudo_cond:                         0
% 14.75/2.52  ac_symbols:                             0
% 14.75/2.52  
% 14.75/2.52  ------ Propositional Solver
% 14.75/2.52  
% 14.75/2.52  prop_solver_calls:                      27
% 14.75/2.52  prop_fast_solver_calls:                 308
% 14.75/2.52  smt_solver_calls:                       0
% 14.75/2.52  smt_fast_solver_calls:                  0
% 14.75/2.52  prop_num_of_clauses:                    6255
% 14.75/2.52  prop_preprocess_simplified:             7738
% 14.75/2.52  prop_fo_subsumed:                       1
% 14.75/2.52  prop_solver_time:                       0.
% 14.75/2.52  smt_solver_time:                        0.
% 14.75/2.52  smt_fast_solver_time:                   0.
% 14.75/2.52  prop_fast_solver_time:                  0.
% 14.75/2.52  prop_unsat_core_time:                   0.
% 14.75/2.52  
% 14.75/2.52  ------ QBF
% 14.75/2.52  
% 14.75/2.52  qbf_q_res:                              0
% 14.75/2.52  qbf_num_tautologies:                    0
% 14.75/2.52  qbf_prep_cycles:                        0
% 14.75/2.52  
% 14.75/2.52  ------ BMC1
% 14.75/2.52  
% 14.75/2.52  bmc1_current_bound:                     -1
% 14.75/2.52  bmc1_last_solved_bound:                 -1
% 14.75/2.52  bmc1_unsat_core_size:                   -1
% 14.75/2.52  bmc1_unsat_core_parents_size:           -1
% 14.75/2.52  bmc1_merge_next_fun:                    0
% 14.75/2.52  bmc1_unsat_core_clauses_time:           0.
% 14.75/2.52  
% 14.75/2.52  ------ Instantiation
% 14.75/2.52  
% 14.75/2.52  inst_num_of_clauses:                    1592
% 14.75/2.52  inst_num_in_passive:                    406
% 14.75/2.52  inst_num_in_active:                     656
% 14.75/2.52  inst_num_in_unprocessed:                530
% 14.75/2.52  inst_num_of_loops:                      670
% 14.75/2.52  inst_num_of_learning_restarts:          0
% 14.75/2.52  inst_num_moves_active_passive:          8
% 14.75/2.52  inst_lit_activity:                      0
% 14.75/2.52  inst_lit_activity_moves:                0
% 14.75/2.52  inst_num_tautologies:                   0
% 14.75/2.52  inst_num_prop_implied:                  0
% 14.75/2.52  inst_num_existing_simplified:           0
% 14.75/2.52  inst_num_eq_res_simplified:             0
% 14.75/2.52  inst_num_child_elim:                    0
% 14.75/2.52  inst_num_of_dismatching_blockings:      5801
% 14.75/2.52  inst_num_of_non_proper_insts:           4911
% 14.75/2.52  inst_num_of_duplicates:                 0
% 14.75/2.52  inst_inst_num_from_inst_to_res:         0
% 14.75/2.52  inst_dismatching_checking_time:         0.
% 14.75/2.52  
% 14.75/2.52  ------ Resolution
% 14.75/2.52  
% 14.75/2.52  res_num_of_clauses:                     0
% 14.75/2.52  res_num_in_passive:                     0
% 14.75/2.52  res_num_in_active:                      0
% 14.75/2.52  res_num_of_loops:                       38
% 14.75/2.52  res_forward_subset_subsumed:            617
% 14.75/2.52  res_backward_subset_subsumed:           0
% 14.75/2.52  res_forward_subsumed:                   0
% 14.75/2.52  res_backward_subsumed:                  0
% 14.75/2.52  res_forward_subsumption_resolution:     0
% 14.75/2.52  res_backward_subsumption_resolution:    0
% 14.75/2.52  res_clause_to_clause_subsumption:       10497
% 14.75/2.52  res_orphan_elimination:                 0
% 14.75/2.52  res_tautology_del:                      629
% 14.75/2.52  res_num_eq_res_simplified:              0
% 14.75/2.52  res_num_sel_changes:                    0
% 14.75/2.52  res_moves_from_active_to_pass:          0
% 14.75/2.52  
% 14.75/2.52  ------ Superposition
% 14.75/2.52  
% 14.75/2.52  sup_time_total:                         0.
% 14.75/2.52  sup_time_generating:                    0.
% 14.75/2.52  sup_time_sim_full:                      0.
% 14.75/2.52  sup_time_sim_immed:                     0.
% 14.75/2.52  
% 14.75/2.52  sup_num_of_clauses:                     2422
% 14.75/2.52  sup_num_in_active:                      123
% 14.75/2.52  sup_num_in_passive:                     2299
% 14.75/2.52  sup_num_of_loops:                       132
% 14.75/2.52  sup_fw_superposition:                   3282
% 14.75/2.52  sup_bw_superposition:                   3256
% 14.75/2.52  sup_immediate_simplified:               5243
% 14.75/2.52  sup_given_eliminated:                   3
% 14.75/2.52  comparisons_done:                       0
% 14.75/2.52  comparisons_avoided:                    0
% 14.75/2.52  
% 14.75/2.52  ------ Simplifications
% 14.75/2.52  
% 14.75/2.52  
% 14.75/2.52  sim_fw_subset_subsumed:                 9
% 14.75/2.52  sim_bw_subset_subsumed:                 0
% 14.75/2.52  sim_fw_subsumed:                        472
% 14.75/2.52  sim_bw_subsumed:                        67
% 14.75/2.52  sim_fw_subsumption_res:                 0
% 14.75/2.52  sim_bw_subsumption_res:                 0
% 14.75/2.52  sim_tautology_del:                      10
% 14.75/2.52  sim_eq_tautology_del:                   441
% 14.75/2.52  sim_eq_res_simp:                        0
% 14.75/2.52  sim_fw_demodulated:                     3549
% 14.75/2.52  sim_bw_demodulated:                     301
% 14.75/2.52  sim_light_normalised:                   1348
% 14.75/2.52  sim_joinable_taut:                      0
% 14.75/2.52  sim_joinable_simp:                      0
% 14.75/2.52  sim_ac_normalised:                      0
% 14.75/2.52  sim_smt_subsumption:                    0
% 14.75/2.52  
%------------------------------------------------------------------------------
