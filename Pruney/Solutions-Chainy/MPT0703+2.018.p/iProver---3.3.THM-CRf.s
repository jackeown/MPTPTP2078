%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:17 EST 2020

% Result     : Theorem 15.28s
% Output     : CNFRefutation 15.28s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 270 expanded)
%              Number of clauses        :   55 (  87 expanded)
%              Number of leaves         :   10 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  216 ( 857 expanded)
%              Number of equality atoms :   79 ( 167 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f38,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_586,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_592,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1930,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_592])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2471,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1930,c_16])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_588,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_597,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1261,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_588,c_597])).

cnf(c_2482,plain,
    ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2471,c_1261])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_589,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_593,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_595,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1404,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_595])).

cnf(c_3289,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_597])).

cnf(c_3535,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_589,c_3289])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_596,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3566,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3535,c_596])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_591,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3794,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3566,c_591])).

cnf(c_732,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_relat_1(X2))
    | r1_tarski(X0,k2_relat_1(X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1033,plain,
    ( r1_tarski(X0,k2_relat_1(sK2))
    | ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_1200,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ r1_tarski(k6_subset_1(sK0,X0),sK0)
    | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_1201,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1377,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_52937,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3794,c_14,c_13,c_11,c_1200,c_1201,c_1377])).

cnf(c_52941,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2482,c_52937])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_598,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1257,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_598,c_597])).

cnf(c_2481,plain,
    ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2471,c_1257])).

cnf(c_2486,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2481,c_1257])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_594,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1089,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_591])).

cnf(c_4614,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_1089])).

cnf(c_735,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_738,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_736,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_742,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_5551,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4614,c_14,c_13,c_738,c_742])).

cnf(c_11525,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2486,c_5551])).

cnf(c_53011,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_52941,c_11525])).

cnf(c_693,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53011,c_693,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.28/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.28/2.49  
% 15.28/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.28/2.49  
% 15.28/2.49  ------  iProver source info
% 15.28/2.49  
% 15.28/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.28/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.28/2.49  git: non_committed_changes: false
% 15.28/2.49  git: last_make_outside_of_git: false
% 15.28/2.49  
% 15.28/2.49  ------ 
% 15.28/2.49  ------ Parsing...
% 15.28/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.28/2.49  
% 15.28/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.28/2.49  
% 15.28/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.28/2.49  
% 15.28/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.28/2.49  ------ Proving...
% 15.28/2.49  ------ Problem Properties 
% 15.28/2.49  
% 15.28/2.49  
% 15.28/2.49  clauses                                 14
% 15.28/2.49  conjectures                             5
% 15.28/2.49  EPR                                     7
% 15.28/2.49  Horn                                    14
% 15.28/2.49  unary                                   8
% 15.28/2.49  binary                                  2
% 15.28/2.49  lits                                    25
% 15.28/2.49  lits eq                                 5
% 15.28/2.49  fd_pure                                 0
% 15.28/2.49  fd_pseudo                               0
% 15.28/2.49  fd_cond                                 0
% 15.28/2.49  fd_pseudo_cond                          1
% 15.28/2.49  AC symbols                              0
% 15.28/2.49  
% 15.28/2.49  ------ Input Options Time Limit: Unbounded
% 15.28/2.49  
% 15.28/2.49  
% 15.28/2.49  ------ 
% 15.28/2.49  Current options:
% 15.28/2.49  ------ 
% 15.28/2.49  
% 15.28/2.49  
% 15.28/2.49  
% 15.28/2.49  
% 15.28/2.49  ------ Proving...
% 15.28/2.49  
% 15.28/2.49  
% 15.28/2.49  % SZS status Theorem for theBenchmark.p
% 15.28/2.49  
% 15.28/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.28/2.49  
% 15.28/2.49  fof(f9,conjecture,(
% 15.28/2.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f10,negated_conjecture,(
% 15.28/2.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 15.28/2.49    inference(negated_conjecture,[],[f9])).
% 15.28/2.49  
% 15.28/2.49  fof(f17,plain,(
% 15.28/2.49    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 15.28/2.49    inference(ennf_transformation,[],[f10])).
% 15.28/2.49  
% 15.28/2.49  fof(f18,plain,(
% 15.28/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 15.28/2.49    inference(flattening,[],[f17])).
% 15.28/2.49  
% 15.28/2.49  fof(f22,plain,(
% 15.28/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 15.28/2.49    introduced(choice_axiom,[])).
% 15.28/2.49  
% 15.28/2.49  fof(f23,plain,(
% 15.28/2.49    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 15.28/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 15.28/2.49  
% 15.28/2.49  fof(f35,plain,(
% 15.28/2.49    v1_relat_1(sK2)),
% 15.28/2.49    inference(cnf_transformation,[],[f23])).
% 15.28/2.49  
% 15.28/2.49  fof(f7,axiom,(
% 15.28/2.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f13,plain,(
% 15.28/2.49    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 15.28/2.49    inference(ennf_transformation,[],[f7])).
% 15.28/2.49  
% 15.28/2.49  fof(f14,plain,(
% 15.28/2.49    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.28/2.49    inference(flattening,[],[f13])).
% 15.28/2.49  
% 15.28/2.49  fof(f33,plain,(
% 15.28/2.49    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.28/2.49    inference(cnf_transformation,[],[f14])).
% 15.28/2.49  
% 15.28/2.49  fof(f36,plain,(
% 15.28/2.49    v1_funct_1(sK2)),
% 15.28/2.49    inference(cnf_transformation,[],[f23])).
% 15.28/2.49  
% 15.28/2.49  fof(f37,plain,(
% 15.28/2.49    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 15.28/2.49    inference(cnf_transformation,[],[f23])).
% 15.28/2.49  
% 15.28/2.49  fof(f2,axiom,(
% 15.28/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f21,plain,(
% 15.28/2.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.28/2.49    inference(nnf_transformation,[],[f2])).
% 15.28/2.49  
% 15.28/2.49  fof(f28,plain,(
% 15.28/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.28/2.49    inference(cnf_transformation,[],[f21])).
% 15.28/2.49  
% 15.28/2.49  fof(f6,axiom,(
% 15.28/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f32,plain,(
% 15.28/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 15.28/2.49    inference(cnf_transformation,[],[f6])).
% 15.28/2.49  
% 15.28/2.49  fof(f40,plain,(
% 15.28/2.49    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 15.28/2.49    inference(definition_unfolding,[],[f28,f32])).
% 15.28/2.49  
% 15.28/2.49  fof(f38,plain,(
% 15.28/2.49    r1_tarski(sK0,k2_relat_1(sK2))),
% 15.28/2.49    inference(cnf_transformation,[],[f23])).
% 15.28/2.49  
% 15.28/2.49  fof(f5,axiom,(
% 15.28/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f31,plain,(
% 15.28/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.28/2.49    inference(cnf_transformation,[],[f5])).
% 15.28/2.49  
% 15.28/2.49  fof(f42,plain,(
% 15.28/2.49    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 15.28/2.49    inference(definition_unfolding,[],[f31,f32])).
% 15.28/2.49  
% 15.28/2.49  fof(f3,axiom,(
% 15.28/2.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f11,plain,(
% 15.28/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 15.28/2.49    inference(ennf_transformation,[],[f3])).
% 15.28/2.49  
% 15.28/2.49  fof(f12,plain,(
% 15.28/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 15.28/2.49    inference(flattening,[],[f11])).
% 15.28/2.49  
% 15.28/2.49  fof(f29,plain,(
% 15.28/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 15.28/2.49    inference(cnf_transformation,[],[f12])).
% 15.28/2.49  
% 15.28/2.49  fof(f27,plain,(
% 15.28/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.28/2.49    inference(cnf_transformation,[],[f21])).
% 15.28/2.49  
% 15.28/2.49  fof(f41,plain,(
% 15.28/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 15.28/2.49    inference(definition_unfolding,[],[f27,f32])).
% 15.28/2.49  
% 15.28/2.49  fof(f8,axiom,(
% 15.28/2.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f15,plain,(
% 15.28/2.49    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.28/2.49    inference(ennf_transformation,[],[f8])).
% 15.28/2.49  
% 15.28/2.49  fof(f16,plain,(
% 15.28/2.49    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.28/2.49    inference(flattening,[],[f15])).
% 15.28/2.49  
% 15.28/2.49  fof(f34,plain,(
% 15.28/2.49    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.28/2.49    inference(cnf_transformation,[],[f16])).
% 15.28/2.49  
% 15.28/2.49  fof(f1,axiom,(
% 15.28/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f19,plain,(
% 15.28/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.28/2.49    inference(nnf_transformation,[],[f1])).
% 15.28/2.49  
% 15.28/2.49  fof(f20,plain,(
% 15.28/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.28/2.49    inference(flattening,[],[f19])).
% 15.28/2.49  
% 15.28/2.49  fof(f24,plain,(
% 15.28/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.28/2.49    inference(cnf_transformation,[],[f20])).
% 15.28/2.49  
% 15.28/2.49  fof(f44,plain,(
% 15.28/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.28/2.49    inference(equality_resolution,[],[f24])).
% 15.28/2.49  
% 15.28/2.49  fof(f4,axiom,(
% 15.28/2.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.28/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.49  
% 15.28/2.49  fof(f30,plain,(
% 15.28/2.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.28/2.49    inference(cnf_transformation,[],[f4])).
% 15.28/2.49  
% 15.28/2.49  fof(f39,plain,(
% 15.28/2.49    ~r1_tarski(sK0,sK1)),
% 15.28/2.49    inference(cnf_transformation,[],[f23])).
% 15.28/2.49  
% 15.28/2.49  cnf(c_14,negated_conjecture,
% 15.28/2.49      ( v1_relat_1(sK2) ),
% 15.28/2.49      inference(cnf_transformation,[],[f35]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_586,plain,
% 15.28/2.49      ( v1_relat_1(sK2) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_8,plain,
% 15.28/2.49      ( ~ v1_relat_1(X0)
% 15.28/2.49      | ~ v1_funct_1(X0)
% 15.28/2.49      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 15.28/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_592,plain,
% 15.28/2.49      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 15.28/2.49      | v1_relat_1(X0) != iProver_top
% 15.28/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1930,plain,
% 15.28/2.49      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 15.28/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_586,c_592]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_13,negated_conjecture,
% 15.28/2.49      ( v1_funct_1(sK2) ),
% 15.28/2.49      inference(cnf_transformation,[],[f36]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_16,plain,
% 15.28/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_2471,plain,
% 15.28/2.49      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 15.28/2.49      inference(global_propositional_subsumption,
% 15.28/2.49                [status(thm)],
% 15.28/2.49                [c_1930,c_16]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_12,negated_conjecture,
% 15.28/2.49      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 15.28/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_588,plain,
% 15.28/2.49      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_3,plain,
% 15.28/2.49      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 15.28/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_597,plain,
% 15.28/2.49      ( k6_subset_1(X0,X1) = k1_xboole_0
% 15.28/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1261,plain,
% 15.28/2.49      ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_588,c_597]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_2482,plain,
% 15.28/2.49      ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_2471,c_1261]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_11,negated_conjecture,
% 15.28/2.49      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 15.28/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_589,plain,
% 15.28/2.49      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_7,plain,
% 15.28/2.49      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 15.28/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_593,plain,
% 15.28/2.49      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_5,plain,
% 15.28/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 15.28/2.49      inference(cnf_transformation,[],[f29]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_595,plain,
% 15.28/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.28/2.49      | r1_tarski(X1,X2) != iProver_top
% 15.28/2.49      | r1_tarski(X0,X2) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1404,plain,
% 15.28/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.28/2.49      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_593,c_595]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_3289,plain,
% 15.28/2.49      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 15.28/2.49      | r1_tarski(X0,X2) != iProver_top ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_1404,c_597]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_3535,plain,
% 15.28/2.49      ( k6_subset_1(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = k1_xboole_0 ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_589,c_3289]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_4,plain,
% 15.28/2.49      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 15.28/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_596,plain,
% 15.28/2.49      ( k6_subset_1(X0,X1) != k1_xboole_0
% 15.28/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_3566,plain,
% 15.28/2.49      ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_3535,c_596]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_9,plain,
% 15.28/2.49      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 15.28/2.49      | ~ v1_relat_1(X1)
% 15.28/2.49      | ~ v1_funct_1(X1)
% 15.28/2.49      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 15.28/2.49      inference(cnf_transformation,[],[f34]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_591,plain,
% 15.28/2.49      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 15.28/2.49      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 15.28/2.49      | v1_relat_1(X0) != iProver_top
% 15.28/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_3794,plain,
% 15.28/2.49      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0)
% 15.28/2.49      | v1_relat_1(sK2) != iProver_top
% 15.28/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_3566,c_591]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_732,plain,
% 15.28/2.49      ( ~ r1_tarski(X0,X1)
% 15.28/2.49      | ~ r1_tarski(X1,k2_relat_1(X2))
% 15.28/2.49      | r1_tarski(X0,k2_relat_1(X2)) ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1033,plain,
% 15.28/2.49      ( r1_tarski(X0,k2_relat_1(sK2))
% 15.28/2.49      | ~ r1_tarski(X0,sK0)
% 15.28/2.49      | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_732]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1200,plain,
% 15.28/2.49      ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
% 15.28/2.49      | ~ r1_tarski(k6_subset_1(sK0,X0),sK0)
% 15.28/2.49      | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_1033]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1201,plain,
% 15.28/2.49      ( r1_tarski(k6_subset_1(sK0,X0),sK0) ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1377,plain,
% 15.28/2.49      ( ~ r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
% 15.28/2.49      | ~ v1_relat_1(sK2)
% 15.28/2.49      | ~ v1_funct_1(sK2)
% 15.28/2.49      | k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0) ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_52937,plain,
% 15.28/2.49      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0) ),
% 15.28/2.49      inference(global_propositional_subsumption,
% 15.28/2.49                [status(thm)],
% 15.28/2.49                [c_3794,c_14,c_13,c_11,c_1200,c_1201,c_1377]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_52941,plain,
% 15.28/2.49      ( k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(sK0,sK1) ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_2482,c_52937]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_2,plain,
% 15.28/2.49      ( r1_tarski(X0,X0) ),
% 15.28/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_598,plain,
% 15.28/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1257,plain,
% 15.28/2.49      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_598,c_597]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_2481,plain,
% 15.28/2.49      ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_2471,c_1257]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_2486,plain,
% 15.28/2.49      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 15.28/2.49      inference(light_normalisation,[status(thm)],[c_2481,c_1257]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_6,plain,
% 15.28/2.49      ( r1_tarski(k1_xboole_0,X0) ),
% 15.28/2.49      inference(cnf_transformation,[],[f30]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_594,plain,
% 15.28/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.28/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_1089,plain,
% 15.28/2.49      ( k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 15.28/2.49      | v1_relat_1(X0) != iProver_top
% 15.28/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_594,c_591]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_4614,plain,
% 15.28/2.49      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
% 15.28/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.28/2.49      inference(superposition,[status(thm)],[c_586,c_1089]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_735,plain,
% 15.28/2.49      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
% 15.28/2.49      | ~ v1_relat_1(X0)
% 15.28/2.49      | ~ v1_funct_1(X0)
% 15.28/2.49      | k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_738,plain,
% 15.28/2.49      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
% 15.28/2.49      | ~ v1_relat_1(sK2)
% 15.28/2.49      | ~ v1_funct_1(sK2)
% 15.28/2.49      | k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_735]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_736,plain,
% 15.28/2.49      ( r1_tarski(k1_xboole_0,k2_relat_1(X0)) ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_742,plain,
% 15.28/2.49      ( r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_736]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_5551,plain,
% 15.28/2.49      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 15.28/2.49      inference(global_propositional_subsumption,
% 15.28/2.49                [status(thm)],
% 15.28/2.49                [c_4614,c_14,c_13,c_738,c_742]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_11525,plain,
% 15.28/2.49      ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 15.28/2.49      inference(demodulation,[status(thm)],[c_2486,c_5551]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_53011,plain,
% 15.28/2.49      ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 15.28/2.49      inference(light_normalisation,[status(thm)],[c_52941,c_11525]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_693,plain,
% 15.28/2.49      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 15.28/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(c_10,negated_conjecture,
% 15.28/2.49      ( ~ r1_tarski(sK0,sK1) ),
% 15.28/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.28/2.49  
% 15.28/2.49  cnf(contradiction,plain,
% 15.28/2.49      ( $false ),
% 15.28/2.49      inference(minisat,[status(thm)],[c_53011,c_693,c_10]) ).
% 15.28/2.49  
% 15.28/2.49  
% 15.28/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.28/2.49  
% 15.28/2.49  ------                               Statistics
% 15.28/2.49  
% 15.28/2.49  ------ Selected
% 15.28/2.49  
% 15.28/2.49  total_time:                             1.688
% 15.28/2.49  
%------------------------------------------------------------------------------
