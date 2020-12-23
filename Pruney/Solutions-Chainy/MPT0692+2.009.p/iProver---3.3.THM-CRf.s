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
% DateTime   : Thu Dec  3 11:51:53 EST 2020

% Result     : Theorem 20.10s
% Output     : CNFRefutation 20.10s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 158 expanded)
%              Number of clauses        :   41 (  49 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  212 ( 457 expanded)
%              Number of equality atoms :   87 ( 162 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).

fof(f43,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_577,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k6_subset_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_583,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_585,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1096,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_585])).

cnf(c_2285,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k2_relat_1(sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_577,c_1096])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_584,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2713,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2285,c_584])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_575,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_582,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_578,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_986,plain,
    ( k6_subset_1(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_585])).

cnf(c_1491,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,k9_relat_1(X0,k10_relat_1(X0,X1)))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_986])).

cnf(c_5696,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_575,c_1491])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_576,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_580,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1369,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_580])).

cnf(c_15,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5030,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1369,c_15])).

cnf(c_5809,plain,
    ( k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5696,c_5030])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_581,plain,
    ( k10_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_78750,plain,
    ( k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0
    | r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5809,c_581])).

cnf(c_79515,plain,
    ( r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top
    | k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_78750,c_15])).

cnf(c_79516,plain,
    ( k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0
    | r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_79515])).

cnf(c_79525,plain,
    ( k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2713,c_79516])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,negated_conjecture,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1110,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(resolution,[status(thm)],[c_0,c_11])).

cnf(c_9,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1277,plain,
    ( ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_1110,c_9])).

cnf(c_773,plain,
    ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79525,c_1277,c_773,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 20.10/3.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.10/3.01  
% 20.10/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 20.10/3.01  
% 20.10/3.01  ------  iProver source info
% 20.10/3.01  
% 20.10/3.01  git: date: 2020-06-30 10:37:57 +0100
% 20.10/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 20.10/3.01  git: non_committed_changes: false
% 20.10/3.01  git: last_make_outside_of_git: false
% 20.10/3.01  
% 20.10/3.01  ------ 
% 20.10/3.01  
% 20.10/3.01  ------ Input Options
% 20.10/3.01  
% 20.10/3.01  --out_options                           all
% 20.10/3.01  --tptp_safe_out                         true
% 20.10/3.01  --problem_path                          ""
% 20.10/3.01  --include_path                          ""
% 20.10/3.01  --clausifier                            res/vclausify_rel
% 20.10/3.01  --clausifier_options                    --mode clausify
% 20.10/3.01  --stdin                                 false
% 20.10/3.01  --stats_out                             sel
% 20.10/3.01  
% 20.10/3.01  ------ General Options
% 20.10/3.01  
% 20.10/3.01  --fof                                   false
% 20.10/3.01  --time_out_real                         604.99
% 20.10/3.01  --time_out_virtual                      -1.
% 20.10/3.01  --symbol_type_check                     false
% 20.10/3.01  --clausify_out                          false
% 20.10/3.01  --sig_cnt_out                           false
% 20.10/3.01  --trig_cnt_out                          false
% 20.10/3.01  --trig_cnt_out_tolerance                1.
% 20.10/3.01  --trig_cnt_out_sk_spl                   false
% 20.10/3.01  --abstr_cl_out                          false
% 20.10/3.01  
% 20.10/3.01  ------ Global Options
% 20.10/3.01  
% 20.10/3.01  --schedule                              none
% 20.10/3.01  --add_important_lit                     false
% 20.10/3.01  --prop_solver_per_cl                    1000
% 20.10/3.01  --min_unsat_core                        false
% 20.10/3.01  --soft_assumptions                      false
% 20.10/3.01  --soft_lemma_size                       3
% 20.10/3.01  --prop_impl_unit_size                   0
% 20.10/3.01  --prop_impl_unit                        []
% 20.10/3.01  --share_sel_clauses                     true
% 20.10/3.01  --reset_solvers                         false
% 20.10/3.01  --bc_imp_inh                            [conj_cone]
% 20.10/3.01  --conj_cone_tolerance                   3.
% 20.10/3.01  --extra_neg_conj                        none
% 20.10/3.01  --large_theory_mode                     true
% 20.10/3.01  --prolific_symb_bound                   200
% 20.10/3.01  --lt_threshold                          2000
% 20.10/3.01  --clause_weak_htbl                      true
% 20.10/3.01  --gc_record_bc_elim                     false
% 20.10/3.01  
% 20.10/3.01  ------ Preprocessing Options
% 20.10/3.01  
% 20.10/3.01  --preprocessing_flag                    true
% 20.10/3.01  --time_out_prep_mult                    0.1
% 20.10/3.01  --splitting_mode                        input
% 20.10/3.01  --splitting_grd                         true
% 20.10/3.01  --splitting_cvd                         false
% 20.10/3.01  --splitting_cvd_svl                     false
% 20.10/3.01  --splitting_nvd                         32
% 20.10/3.01  --sub_typing                            true
% 20.10/3.01  --prep_gs_sim                           false
% 20.10/3.01  --prep_unflatten                        true
% 20.10/3.01  --prep_res_sim                          true
% 20.10/3.01  --prep_upred                            true
% 20.10/3.01  --prep_sem_filter                       exhaustive
% 20.10/3.01  --prep_sem_filter_out                   false
% 20.10/3.01  --pred_elim                             false
% 20.10/3.01  --res_sim_input                         true
% 20.10/3.01  --eq_ax_congr_red                       true
% 20.10/3.01  --pure_diseq_elim                       true
% 20.10/3.01  --brand_transform                       false
% 20.10/3.01  --non_eq_to_eq                          false
% 20.10/3.01  --prep_def_merge                        true
% 20.10/3.01  --prep_def_merge_prop_impl              false
% 20.10/3.01  --prep_def_merge_mbd                    true
% 20.10/3.01  --prep_def_merge_tr_red                 false
% 20.10/3.01  --prep_def_merge_tr_cl                  false
% 20.10/3.01  --smt_preprocessing                     true
% 20.10/3.01  --smt_ac_axioms                         fast
% 20.10/3.01  --preprocessed_out                      false
% 20.10/3.01  --preprocessed_stats                    false
% 20.10/3.01  
% 20.10/3.01  ------ Abstraction refinement Options
% 20.10/3.01  
% 20.10/3.01  --abstr_ref                             []
% 20.10/3.01  --abstr_ref_prep                        false
% 20.10/3.01  --abstr_ref_until_sat                   false
% 20.10/3.01  --abstr_ref_sig_restrict                funpre
% 20.10/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 20.10/3.01  --abstr_ref_under                       []
% 20.10/3.01  
% 20.10/3.01  ------ SAT Options
% 20.10/3.01  
% 20.10/3.01  --sat_mode                              false
% 20.10/3.01  --sat_fm_restart_options                ""
% 20.10/3.01  --sat_gr_def                            false
% 20.10/3.01  --sat_epr_types                         true
% 20.10/3.01  --sat_non_cyclic_types                  false
% 20.10/3.01  --sat_finite_models                     false
% 20.10/3.01  --sat_fm_lemmas                         false
% 20.10/3.01  --sat_fm_prep                           false
% 20.10/3.01  --sat_fm_uc_incr                        true
% 20.10/3.01  --sat_out_model                         small
% 20.10/3.01  --sat_out_clauses                       false
% 20.10/3.01  
% 20.10/3.01  ------ QBF Options
% 20.10/3.01  
% 20.10/3.01  --qbf_mode                              false
% 20.10/3.01  --qbf_elim_univ                         false
% 20.10/3.01  --qbf_dom_inst                          none
% 20.10/3.01  --qbf_dom_pre_inst                      false
% 20.10/3.01  --qbf_sk_in                             false
% 20.10/3.01  --qbf_pred_elim                         true
% 20.10/3.01  --qbf_split                             512
% 20.10/3.01  
% 20.10/3.01  ------ BMC1 Options
% 20.10/3.01  
% 20.10/3.01  --bmc1_incremental                      false
% 20.10/3.01  --bmc1_axioms                           reachable_all
% 20.10/3.01  --bmc1_min_bound                        0
% 20.10/3.01  --bmc1_max_bound                        -1
% 20.10/3.01  --bmc1_max_bound_default                -1
% 20.10/3.01  --bmc1_symbol_reachability              true
% 20.10/3.01  --bmc1_property_lemmas                  false
% 20.10/3.01  --bmc1_k_induction                      false
% 20.10/3.01  --bmc1_non_equiv_states                 false
% 20.10/3.01  --bmc1_deadlock                         false
% 20.10/3.01  --bmc1_ucm                              false
% 20.10/3.01  --bmc1_add_unsat_core                   none
% 20.10/3.01  --bmc1_unsat_core_children              false
% 20.10/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 20.10/3.01  --bmc1_out_stat                         full
% 20.10/3.01  --bmc1_ground_init                      false
% 20.10/3.01  --bmc1_pre_inst_next_state              false
% 20.10/3.01  --bmc1_pre_inst_state                   false
% 20.10/3.01  --bmc1_pre_inst_reach_state             false
% 20.10/3.01  --bmc1_out_unsat_core                   false
% 20.10/3.01  --bmc1_aig_witness_out                  false
% 20.10/3.01  --bmc1_verbose                          false
% 20.10/3.01  --bmc1_dump_clauses_tptp                false
% 20.10/3.01  --bmc1_dump_unsat_core_tptp             false
% 20.10/3.01  --bmc1_dump_file                        -
% 20.10/3.01  --bmc1_ucm_expand_uc_limit              128
% 20.10/3.01  --bmc1_ucm_n_expand_iterations          6
% 20.10/3.01  --bmc1_ucm_extend_mode                  1
% 20.10/3.01  --bmc1_ucm_init_mode                    2
% 20.10/3.01  --bmc1_ucm_cone_mode                    none
% 20.10/3.01  --bmc1_ucm_reduced_relation_type        0
% 20.10/3.01  --bmc1_ucm_relax_model                  4
% 20.10/3.01  --bmc1_ucm_full_tr_after_sat            true
% 20.10/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 20.10/3.01  --bmc1_ucm_layered_model                none
% 20.10/3.01  --bmc1_ucm_max_lemma_size               10
% 20.10/3.01  
% 20.10/3.01  ------ AIG Options
% 20.10/3.01  
% 20.10/3.01  --aig_mode                              false
% 20.10/3.01  
% 20.10/3.01  ------ Instantiation Options
% 20.10/3.01  
% 20.10/3.01  --instantiation_flag                    true
% 20.10/3.01  --inst_sos_flag                         false
% 20.10/3.01  --inst_sos_phase                        true
% 20.10/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 20.10/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 20.10/3.01  --inst_lit_sel_side                     num_symb
% 20.10/3.01  --inst_solver_per_active                1400
% 20.10/3.01  --inst_solver_calls_frac                1.
% 20.10/3.01  --inst_passive_queue_type               priority_queues
% 20.10/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 20.10/3.01  --inst_passive_queues_freq              [25;2]
% 20.10/3.01  --inst_dismatching                      true
% 20.10/3.01  --inst_eager_unprocessed_to_passive     true
% 20.10/3.01  --inst_prop_sim_given                   true
% 20.10/3.01  --inst_prop_sim_new                     false
% 20.10/3.01  --inst_subs_new                         false
% 20.10/3.01  --inst_eq_res_simp                      false
% 20.10/3.01  --inst_subs_given                       false
% 20.10/3.01  --inst_orphan_elimination               true
% 20.10/3.01  --inst_learning_loop_flag               true
% 20.10/3.01  --inst_learning_start                   3000
% 20.10/3.01  --inst_learning_factor                  2
% 20.10/3.01  --inst_start_prop_sim_after_learn       3
% 20.10/3.01  --inst_sel_renew                        solver
% 20.10/3.01  --inst_lit_activity_flag                true
% 20.10/3.01  --inst_restr_to_given                   false
% 20.10/3.01  --inst_activity_threshold               500
% 20.10/3.01  --inst_out_proof                        true
% 20.10/3.01  
% 20.10/3.01  ------ Resolution Options
% 20.10/3.01  
% 20.10/3.01  --resolution_flag                       true
% 20.10/3.01  --res_lit_sel                           adaptive
% 20.10/3.01  --res_lit_sel_side                      none
% 20.10/3.01  --res_ordering                          kbo
% 20.10/3.01  --res_to_prop_solver                    active
% 20.10/3.01  --res_prop_simpl_new                    false
% 20.10/3.01  --res_prop_simpl_given                  true
% 20.10/3.01  --res_passive_queue_type                priority_queues
% 20.10/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 20.10/3.01  --res_passive_queues_freq               [15;5]
% 20.10/3.01  --res_forward_subs                      full
% 20.10/3.01  --res_backward_subs                     full
% 20.10/3.01  --res_forward_subs_resolution           true
% 20.10/3.01  --res_backward_subs_resolution          true
% 20.10/3.01  --res_orphan_elimination                true
% 20.10/3.01  --res_time_limit                        2.
% 20.10/3.01  --res_out_proof                         true
% 20.10/3.01  
% 20.10/3.01  ------ Superposition Options
% 20.10/3.01  
% 20.10/3.01  --superposition_flag                    true
% 20.10/3.01  --sup_passive_queue_type                priority_queues
% 20.10/3.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 20.10/3.01  --sup_passive_queues_freq               [1;4]
% 20.10/3.01  --demod_completeness_check              fast
% 20.10/3.01  --demod_use_ground                      true
% 20.10/3.01  --sup_to_prop_solver                    passive
% 20.10/3.01  --sup_prop_simpl_new                    true
% 20.10/3.01  --sup_prop_simpl_given                  true
% 20.10/3.01  --sup_fun_splitting                     false
% 20.10/3.01  --sup_smt_interval                      50000
% 20.10/3.01  
% 20.10/3.01  ------ Superposition Simplification Setup
% 20.10/3.01  
% 20.10/3.01  --sup_indices_passive                   []
% 20.10/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.10/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.10/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.10/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 20.10/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.10/3.01  --sup_full_bw                           [BwDemod]
% 20.10/3.01  --sup_immed_triv                        [TrivRules]
% 20.10/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 20.10/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.10/3.01  --sup_immed_bw_main                     []
% 20.10/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 20.10/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 20.10/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.10/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 20.10/3.01  
% 20.10/3.01  ------ Combination Options
% 20.10/3.01  
% 20.10/3.01  --comb_res_mult                         3
% 20.10/3.01  --comb_sup_mult                         2
% 20.10/3.01  --comb_inst_mult                        10
% 20.10/3.01  
% 20.10/3.01  ------ Debug Options
% 20.10/3.01  
% 20.10/3.01  --dbg_backtrace                         false
% 20.10/3.01  --dbg_dump_prop_clauses                 false
% 20.10/3.01  --dbg_dump_prop_clauses_file            -
% 20.10/3.01  --dbg_out_stat                          false
% 20.10/3.01  ------ Parsing...
% 20.10/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 20.10/3.01  
% 20.10/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 20.10/3.01  
% 20.10/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 20.10/3.01  
% 20.10/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 20.10/3.01  ------ Proving...
% 20.10/3.01  ------ Problem Properties 
% 20.10/3.01  
% 20.10/3.01  
% 20.10/3.01  clauses                                 14
% 20.10/3.01  conjectures                             4
% 20.10/3.01  EPR                                     4
% 20.10/3.01  Horn                                    14
% 20.10/3.01  unary                                   5
% 20.10/3.01  binary                                  4
% 20.10/3.01  lits                                    29
% 20.10/3.01  lits eq                                 7
% 20.10/3.01  fd_pure                                 0
% 20.10/3.01  fd_pseudo                               0
% 20.10/3.01  fd_cond                                 1
% 20.10/3.01  fd_pseudo_cond                          1
% 20.10/3.01  AC symbols                              0
% 20.10/3.01  
% 20.10/3.01  ------ Input Options Time Limit: Unbounded
% 20.10/3.01  
% 20.10/3.01  
% 20.10/3.01  ------ 
% 20.10/3.01  Current options:
% 20.10/3.01  ------ 
% 20.10/3.01  
% 20.10/3.01  ------ Input Options
% 20.10/3.01  
% 20.10/3.01  --out_options                           all
% 20.10/3.01  --tptp_safe_out                         true
% 20.10/3.01  --problem_path                          ""
% 20.10/3.01  --include_path                          ""
% 20.10/3.01  --clausifier                            res/vclausify_rel
% 20.10/3.01  --clausifier_options                    --mode clausify
% 20.10/3.01  --stdin                                 false
% 20.10/3.01  --stats_out                             sel
% 20.10/3.01  
% 20.10/3.01  ------ General Options
% 20.10/3.01  
% 20.10/3.01  --fof                                   false
% 20.10/3.01  --time_out_real                         604.99
% 20.10/3.01  --time_out_virtual                      -1.
% 20.10/3.01  --symbol_type_check                     false
% 20.10/3.01  --clausify_out                          false
% 20.10/3.01  --sig_cnt_out                           false
% 20.10/3.01  --trig_cnt_out                          false
% 20.10/3.01  --trig_cnt_out_tolerance                1.
% 20.10/3.01  --trig_cnt_out_sk_spl                   false
% 20.10/3.01  --abstr_cl_out                          false
% 20.10/3.01  
% 20.10/3.01  ------ Global Options
% 20.10/3.01  
% 20.10/3.01  --schedule                              none
% 20.10/3.01  --add_important_lit                     false
% 20.10/3.01  --prop_solver_per_cl                    1000
% 20.10/3.01  --min_unsat_core                        false
% 20.10/3.01  --soft_assumptions                      false
% 20.10/3.01  --soft_lemma_size                       3
% 20.10/3.01  --prop_impl_unit_size                   0
% 20.10/3.01  --prop_impl_unit                        []
% 20.10/3.01  --share_sel_clauses                     true
% 20.10/3.01  --reset_solvers                         false
% 20.10/3.01  --bc_imp_inh                            [conj_cone]
% 20.10/3.01  --conj_cone_tolerance                   3.
% 20.10/3.01  --extra_neg_conj                        none
% 20.10/3.01  --large_theory_mode                     true
% 20.10/3.01  --prolific_symb_bound                   200
% 20.10/3.01  --lt_threshold                          2000
% 20.10/3.01  --clause_weak_htbl                      true
% 20.10/3.01  --gc_record_bc_elim                     false
% 20.10/3.01  
% 20.10/3.01  ------ Preprocessing Options
% 20.10/3.01  
% 20.10/3.01  --preprocessing_flag                    true
% 20.10/3.01  --time_out_prep_mult                    0.1
% 20.10/3.01  --splitting_mode                        input
% 20.10/3.01  --splitting_grd                         true
% 20.10/3.01  --splitting_cvd                         false
% 20.10/3.01  --splitting_cvd_svl                     false
% 20.10/3.01  --splitting_nvd                         32
% 20.10/3.01  --sub_typing                            true
% 20.10/3.01  --prep_gs_sim                           false
% 20.10/3.01  --prep_unflatten                        true
% 20.10/3.01  --prep_res_sim                          true
% 20.10/3.01  --prep_upred                            true
% 20.10/3.01  --prep_sem_filter                       exhaustive
% 20.10/3.01  --prep_sem_filter_out                   false
% 20.10/3.01  --pred_elim                             false
% 20.10/3.01  --res_sim_input                         true
% 20.10/3.01  --eq_ax_congr_red                       true
% 20.10/3.01  --pure_diseq_elim                       true
% 20.10/3.01  --brand_transform                       false
% 20.10/3.01  --non_eq_to_eq                          false
% 20.10/3.01  --prep_def_merge                        true
% 20.10/3.01  --prep_def_merge_prop_impl              false
% 20.10/3.01  --prep_def_merge_mbd                    true
% 20.10/3.01  --prep_def_merge_tr_red                 false
% 20.10/3.01  --prep_def_merge_tr_cl                  false
% 20.10/3.01  --smt_preprocessing                     true
% 20.10/3.01  --smt_ac_axioms                         fast
% 20.10/3.01  --preprocessed_out                      false
% 20.10/3.01  --preprocessed_stats                    false
% 20.10/3.01  
% 20.10/3.01  ------ Abstraction refinement Options
% 20.10/3.01  
% 20.10/3.01  --abstr_ref                             []
% 20.10/3.01  --abstr_ref_prep                        false
% 20.10/3.01  --abstr_ref_until_sat                   false
% 20.10/3.01  --abstr_ref_sig_restrict                funpre
% 20.10/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 20.10/3.01  --abstr_ref_under                       []
% 20.10/3.01  
% 20.10/3.01  ------ SAT Options
% 20.10/3.01  
% 20.10/3.01  --sat_mode                              false
% 20.10/3.01  --sat_fm_restart_options                ""
% 20.10/3.01  --sat_gr_def                            false
% 20.10/3.01  --sat_epr_types                         true
% 20.10/3.01  --sat_non_cyclic_types                  false
% 20.10/3.01  --sat_finite_models                     false
% 20.10/3.01  --sat_fm_lemmas                         false
% 20.10/3.01  --sat_fm_prep                           false
% 20.10/3.01  --sat_fm_uc_incr                        true
% 20.10/3.01  --sat_out_model                         small
% 20.10/3.01  --sat_out_clauses                       false
% 20.10/3.01  
% 20.10/3.01  ------ QBF Options
% 20.10/3.01  
% 20.10/3.01  --qbf_mode                              false
% 20.10/3.01  --qbf_elim_univ                         false
% 20.10/3.01  --qbf_dom_inst                          none
% 20.10/3.01  --qbf_dom_pre_inst                      false
% 20.10/3.01  --qbf_sk_in                             false
% 20.10/3.01  --qbf_pred_elim                         true
% 20.10/3.01  --qbf_split                             512
% 20.10/3.01  
% 20.10/3.01  ------ BMC1 Options
% 20.10/3.01  
% 20.10/3.01  --bmc1_incremental                      false
% 20.10/3.01  --bmc1_axioms                           reachable_all
% 20.10/3.01  --bmc1_min_bound                        0
% 20.10/3.01  --bmc1_max_bound                        -1
% 20.10/3.01  --bmc1_max_bound_default                -1
% 20.10/3.01  --bmc1_symbol_reachability              true
% 20.10/3.01  --bmc1_property_lemmas                  false
% 20.10/3.01  --bmc1_k_induction                      false
% 20.10/3.01  --bmc1_non_equiv_states                 false
% 20.10/3.01  --bmc1_deadlock                         false
% 20.10/3.01  --bmc1_ucm                              false
% 20.10/3.01  --bmc1_add_unsat_core                   none
% 20.10/3.01  --bmc1_unsat_core_children              false
% 20.10/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 20.10/3.01  --bmc1_out_stat                         full
% 20.10/3.01  --bmc1_ground_init                      false
% 20.10/3.01  --bmc1_pre_inst_next_state              false
% 20.10/3.01  --bmc1_pre_inst_state                   false
% 20.10/3.01  --bmc1_pre_inst_reach_state             false
% 20.10/3.01  --bmc1_out_unsat_core                   false
% 20.10/3.01  --bmc1_aig_witness_out                  false
% 20.10/3.01  --bmc1_verbose                          false
% 20.10/3.01  --bmc1_dump_clauses_tptp                false
% 20.10/3.01  --bmc1_dump_unsat_core_tptp             false
% 20.10/3.01  --bmc1_dump_file                        -
% 20.10/3.01  --bmc1_ucm_expand_uc_limit              128
% 20.10/3.01  --bmc1_ucm_n_expand_iterations          6
% 20.10/3.01  --bmc1_ucm_extend_mode                  1
% 20.10/3.01  --bmc1_ucm_init_mode                    2
% 20.10/3.01  --bmc1_ucm_cone_mode                    none
% 20.10/3.01  --bmc1_ucm_reduced_relation_type        0
% 20.10/3.01  --bmc1_ucm_relax_model                  4
% 20.10/3.01  --bmc1_ucm_full_tr_after_sat            true
% 20.10/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 20.10/3.01  --bmc1_ucm_layered_model                none
% 20.10/3.01  --bmc1_ucm_max_lemma_size               10
% 20.10/3.01  
% 20.10/3.01  ------ AIG Options
% 20.10/3.01  
% 20.10/3.01  --aig_mode                              false
% 20.10/3.01  
% 20.10/3.01  ------ Instantiation Options
% 20.10/3.01  
% 20.10/3.01  --instantiation_flag                    true
% 20.10/3.01  --inst_sos_flag                         false
% 20.10/3.01  --inst_sos_phase                        true
% 20.10/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 20.10/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 20.10/3.01  --inst_lit_sel_side                     num_symb
% 20.10/3.01  --inst_solver_per_active                1400
% 20.10/3.01  --inst_solver_calls_frac                1.
% 20.10/3.01  --inst_passive_queue_type               priority_queues
% 20.10/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 20.10/3.01  --inst_passive_queues_freq              [25;2]
% 20.10/3.01  --inst_dismatching                      true
% 20.10/3.01  --inst_eager_unprocessed_to_passive     true
% 20.10/3.01  --inst_prop_sim_given                   true
% 20.10/3.01  --inst_prop_sim_new                     false
% 20.10/3.01  --inst_subs_new                         false
% 20.10/3.01  --inst_eq_res_simp                      false
% 20.10/3.01  --inst_subs_given                       false
% 20.10/3.01  --inst_orphan_elimination               true
% 20.10/3.01  --inst_learning_loop_flag               true
% 20.10/3.01  --inst_learning_start                   3000
% 20.10/3.01  --inst_learning_factor                  2
% 20.10/3.01  --inst_start_prop_sim_after_learn       3
% 20.10/3.01  --inst_sel_renew                        solver
% 20.10/3.01  --inst_lit_activity_flag                true
% 20.10/3.01  --inst_restr_to_given                   false
% 20.10/3.01  --inst_activity_threshold               500
% 20.10/3.01  --inst_out_proof                        true
% 20.10/3.01  
% 20.10/3.01  ------ Resolution Options
% 20.10/3.01  
% 20.10/3.01  --resolution_flag                       true
% 20.10/3.01  --res_lit_sel                           adaptive
% 20.10/3.01  --res_lit_sel_side                      none
% 20.10/3.01  --res_ordering                          kbo
% 20.10/3.01  --res_to_prop_solver                    active
% 20.10/3.01  --res_prop_simpl_new                    false
% 20.10/3.01  --res_prop_simpl_given                  true
% 20.10/3.01  --res_passive_queue_type                priority_queues
% 20.10/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 20.10/3.01  --res_passive_queues_freq               [15;5]
% 20.10/3.01  --res_forward_subs                      full
% 20.10/3.01  --res_backward_subs                     full
% 20.10/3.01  --res_forward_subs_resolution           true
% 20.10/3.01  --res_backward_subs_resolution          true
% 20.10/3.01  --res_orphan_elimination                true
% 20.10/3.01  --res_time_limit                        2.
% 20.10/3.01  --res_out_proof                         true
% 20.10/3.01  
% 20.10/3.01  ------ Superposition Options
% 20.10/3.01  
% 20.10/3.01  --superposition_flag                    true
% 20.10/3.01  --sup_passive_queue_type                priority_queues
% 20.10/3.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 20.10/3.01  --sup_passive_queues_freq               [1;4]
% 20.10/3.01  --demod_completeness_check              fast
% 20.10/3.01  --demod_use_ground                      true
% 20.10/3.01  --sup_to_prop_solver                    passive
% 20.10/3.01  --sup_prop_simpl_new                    true
% 20.10/3.01  --sup_prop_simpl_given                  true
% 20.10/3.01  --sup_fun_splitting                     false
% 20.10/3.01  --sup_smt_interval                      50000
% 20.10/3.01  
% 20.10/3.01  ------ Superposition Simplification Setup
% 20.10/3.01  
% 20.10/3.01  --sup_indices_passive                   []
% 20.10/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.10/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.10/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.10/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 20.10/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.10/3.01  --sup_full_bw                           [BwDemod]
% 20.10/3.01  --sup_immed_triv                        [TrivRules]
% 20.10/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 20.10/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.10/3.01  --sup_immed_bw_main                     []
% 20.10/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 20.10/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 20.10/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.10/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 20.10/3.01  
% 20.10/3.01  ------ Combination Options
% 20.10/3.01  
% 20.10/3.01  --comb_res_mult                         3
% 20.10/3.01  --comb_sup_mult                         2
% 20.10/3.01  --comb_inst_mult                        10
% 20.10/3.01  
% 20.10/3.01  ------ Debug Options
% 20.10/3.01  
% 20.10/3.01  --dbg_backtrace                         false
% 20.10/3.01  --dbg_dump_prop_clauses                 false
% 20.10/3.01  --dbg_dump_prop_clauses_file            -
% 20.10/3.01  --dbg_out_stat                          false
% 20.10/3.01  
% 20.10/3.01  
% 20.10/3.01  
% 20.10/3.01  
% 20.10/3.01  ------ Proving...
% 20.10/3.01  
% 20.10/3.01  
% 20.10/3.01  % SZS status Theorem for theBenchmark.p
% 20.10/3.01  
% 20.10/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 20.10/3.01  
% 20.10/3.01  fof(f10,conjecture,(
% 20.10/3.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f11,negated_conjecture,(
% 20.10/3.01    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 20.10/3.01    inference(negated_conjecture,[],[f10])).
% 20.10/3.01  
% 20.10/3.01  fof(f22,plain,(
% 20.10/3.01    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 20.10/3.01    inference(ennf_transformation,[],[f11])).
% 20.10/3.01  
% 20.10/3.01  fof(f23,plain,(
% 20.10/3.01    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 20.10/3.01    inference(flattening,[],[f22])).
% 20.10/3.01  
% 20.10/3.01  fof(f27,plain,(
% 20.10/3.01    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 20.10/3.01    introduced(choice_axiom,[])).
% 20.10/3.01  
% 20.10/3.01  fof(f28,plain,(
% 20.10/3.01    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 20.10/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).
% 20.10/3.01  
% 20.10/3.01  fof(f43,plain,(
% 20.10/3.01    r1_tarski(sK0,k2_relat_1(sK1))),
% 20.10/3.01    inference(cnf_transformation,[],[f28])).
% 20.10/3.01  
% 20.10/3.01  fof(f3,axiom,(
% 20.10/3.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f12,plain,(
% 20.10/3.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 20.10/3.01    inference(ennf_transformation,[],[f3])).
% 20.10/3.01  
% 20.10/3.01  fof(f34,plain,(
% 20.10/3.01    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f12])).
% 20.10/3.01  
% 20.10/3.01  fof(f4,axiom,(
% 20.10/3.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f35,plain,(
% 20.10/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f4])).
% 20.10/3.01  
% 20.10/3.01  fof(f47,plain,(
% 20.10/3.01    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 20.10/3.01    inference(definition_unfolding,[],[f34,f35])).
% 20.10/3.01  
% 20.10/3.01  fof(f2,axiom,(
% 20.10/3.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f26,plain,(
% 20.10/3.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 20.10/3.01    inference(nnf_transformation,[],[f2])).
% 20.10/3.01  
% 20.10/3.01  fof(f33,plain,(
% 20.10/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f26])).
% 20.10/3.01  
% 20.10/3.01  fof(f45,plain,(
% 20.10/3.01    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 20.10/3.01    inference(definition_unfolding,[],[f33,f35])).
% 20.10/3.01  
% 20.10/3.01  fof(f32,plain,(
% 20.10/3.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 20.10/3.01    inference(cnf_transformation,[],[f26])).
% 20.10/3.01  
% 20.10/3.01  fof(f46,plain,(
% 20.10/3.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 20.10/3.01    inference(definition_unfolding,[],[f32,f35])).
% 20.10/3.01  
% 20.10/3.01  fof(f41,plain,(
% 20.10/3.01    v1_relat_1(sK1)),
% 20.10/3.01    inference(cnf_transformation,[],[f28])).
% 20.10/3.01  
% 20.10/3.01  fof(f5,axiom,(
% 20.10/3.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f13,plain,(
% 20.10/3.01    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 20.10/3.01    inference(ennf_transformation,[],[f5])).
% 20.10/3.01  
% 20.10/3.01  fof(f36,plain,(
% 20.10/3.01    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f13])).
% 20.10/3.01  
% 20.10/3.01  fof(f9,axiom,(
% 20.10/3.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f20,plain,(
% 20.10/3.01    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 20.10/3.01    inference(ennf_transformation,[],[f9])).
% 20.10/3.01  
% 20.10/3.01  fof(f21,plain,(
% 20.10/3.01    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 20.10/3.01    inference(flattening,[],[f20])).
% 20.10/3.01  
% 20.10/3.01  fof(f40,plain,(
% 20.10/3.01    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f21])).
% 20.10/3.01  
% 20.10/3.01  fof(f42,plain,(
% 20.10/3.01    v1_funct_1(sK1)),
% 20.10/3.01    inference(cnf_transformation,[],[f28])).
% 20.10/3.01  
% 20.10/3.01  fof(f7,axiom,(
% 20.10/3.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f16,plain,(
% 20.10/3.01    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 20.10/3.01    inference(ennf_transformation,[],[f7])).
% 20.10/3.01  
% 20.10/3.01  fof(f17,plain,(
% 20.10/3.01    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 20.10/3.01    inference(flattening,[],[f16])).
% 20.10/3.01  
% 20.10/3.01  fof(f38,plain,(
% 20.10/3.01    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f17])).
% 20.10/3.01  
% 20.10/3.01  fof(f6,axiom,(
% 20.10/3.01    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f14,plain,(
% 20.10/3.01    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 20.10/3.01    inference(ennf_transformation,[],[f6])).
% 20.10/3.01  
% 20.10/3.01  fof(f15,plain,(
% 20.10/3.01    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 20.10/3.01    inference(flattening,[],[f14])).
% 20.10/3.01  
% 20.10/3.01  fof(f37,plain,(
% 20.10/3.01    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f15])).
% 20.10/3.01  
% 20.10/3.01  fof(f1,axiom,(
% 20.10/3.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f24,plain,(
% 20.10/3.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 20.10/3.01    inference(nnf_transformation,[],[f1])).
% 20.10/3.01  
% 20.10/3.01  fof(f25,plain,(
% 20.10/3.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 20.10/3.01    inference(flattening,[],[f24])).
% 20.10/3.01  
% 20.10/3.01  fof(f31,plain,(
% 20.10/3.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f25])).
% 20.10/3.01  
% 20.10/3.01  fof(f44,plain,(
% 20.10/3.01    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0),
% 20.10/3.01    inference(cnf_transformation,[],[f28])).
% 20.10/3.01  
% 20.10/3.01  fof(f8,axiom,(
% 20.10/3.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 20.10/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.10/3.01  
% 20.10/3.01  fof(f18,plain,(
% 20.10/3.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 20.10/3.01    inference(ennf_transformation,[],[f8])).
% 20.10/3.01  
% 20.10/3.01  fof(f19,plain,(
% 20.10/3.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 20.10/3.01    inference(flattening,[],[f18])).
% 20.10/3.01  
% 20.10/3.01  fof(f39,plain,(
% 20.10/3.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 20.10/3.01    inference(cnf_transformation,[],[f19])).
% 20.10/3.01  
% 20.10/3.01  cnf(c_12,negated_conjecture,
% 20.10/3.01      ( r1_tarski(sK0,k2_relat_1(sK1)) ),
% 20.10/3.01      inference(cnf_transformation,[],[f43]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_577,plain,
% 20.10/3.01      ( r1_tarski(sK0,k2_relat_1(sK1)) = iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_5,plain,
% 20.10/3.01      ( ~ r1_tarski(X0,X1) | r1_tarski(k6_subset_1(X0,X2),X1) ),
% 20.10/3.01      inference(cnf_transformation,[],[f47]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_583,plain,
% 20.10/3.01      ( r1_tarski(X0,X1) != iProver_top
% 20.10/3.01      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_3,plain,
% 20.10/3.01      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 20.10/3.01      inference(cnf_transformation,[],[f45]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_585,plain,
% 20.10/3.01      ( k6_subset_1(X0,X1) = k1_xboole_0
% 20.10/3.01      | r1_tarski(X0,X1) != iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_1096,plain,
% 20.10/3.01      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 20.10/3.01      | r1_tarski(X0,X2) != iProver_top ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_583,c_585]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_2285,plain,
% 20.10/3.01      ( k6_subset_1(k6_subset_1(sK0,X0),k2_relat_1(sK1)) = k1_xboole_0 ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_577,c_1096]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_4,plain,
% 20.10/3.01      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 20.10/3.01      inference(cnf_transformation,[],[f46]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_584,plain,
% 20.10/3.01      ( k6_subset_1(X0,X1) != k1_xboole_0
% 20.10/3.01      | r1_tarski(X0,X1) = iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_2713,plain,
% 20.10/3.01      ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1)) = iProver_top ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_2285,c_584]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_14,negated_conjecture,
% 20.10/3.01      ( v1_relat_1(sK1) ),
% 20.10/3.01      inference(cnf_transformation,[],[f41]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_575,plain,
% 20.10/3.01      ( v1_relat_1(sK1) = iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_6,plain,
% 20.10/3.01      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 20.10/3.01      inference(cnf_transformation,[],[f36]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_582,plain,
% 20.10/3.01      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 20.10/3.01      | v1_relat_1(X0) != iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_10,plain,
% 20.10/3.01      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 20.10/3.01      | ~ r1_tarski(X0,k1_relat_1(X1))
% 20.10/3.01      | ~ v1_relat_1(X1) ),
% 20.10/3.01      inference(cnf_transformation,[],[f40]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_578,plain,
% 20.10/3.01      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 20.10/3.01      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 20.10/3.01      | v1_relat_1(X1) != iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_986,plain,
% 20.10/3.01      ( k6_subset_1(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = k1_xboole_0
% 20.10/3.01      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 20.10/3.01      | v1_relat_1(X1) != iProver_top ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_578,c_585]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_1491,plain,
% 20.10/3.01      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,k9_relat_1(X0,k10_relat_1(X0,X1)))) = k1_xboole_0
% 20.10/3.01      | v1_relat_1(X0) != iProver_top ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_582,c_986]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_5696,plain,
% 20.10/3.01      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k1_xboole_0 ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_575,c_1491]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_13,negated_conjecture,
% 20.10/3.01      ( v1_funct_1(sK1) ),
% 20.10/3.01      inference(cnf_transformation,[],[f42]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_576,plain,
% 20.10/3.01      ( v1_funct_1(sK1) = iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_8,plain,
% 20.10/3.01      ( ~ v1_funct_1(X0)
% 20.10/3.01      | ~ v1_relat_1(X0)
% 20.10/3.01      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 20.10/3.01      inference(cnf_transformation,[],[f38]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_580,plain,
% 20.10/3.01      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 20.10/3.01      | v1_funct_1(X0) != iProver_top
% 20.10/3.01      | v1_relat_1(X0) != iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_1369,plain,
% 20.10/3.01      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
% 20.10/3.01      | v1_relat_1(sK1) != iProver_top ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_576,c_580]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_15,plain,
% 20.10/3.01      ( v1_relat_1(sK1) = iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_5030,plain,
% 20.10/3.01      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 20.10/3.01      inference(global_propositional_subsumption,
% 20.10/3.01                [status(thm)],
% 20.10/3.01                [c_1369,c_15]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_5809,plain,
% 20.10/3.01      ( k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k1_xboole_0 ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_5696,c_5030]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_7,plain,
% 20.10/3.01      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 20.10/3.01      | ~ v1_relat_1(X1)
% 20.10/3.01      | k10_relat_1(X1,X0) != k1_xboole_0
% 20.10/3.01      | k1_xboole_0 = X0 ),
% 20.10/3.01      inference(cnf_transformation,[],[f37]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_581,plain,
% 20.10/3.01      ( k10_relat_1(X0,X1) != k1_xboole_0
% 20.10/3.01      | k1_xboole_0 = X1
% 20.10/3.01      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 20.10/3.01      | v1_relat_1(X0) != iProver_top ),
% 20.10/3.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_78750,plain,
% 20.10/3.01      ( k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0
% 20.10/3.01      | r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top
% 20.10/3.01      | v1_relat_1(sK1) != iProver_top ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_5809,c_581]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_79515,plain,
% 20.10/3.01      ( r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top
% 20.10/3.01      | k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0 ),
% 20.10/3.01      inference(global_propositional_subsumption,
% 20.10/3.01                [status(thm)],
% 20.10/3.01                [c_78750,c_15]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_79516,plain,
% 20.10/3.01      ( k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0
% 20.10/3.01      | r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top ),
% 20.10/3.01      inference(renaming,[status(thm)],[c_79515]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_79525,plain,
% 20.10/3.01      ( k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) = k1_xboole_0 ),
% 20.10/3.01      inference(superposition,[status(thm)],[c_2713,c_79516]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_0,plain,
% 20.10/3.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 20.10/3.01      inference(cnf_transformation,[],[f31]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_11,negated_conjecture,
% 20.10/3.01      ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
% 20.10/3.01      inference(cnf_transformation,[],[f44]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_1110,plain,
% 20.10/3.01      ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
% 20.10/3.01      | ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
% 20.10/3.01      inference(resolution,[status(thm)],[c_0,c_11]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_9,plain,
% 20.10/3.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 20.10/3.01      | ~ v1_funct_1(X0)
% 20.10/3.01      | ~ v1_relat_1(X0) ),
% 20.10/3.01      inference(cnf_transformation,[],[f39]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_1277,plain,
% 20.10/3.01      ( ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
% 20.10/3.01      | ~ v1_funct_1(sK1)
% 20.10/3.01      | ~ v1_relat_1(sK1) ),
% 20.10/3.01      inference(resolution,[status(thm)],[c_1110,c_9]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(c_773,plain,
% 20.10/3.01      ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
% 20.10/3.01      | k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) != k1_xboole_0 ),
% 20.10/3.01      inference(instantiation,[status(thm)],[c_4]) ).
% 20.10/3.01  
% 20.10/3.01  cnf(contradiction,plain,
% 20.10/3.01      ( $false ),
% 20.10/3.01      inference(minisat,[status(thm)],[c_79525,c_1277,c_773,c_13,c_14]) ).
% 20.10/3.01  
% 20.10/3.01  
% 20.10/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 20.10/3.01  
% 20.10/3.01  ------                               Statistics
% 20.10/3.01  
% 20.10/3.01  ------ Selected
% 20.10/3.01  
% 20.10/3.01  total_time:                             2.417
% 20.10/3.01  
%------------------------------------------------------------------------------
