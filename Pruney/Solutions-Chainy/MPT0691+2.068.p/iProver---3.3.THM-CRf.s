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
% DateTime   : Thu Dec  3 11:51:50 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 511 expanded)
%              Number of clauses        :   52 ( 173 expanded)
%              Number of leaves         :   10 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :  158 (1261 expanded)
%              Number of equality atoms :   80 ( 262 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f44])).

fof(f67,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_801,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_806,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5135,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_806])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_997,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6156,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5135,c_22,c_21,c_997])).

cnf(c_800,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_814,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_804,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1124,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_804])).

cnf(c_6903,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_800,c_1124])).

cnf(c_7203,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),sK0) = k7_relat_1(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_6156,c_6903])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_811,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1497,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_811])).

cnf(c_8990,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_800,c_1497])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_813,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2539,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_800,c_813])).

cnf(c_8992,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_8990,c_2539])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k10_relat_1(X0,X2)) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_803,plain,
    ( k3_xboole_0(X0,k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1288,plain,
    ( k3_xboole_0(X0,k10_relat_1(k7_relat_1(X1,X2),X3)) = k10_relat_1(k7_relat_1(k7_relat_1(X1,X2),X0),X3)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_803])).

cnf(c_7654,plain,
    ( k3_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X1),X2)) = k10_relat_1(k7_relat_1(k7_relat_1(sK1,X1),X0),X2) ),
    inference(superposition,[status(thm)],[c_800,c_1288])).

cnf(c_10486,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),k9_relat_1(sK1,X0)) = k3_xboole_0(X1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_8992,c_7654])).

cnf(c_10599,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_7203,c_10486])).

cnf(c_10638,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_10599,c_6156])).

cnf(c_11951,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_10638,c_8992])).

cnf(c_11956,plain,
    ( k3_xboole_0(sK0,sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_11951,c_6156])).

cnf(c_11958,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_11956,c_10638])).

cnf(c_1289,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,X1)) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_800,c_803])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_807,plain,
    ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3011,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = k1_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_807])).

cnf(c_24059,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) ),
    inference(superposition,[status(thm)],[c_800,c_3011])).

cnf(c_24286,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_6156,c_24059])).

cnf(c_14,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_808,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_24876,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24286,c_808])).

cnf(c_23,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13032,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_13033,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13032])).

cnf(c_30582,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24876,c_23,c_13033])).

cnf(c_30589,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),X0),k10_relat_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_30582])).

cnf(c_30932,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11958,c_30589])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30932,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:47:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.74/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.49  
% 7.74/1.49  ------  iProver source info
% 7.74/1.49  
% 7.74/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.49  git: non_committed_changes: false
% 7.74/1.49  git: last_make_outside_of_git: false
% 7.74/1.49  
% 7.74/1.49  ------ 
% 7.74/1.49  
% 7.74/1.49  ------ Input Options
% 7.74/1.49  
% 7.74/1.49  --out_options                           all
% 7.74/1.49  --tptp_safe_out                         true
% 7.74/1.49  --problem_path                          ""
% 7.74/1.49  --include_path                          ""
% 7.74/1.49  --clausifier                            res/vclausify_rel
% 7.74/1.49  --clausifier_options                    --mode clausify
% 7.74/1.49  --stdin                                 false
% 7.74/1.49  --stats_out                             all
% 7.74/1.49  
% 7.74/1.49  ------ General Options
% 7.74/1.49  
% 7.74/1.49  --fof                                   false
% 7.74/1.49  --time_out_real                         305.
% 7.74/1.49  --time_out_virtual                      -1.
% 7.74/1.49  --symbol_type_check                     false
% 7.74/1.49  --clausify_out                          false
% 7.74/1.49  --sig_cnt_out                           false
% 7.74/1.49  --trig_cnt_out                          false
% 7.74/1.49  --trig_cnt_out_tolerance                1.
% 7.74/1.49  --trig_cnt_out_sk_spl                   false
% 7.74/1.49  --abstr_cl_out                          false
% 7.74/1.49  
% 7.74/1.49  ------ Global Options
% 7.74/1.49  
% 7.74/1.49  --schedule                              default
% 7.74/1.49  --add_important_lit                     false
% 7.74/1.49  --prop_solver_per_cl                    1000
% 7.74/1.49  --min_unsat_core                        false
% 7.74/1.49  --soft_assumptions                      false
% 7.74/1.49  --soft_lemma_size                       3
% 7.74/1.49  --prop_impl_unit_size                   0
% 7.74/1.49  --prop_impl_unit                        []
% 7.74/1.49  --share_sel_clauses                     true
% 7.74/1.49  --reset_solvers                         false
% 7.74/1.49  --bc_imp_inh                            [conj_cone]
% 7.74/1.49  --conj_cone_tolerance                   3.
% 7.74/1.49  --extra_neg_conj                        none
% 7.74/1.49  --large_theory_mode                     true
% 7.74/1.49  --prolific_symb_bound                   200
% 7.74/1.49  --lt_threshold                          2000
% 7.74/1.49  --clause_weak_htbl                      true
% 7.74/1.49  --gc_record_bc_elim                     false
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing Options
% 7.74/1.49  
% 7.74/1.49  --preprocessing_flag                    true
% 7.74/1.49  --time_out_prep_mult                    0.1
% 7.74/1.49  --splitting_mode                        input
% 7.74/1.49  --splitting_grd                         true
% 7.74/1.49  --splitting_cvd                         false
% 7.74/1.49  --splitting_cvd_svl                     false
% 7.74/1.49  --splitting_nvd                         32
% 7.74/1.49  --sub_typing                            true
% 7.74/1.49  --prep_gs_sim                           true
% 7.74/1.49  --prep_unflatten                        true
% 7.74/1.49  --prep_res_sim                          true
% 7.74/1.49  --prep_upred                            true
% 7.74/1.49  --prep_sem_filter                       exhaustive
% 7.74/1.49  --prep_sem_filter_out                   false
% 7.74/1.49  --pred_elim                             true
% 7.74/1.49  --res_sim_input                         true
% 7.74/1.49  --eq_ax_congr_red                       true
% 7.74/1.49  --pure_diseq_elim                       true
% 7.74/1.49  --brand_transform                       false
% 7.74/1.49  --non_eq_to_eq                          false
% 7.74/1.49  --prep_def_merge                        true
% 7.74/1.49  --prep_def_merge_prop_impl              false
% 7.74/1.49  --prep_def_merge_mbd                    true
% 7.74/1.49  --prep_def_merge_tr_red                 false
% 7.74/1.49  --prep_def_merge_tr_cl                  false
% 7.74/1.49  --smt_preprocessing                     true
% 7.74/1.49  --smt_ac_axioms                         fast
% 7.74/1.49  --preprocessed_out                      false
% 7.74/1.49  --preprocessed_stats                    false
% 7.74/1.49  
% 7.74/1.49  ------ Abstraction refinement Options
% 7.74/1.49  
% 7.74/1.49  --abstr_ref                             []
% 7.74/1.49  --abstr_ref_prep                        false
% 7.74/1.49  --abstr_ref_until_sat                   false
% 7.74/1.49  --abstr_ref_sig_restrict                funpre
% 7.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.49  --abstr_ref_under                       []
% 7.74/1.49  
% 7.74/1.49  ------ SAT Options
% 7.74/1.49  
% 7.74/1.49  --sat_mode                              false
% 7.74/1.49  --sat_fm_restart_options                ""
% 7.74/1.49  --sat_gr_def                            false
% 7.74/1.49  --sat_epr_types                         true
% 7.74/1.49  --sat_non_cyclic_types                  false
% 7.74/1.49  --sat_finite_models                     false
% 7.74/1.49  --sat_fm_lemmas                         false
% 7.74/1.49  --sat_fm_prep                           false
% 7.74/1.49  --sat_fm_uc_incr                        true
% 7.74/1.49  --sat_out_model                         small
% 7.74/1.49  --sat_out_clauses                       false
% 7.74/1.49  
% 7.74/1.49  ------ QBF Options
% 7.74/1.49  
% 7.74/1.49  --qbf_mode                              false
% 7.74/1.49  --qbf_elim_univ                         false
% 7.74/1.49  --qbf_dom_inst                          none
% 7.74/1.49  --qbf_dom_pre_inst                      false
% 7.74/1.49  --qbf_sk_in                             false
% 7.74/1.49  --qbf_pred_elim                         true
% 7.74/1.49  --qbf_split                             512
% 7.74/1.49  
% 7.74/1.49  ------ BMC1 Options
% 7.74/1.49  
% 7.74/1.49  --bmc1_incremental                      false
% 7.74/1.49  --bmc1_axioms                           reachable_all
% 7.74/1.49  --bmc1_min_bound                        0
% 7.74/1.49  --bmc1_max_bound                        -1
% 7.74/1.49  --bmc1_max_bound_default                -1
% 7.74/1.49  --bmc1_symbol_reachability              true
% 7.74/1.49  --bmc1_property_lemmas                  false
% 7.74/1.49  --bmc1_k_induction                      false
% 7.74/1.49  --bmc1_non_equiv_states                 false
% 7.74/1.49  --bmc1_deadlock                         false
% 7.74/1.49  --bmc1_ucm                              false
% 7.74/1.49  --bmc1_add_unsat_core                   none
% 7.74/1.49  --bmc1_unsat_core_children              false
% 7.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.49  --bmc1_out_stat                         full
% 7.74/1.49  --bmc1_ground_init                      false
% 7.74/1.49  --bmc1_pre_inst_next_state              false
% 7.74/1.49  --bmc1_pre_inst_state                   false
% 7.74/1.49  --bmc1_pre_inst_reach_state             false
% 7.74/1.49  --bmc1_out_unsat_core                   false
% 7.74/1.49  --bmc1_aig_witness_out                  false
% 7.74/1.49  --bmc1_verbose                          false
% 7.74/1.49  --bmc1_dump_clauses_tptp                false
% 7.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.49  --bmc1_dump_file                        -
% 7.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.49  --bmc1_ucm_extend_mode                  1
% 7.74/1.49  --bmc1_ucm_init_mode                    2
% 7.74/1.49  --bmc1_ucm_cone_mode                    none
% 7.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.49  --bmc1_ucm_relax_model                  4
% 7.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.49  --bmc1_ucm_layered_model                none
% 7.74/1.49  --bmc1_ucm_max_lemma_size               10
% 7.74/1.49  
% 7.74/1.49  ------ AIG Options
% 7.74/1.49  
% 7.74/1.49  --aig_mode                              false
% 7.74/1.49  
% 7.74/1.49  ------ Instantiation Options
% 7.74/1.49  
% 7.74/1.49  --instantiation_flag                    true
% 7.74/1.49  --inst_sos_flag                         false
% 7.74/1.49  --inst_sos_phase                        true
% 7.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel_side                     num_symb
% 7.74/1.49  --inst_solver_per_active                1400
% 7.74/1.49  --inst_solver_calls_frac                1.
% 7.74/1.49  --inst_passive_queue_type               priority_queues
% 7.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.49  --inst_passive_queues_freq              [25;2]
% 7.74/1.49  --inst_dismatching                      true
% 7.74/1.49  --inst_eager_unprocessed_to_passive     true
% 7.74/1.49  --inst_prop_sim_given                   true
% 7.74/1.49  --inst_prop_sim_new                     false
% 7.74/1.49  --inst_subs_new                         false
% 7.74/1.49  --inst_eq_res_simp                      false
% 7.74/1.49  --inst_subs_given                       false
% 7.74/1.49  --inst_orphan_elimination               true
% 7.74/1.49  --inst_learning_loop_flag               true
% 7.74/1.49  --inst_learning_start                   3000
% 7.74/1.49  --inst_learning_factor                  2
% 7.74/1.49  --inst_start_prop_sim_after_learn       3
% 7.74/1.49  --inst_sel_renew                        solver
% 7.74/1.49  --inst_lit_activity_flag                true
% 7.74/1.49  --inst_restr_to_given                   false
% 7.74/1.49  --inst_activity_threshold               500
% 7.74/1.49  --inst_out_proof                        true
% 7.74/1.49  
% 7.74/1.49  ------ Resolution Options
% 7.74/1.49  
% 7.74/1.49  --resolution_flag                       true
% 7.74/1.49  --res_lit_sel                           adaptive
% 7.74/1.49  --res_lit_sel_side                      none
% 7.74/1.49  --res_ordering                          kbo
% 7.74/1.49  --res_to_prop_solver                    active
% 7.74/1.49  --res_prop_simpl_new                    false
% 7.74/1.49  --res_prop_simpl_given                  true
% 7.74/1.49  --res_passive_queue_type                priority_queues
% 7.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.49  --res_passive_queues_freq               [15;5]
% 7.74/1.49  --res_forward_subs                      full
% 7.74/1.49  --res_backward_subs                     full
% 7.74/1.49  --res_forward_subs_resolution           true
% 7.74/1.49  --res_backward_subs_resolution          true
% 7.74/1.49  --res_orphan_elimination                true
% 7.74/1.49  --res_time_limit                        2.
% 7.74/1.49  --res_out_proof                         true
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Options
% 7.74/1.49  
% 7.74/1.49  --superposition_flag                    true
% 7.74/1.49  --sup_passive_queue_type                priority_queues
% 7.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.49  --demod_completeness_check              fast
% 7.74/1.49  --demod_use_ground                      true
% 7.74/1.49  --sup_to_prop_solver                    passive
% 7.74/1.49  --sup_prop_simpl_new                    true
% 7.74/1.49  --sup_prop_simpl_given                  true
% 7.74/1.49  --sup_fun_splitting                     false
% 7.74/1.49  --sup_smt_interval                      50000
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Simplification Setup
% 7.74/1.49  
% 7.74/1.49  --sup_indices_passive                   []
% 7.74/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_full_bw                           [BwDemod]
% 7.74/1.49  --sup_immed_triv                        [TrivRules]
% 7.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_immed_bw_main                     []
% 7.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.74/1.49  
% 7.74/1.49  ------ Combination Options
% 7.74/1.49  
% 7.74/1.49  --comb_res_mult                         3
% 7.74/1.49  --comb_sup_mult                         2
% 7.74/1.49  --comb_inst_mult                        10
% 7.74/1.49  
% 7.74/1.49  ------ Debug Options
% 7.74/1.49  
% 7.74/1.49  --dbg_backtrace                         false
% 7.74/1.49  --dbg_dump_prop_clauses                 false
% 7.74/1.49  --dbg_dump_prop_clauses_file            -
% 7.74/1.49  --dbg_out_stat                          false
% 7.74/1.49  ------ Parsing...
% 7.74/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.49  ------ Proving...
% 7.74/1.49  ------ Problem Properties 
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  clauses                                 22
% 7.74/1.49  conjectures                             3
% 7.74/1.49  EPR                                     3
% 7.74/1.49  Horn                                    22
% 7.74/1.49  unary                                   5
% 7.74/1.49  binary                                  13
% 7.74/1.49  lits                                    43
% 7.74/1.49  lits eq                                 10
% 7.74/1.49  fd_pure                                 0
% 7.74/1.49  fd_pseudo                               0
% 7.74/1.49  fd_cond                                 0
% 7.74/1.49  fd_pseudo_cond                          1
% 7.74/1.49  AC symbols                              0
% 7.74/1.49  
% 7.74/1.49  ------ Schedule dynamic 5 is on 
% 7.74/1.49  
% 7.74/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  ------ 
% 7.74/1.49  Current options:
% 7.74/1.49  ------ 
% 7.74/1.49  
% 7.74/1.49  ------ Input Options
% 7.74/1.49  
% 7.74/1.49  --out_options                           all
% 7.74/1.49  --tptp_safe_out                         true
% 7.74/1.49  --problem_path                          ""
% 7.74/1.49  --include_path                          ""
% 7.74/1.49  --clausifier                            res/vclausify_rel
% 7.74/1.49  --clausifier_options                    --mode clausify
% 7.74/1.49  --stdin                                 false
% 7.74/1.49  --stats_out                             all
% 7.74/1.49  
% 7.74/1.49  ------ General Options
% 7.74/1.49  
% 7.74/1.49  --fof                                   false
% 7.74/1.49  --time_out_real                         305.
% 7.74/1.49  --time_out_virtual                      -1.
% 7.74/1.49  --symbol_type_check                     false
% 7.74/1.49  --clausify_out                          false
% 7.74/1.49  --sig_cnt_out                           false
% 7.74/1.49  --trig_cnt_out                          false
% 7.74/1.49  --trig_cnt_out_tolerance                1.
% 7.74/1.49  --trig_cnt_out_sk_spl                   false
% 7.74/1.49  --abstr_cl_out                          false
% 7.74/1.49  
% 7.74/1.49  ------ Global Options
% 7.74/1.49  
% 7.74/1.49  --schedule                              default
% 7.74/1.49  --add_important_lit                     false
% 7.74/1.49  --prop_solver_per_cl                    1000
% 7.74/1.49  --min_unsat_core                        false
% 7.74/1.49  --soft_assumptions                      false
% 7.74/1.49  --soft_lemma_size                       3
% 7.74/1.49  --prop_impl_unit_size                   0
% 7.74/1.49  --prop_impl_unit                        []
% 7.74/1.49  --share_sel_clauses                     true
% 7.74/1.49  --reset_solvers                         false
% 7.74/1.49  --bc_imp_inh                            [conj_cone]
% 7.74/1.49  --conj_cone_tolerance                   3.
% 7.74/1.49  --extra_neg_conj                        none
% 7.74/1.49  --large_theory_mode                     true
% 7.74/1.49  --prolific_symb_bound                   200
% 7.74/1.49  --lt_threshold                          2000
% 7.74/1.49  --clause_weak_htbl                      true
% 7.74/1.49  --gc_record_bc_elim                     false
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing Options
% 7.74/1.49  
% 7.74/1.49  --preprocessing_flag                    true
% 7.74/1.49  --time_out_prep_mult                    0.1
% 7.74/1.49  --splitting_mode                        input
% 7.74/1.49  --splitting_grd                         true
% 7.74/1.49  --splitting_cvd                         false
% 7.74/1.49  --splitting_cvd_svl                     false
% 7.74/1.49  --splitting_nvd                         32
% 7.74/1.49  --sub_typing                            true
% 7.74/1.49  --prep_gs_sim                           true
% 7.74/1.49  --prep_unflatten                        true
% 7.74/1.49  --prep_res_sim                          true
% 7.74/1.49  --prep_upred                            true
% 7.74/1.49  --prep_sem_filter                       exhaustive
% 7.74/1.49  --prep_sem_filter_out                   false
% 7.74/1.49  --pred_elim                             true
% 7.74/1.49  --res_sim_input                         true
% 7.74/1.49  --eq_ax_congr_red                       true
% 7.74/1.49  --pure_diseq_elim                       true
% 7.74/1.49  --brand_transform                       false
% 7.74/1.49  --non_eq_to_eq                          false
% 7.74/1.49  --prep_def_merge                        true
% 7.74/1.49  --prep_def_merge_prop_impl              false
% 7.74/1.49  --prep_def_merge_mbd                    true
% 7.74/1.49  --prep_def_merge_tr_red                 false
% 7.74/1.49  --prep_def_merge_tr_cl                  false
% 7.74/1.49  --smt_preprocessing                     true
% 7.74/1.49  --smt_ac_axioms                         fast
% 7.74/1.49  --preprocessed_out                      false
% 7.74/1.49  --preprocessed_stats                    false
% 7.74/1.49  
% 7.74/1.49  ------ Abstraction refinement Options
% 7.74/1.49  
% 7.74/1.49  --abstr_ref                             []
% 7.74/1.49  --abstr_ref_prep                        false
% 7.74/1.49  --abstr_ref_until_sat                   false
% 7.74/1.49  --abstr_ref_sig_restrict                funpre
% 7.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.49  --abstr_ref_under                       []
% 7.74/1.49  
% 7.74/1.49  ------ SAT Options
% 7.74/1.49  
% 7.74/1.49  --sat_mode                              false
% 7.74/1.49  --sat_fm_restart_options                ""
% 7.74/1.49  --sat_gr_def                            false
% 7.74/1.49  --sat_epr_types                         true
% 7.74/1.49  --sat_non_cyclic_types                  false
% 7.74/1.49  --sat_finite_models                     false
% 7.74/1.49  --sat_fm_lemmas                         false
% 7.74/1.49  --sat_fm_prep                           false
% 7.74/1.49  --sat_fm_uc_incr                        true
% 7.74/1.49  --sat_out_model                         small
% 7.74/1.49  --sat_out_clauses                       false
% 7.74/1.49  
% 7.74/1.49  ------ QBF Options
% 7.74/1.49  
% 7.74/1.49  --qbf_mode                              false
% 7.74/1.49  --qbf_elim_univ                         false
% 7.74/1.49  --qbf_dom_inst                          none
% 7.74/1.49  --qbf_dom_pre_inst                      false
% 7.74/1.49  --qbf_sk_in                             false
% 7.74/1.49  --qbf_pred_elim                         true
% 7.74/1.49  --qbf_split                             512
% 7.74/1.49  
% 7.74/1.49  ------ BMC1 Options
% 7.74/1.49  
% 7.74/1.49  --bmc1_incremental                      false
% 7.74/1.49  --bmc1_axioms                           reachable_all
% 7.74/1.49  --bmc1_min_bound                        0
% 7.74/1.49  --bmc1_max_bound                        -1
% 7.74/1.49  --bmc1_max_bound_default                -1
% 7.74/1.49  --bmc1_symbol_reachability              true
% 7.74/1.49  --bmc1_property_lemmas                  false
% 7.74/1.49  --bmc1_k_induction                      false
% 7.74/1.49  --bmc1_non_equiv_states                 false
% 7.74/1.49  --bmc1_deadlock                         false
% 7.74/1.49  --bmc1_ucm                              false
% 7.74/1.49  --bmc1_add_unsat_core                   none
% 7.74/1.49  --bmc1_unsat_core_children              false
% 7.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.49  --bmc1_out_stat                         full
% 7.74/1.49  --bmc1_ground_init                      false
% 7.74/1.49  --bmc1_pre_inst_next_state              false
% 7.74/1.49  --bmc1_pre_inst_state                   false
% 7.74/1.49  --bmc1_pre_inst_reach_state             false
% 7.74/1.49  --bmc1_out_unsat_core                   false
% 7.74/1.49  --bmc1_aig_witness_out                  false
% 7.74/1.49  --bmc1_verbose                          false
% 7.74/1.49  --bmc1_dump_clauses_tptp                false
% 7.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.49  --bmc1_dump_file                        -
% 7.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.49  --bmc1_ucm_extend_mode                  1
% 7.74/1.49  --bmc1_ucm_init_mode                    2
% 7.74/1.49  --bmc1_ucm_cone_mode                    none
% 7.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.49  --bmc1_ucm_relax_model                  4
% 7.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.49  --bmc1_ucm_layered_model                none
% 7.74/1.49  --bmc1_ucm_max_lemma_size               10
% 7.74/1.49  
% 7.74/1.49  ------ AIG Options
% 7.74/1.49  
% 7.74/1.49  --aig_mode                              false
% 7.74/1.49  
% 7.74/1.49  ------ Instantiation Options
% 7.74/1.49  
% 7.74/1.49  --instantiation_flag                    true
% 7.74/1.49  --inst_sos_flag                         false
% 7.74/1.49  --inst_sos_phase                        true
% 7.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel_side                     none
% 7.74/1.49  --inst_solver_per_active                1400
% 7.74/1.49  --inst_solver_calls_frac                1.
% 7.74/1.49  --inst_passive_queue_type               priority_queues
% 7.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.49  --inst_passive_queues_freq              [25;2]
% 7.74/1.49  --inst_dismatching                      true
% 7.74/1.49  --inst_eager_unprocessed_to_passive     true
% 7.74/1.49  --inst_prop_sim_given                   true
% 7.74/1.49  --inst_prop_sim_new                     false
% 7.74/1.49  --inst_subs_new                         false
% 7.74/1.49  --inst_eq_res_simp                      false
% 7.74/1.49  --inst_subs_given                       false
% 7.74/1.49  --inst_orphan_elimination               true
% 7.74/1.49  --inst_learning_loop_flag               true
% 7.74/1.49  --inst_learning_start                   3000
% 7.74/1.49  --inst_learning_factor                  2
% 7.74/1.49  --inst_start_prop_sim_after_learn       3
% 7.74/1.49  --inst_sel_renew                        solver
% 7.74/1.49  --inst_lit_activity_flag                true
% 7.74/1.49  --inst_restr_to_given                   false
% 7.74/1.49  --inst_activity_threshold               500
% 7.74/1.49  --inst_out_proof                        true
% 7.74/1.49  
% 7.74/1.49  ------ Resolution Options
% 7.74/1.49  
% 7.74/1.49  --resolution_flag                       false
% 7.74/1.49  --res_lit_sel                           adaptive
% 7.74/1.49  --res_lit_sel_side                      none
% 7.74/1.49  --res_ordering                          kbo
% 7.74/1.49  --res_to_prop_solver                    active
% 7.74/1.49  --res_prop_simpl_new                    false
% 7.74/1.49  --res_prop_simpl_given                  true
% 7.74/1.49  --res_passive_queue_type                priority_queues
% 7.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.49  --res_passive_queues_freq               [15;5]
% 7.74/1.49  --res_forward_subs                      full
% 7.74/1.49  --res_backward_subs                     full
% 7.74/1.49  --res_forward_subs_resolution           true
% 7.74/1.49  --res_backward_subs_resolution          true
% 7.74/1.49  --res_orphan_elimination                true
% 7.74/1.49  --res_time_limit                        2.
% 7.74/1.49  --res_out_proof                         true
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Options
% 7.74/1.49  
% 7.74/1.49  --superposition_flag                    true
% 7.74/1.49  --sup_passive_queue_type                priority_queues
% 7.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.49  --demod_completeness_check              fast
% 7.74/1.49  --demod_use_ground                      true
% 7.74/1.49  --sup_to_prop_solver                    passive
% 7.74/1.49  --sup_prop_simpl_new                    true
% 7.74/1.49  --sup_prop_simpl_given                  true
% 7.74/1.49  --sup_fun_splitting                     false
% 7.74/1.49  --sup_smt_interval                      50000
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Simplification Setup
% 7.74/1.49  
% 7.74/1.49  --sup_indices_passive                   []
% 7.74/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_full_bw                           [BwDemod]
% 7.74/1.49  --sup_immed_triv                        [TrivRules]
% 7.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_immed_bw_main                     []
% 7.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.74/1.49  
% 7.74/1.49  ------ Combination Options
% 7.74/1.49  
% 7.74/1.49  --comb_res_mult                         3
% 7.74/1.49  --comb_sup_mult                         2
% 7.74/1.49  --comb_inst_mult                        10
% 7.74/1.49  
% 7.74/1.49  ------ Debug Options
% 7.74/1.49  
% 7.74/1.49  --dbg_backtrace                         false
% 7.74/1.49  --dbg_dump_prop_clauses                 false
% 7.74/1.49  --dbg_dump_prop_clauses_file            -
% 7.74/1.49  --dbg_out_stat                          false
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  ------ Proving...
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  % SZS status Theorem for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  fof(f19,conjecture,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f20,negated_conjecture,(
% 7.74/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.74/1.49    inference(negated_conjecture,[],[f19])).
% 7.74/1.49  
% 7.74/1.49  fof(f40,plain,(
% 7.74/1.49    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f20])).
% 7.74/1.49  
% 7.74/1.49  fof(f41,plain,(
% 7.74/1.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 7.74/1.49    inference(flattening,[],[f40])).
% 7.74/1.49  
% 7.74/1.49  fof(f44,plain,(
% 7.74/1.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f45,plain,(
% 7.74/1.49    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f44])).
% 7.74/1.49  
% 7.74/1.49  fof(f67,plain,(
% 7.74/1.49    r1_tarski(sK0,k1_relat_1(sK1))),
% 7.74/1.49    inference(cnf_transformation,[],[f45])).
% 7.74/1.49  
% 7.74/1.49  fof(f15,axiom,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f34,plain,(
% 7.74/1.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f15])).
% 7.74/1.49  
% 7.74/1.49  fof(f35,plain,(
% 7.74/1.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(flattening,[],[f34])).
% 7.74/1.49  
% 7.74/1.49  fof(f62,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f66,plain,(
% 7.74/1.49    v1_relat_1(sK1)),
% 7.74/1.49    inference(cnf_transformation,[],[f45])).
% 7.74/1.49  
% 7.74/1.49  fof(f7,axiom,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f26,plain,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.74/1.49    inference(ennf_transformation,[],[f7])).
% 7.74/1.49  
% 7.74/1.49  fof(f54,plain,(
% 7.74/1.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f26])).
% 7.74/1.49  
% 7.74/1.49  fof(f17,axiom,(
% 7.74/1.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f38,plain,(
% 7.74/1.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 7.74/1.49    inference(ennf_transformation,[],[f17])).
% 7.74/1.49  
% 7.74/1.49  fof(f64,plain,(
% 7.74/1.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f38])).
% 7.74/1.49  
% 7.74/1.49  fof(f10,axiom,(
% 7.74/1.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f29,plain,(
% 7.74/1.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 7.74/1.49    inference(ennf_transformation,[],[f10])).
% 7.74/1.49  
% 7.74/1.49  fof(f57,plain,(
% 7.74/1.49    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f29])).
% 7.74/1.49  
% 7.74/1.49  fof(f8,axiom,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f27,plain,(
% 7.74/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f8])).
% 7.74/1.49  
% 7.74/1.49  fof(f55,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f27])).
% 7.74/1.49  
% 7.74/1.49  fof(f18,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f39,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 7.74/1.49    inference(ennf_transformation,[],[f18])).
% 7.74/1.49  
% 7.74/1.49  fof(f65,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f39])).
% 7.74/1.49  
% 7.74/1.49  fof(f14,axiom,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f33,plain,(
% 7.74/1.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f14])).
% 7.74/1.49  
% 7.74/1.49  fof(f61,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f33])).
% 7.74/1.49  
% 7.74/1.49  fof(f13,axiom,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f32,plain,(
% 7.74/1.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f13])).
% 7.74/1.49  
% 7.74/1.49  fof(f60,plain,(
% 7.74/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f32])).
% 7.74/1.49  
% 7.74/1.49  fof(f68,plain,(
% 7.74/1.49    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 7.74/1.49    inference(cnf_transformation,[],[f45])).
% 7.74/1.49  
% 7.74/1.49  cnf(c_21,negated_conjecture,
% 7.74/1.49      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_801,plain,
% 7.74/1.49      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_16,plain,
% 7.74/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.74/1.49      | ~ v1_relat_1(X1)
% 7.74/1.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.74/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_806,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.74/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5135,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 7.74/1.49      | v1_relat_1(sK1) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_801,c_806]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_22,negated_conjecture,
% 7.74/1.49      ( v1_relat_1(sK1) ),
% 7.74/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_997,plain,
% 7.74/1.49      ( ~ r1_tarski(sK0,k1_relat_1(sK1))
% 7.74/1.49      | ~ v1_relat_1(sK1)
% 7.74/1.49      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6156,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_5135,c_22,c_21,c_997]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_800,plain,
% 7.74/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8,plain,
% 7.74/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_814,plain,
% 7.74/1.49      ( v1_relat_1(X0) != iProver_top
% 7.74/1.49      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_18,plain,
% 7.74/1.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 7.74/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_804,plain,
% 7.74/1.49      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1124,plain,
% 7.74/1.49      ( k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(X0,X1)
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_814,c_804]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6903,plain,
% 7.74/1.49      ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_800,c_1124]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7203,plain,
% 7.74/1.49      ( k7_relat_1(k7_relat_1(sK1,sK0),sK0) = k7_relat_1(sK1,sK0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_6156,c_6903]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_11,plain,
% 7.74/1.49      ( ~ v1_relat_1(X0)
% 7.74/1.49      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_811,plain,
% 7.74/1.49      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1497,plain,
% 7.74/1.49      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_814,c_811]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8990,plain,
% 7.74/1.49      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_800,c_1497]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9,plain,
% 7.74/1.49      ( ~ v1_relat_1(X0)
% 7.74/1.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.74/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_813,plain,
% 7.74/1.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2539,plain,
% 7.74/1.49      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_800,c_813]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8992,plain,
% 7.74/1.49      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_8990,c_2539]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_19,plain,
% 7.74/1.49      ( ~ v1_relat_1(X0)
% 7.74/1.49      | k3_xboole_0(X1,k10_relat_1(X0,X2)) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.74/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_803,plain,
% 7.74/1.49      ( k3_xboole_0(X0,k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.74/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1288,plain,
% 7.74/1.49      ( k3_xboole_0(X0,k10_relat_1(k7_relat_1(X1,X2),X3)) = k10_relat_1(k7_relat_1(k7_relat_1(X1,X2),X0),X3)
% 7.74/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_814,c_803]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7654,plain,
% 7.74/1.49      ( k3_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X1),X2)) = k10_relat_1(k7_relat_1(k7_relat_1(sK1,X1),X0),X2) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_800,c_1288]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_10486,plain,
% 7.74/1.49      ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),k9_relat_1(sK1,X0)) = k3_xboole_0(X1,k1_relat_1(k7_relat_1(sK1,X0))) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_8992,c_7654]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_10599,plain,
% 7.74/1.49      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_7203,c_10486]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_10638,plain,
% 7.74/1.49      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,sK0) ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_10599,c_6156]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_11951,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(sK0,sK0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_10638,c_8992]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_11956,plain,
% 7.74/1.49      ( k3_xboole_0(sK0,sK0) = sK0 ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_11951,c_6156]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_11958,plain,
% 7.74/1.49      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = sK0 ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_11956,c_10638]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1289,plain,
% 7.74/1.49      ( k3_xboole_0(X0,k10_relat_1(sK1,X1)) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_800,c_803]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_15,plain,
% 7.74/1.49      ( ~ v1_relat_1(X0)
% 7.74/1.49      | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_807,plain,
% 7.74/1.49      ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1))
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3011,plain,
% 7.74/1.49      ( k3_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = k1_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2))
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_814,c_807]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_24059,plain,
% 7.74/1.49      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_800,c_3011]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_24286,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)) = k3_xboole_0(sK0,X0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_6156,c_24059]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_14,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_808,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_24876,plain,
% 7.74/1.49      ( r1_tarski(k3_xboole_0(sK0,X0),X0) = iProver_top
% 7.74/1.49      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_24286,c_808]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_23,plain,
% 7.74/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_13032,plain,
% 7.74/1.49      ( v1_relat_1(k7_relat_1(sK1,sK0)) | ~ v1_relat_1(sK1) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_13033,plain,
% 7.74/1.49      ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
% 7.74/1.49      | v1_relat_1(sK1) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_13032]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_30582,plain,
% 7.74/1.49      ( r1_tarski(k3_xboole_0(sK0,X0),X0) = iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_24876,c_23,c_13033]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_30589,plain,
% 7.74/1.49      ( r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),X0),k10_relat_1(sK1,X0)) = iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1289,c_30582]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_30932,plain,
% 7.74/1.49      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_11958,c_30589]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_20,negated_conjecture,
% 7.74/1.49      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 7.74/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_25,plain,
% 7.74/1.49      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(contradiction,plain,
% 7.74/1.49      ( $false ),
% 7.74/1.49      inference(minisat,[status(thm)],[c_30932,c_25]) ).
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  ------                               Statistics
% 7.74/1.49  
% 7.74/1.49  ------ General
% 7.74/1.49  
% 7.74/1.49  abstr_ref_over_cycles:                  0
% 7.74/1.49  abstr_ref_under_cycles:                 0
% 7.74/1.49  gc_basic_clause_elim:                   0
% 7.74/1.49  forced_gc_time:                         0
% 7.74/1.49  parsing_time:                           0.01
% 7.74/1.49  unif_index_cands_time:                  0.
% 7.74/1.49  unif_index_add_time:                    0.
% 7.74/1.49  orderings_time:                         0.
% 7.74/1.49  out_proof_time:                         0.011
% 7.74/1.49  total_time:                             0.773
% 7.74/1.49  num_of_symbols:                         42
% 7.74/1.49  num_of_terms:                           40167
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing
% 7.74/1.49  
% 7.74/1.49  num_of_splits:                          0
% 7.74/1.49  num_of_split_atoms:                     0
% 7.74/1.49  num_of_reused_defs:                     0
% 7.74/1.49  num_eq_ax_congr_red:                    9
% 7.74/1.49  num_of_sem_filtered_clauses:            1
% 7.74/1.49  num_of_subtypes:                        0
% 7.74/1.49  monotx_restored_types:                  0
% 7.74/1.49  sat_num_of_epr_types:                   0
% 7.74/1.49  sat_num_of_non_cyclic_types:            0
% 7.74/1.49  sat_guarded_non_collapsed_types:        0
% 7.74/1.49  num_pure_diseq_elim:                    0
% 7.74/1.49  simp_replaced_by:                       0
% 7.74/1.49  res_preprocessed:                       109
% 7.74/1.49  prep_upred:                             0
% 7.74/1.49  prep_unflattend:                        0
% 7.74/1.49  smt_new_axioms:                         0
% 7.74/1.49  pred_elim_cands:                        2
% 7.74/1.49  pred_elim:                              0
% 7.74/1.49  pred_elim_cl:                           0
% 7.74/1.49  pred_elim_cycles:                       2
% 7.74/1.49  merged_defs:                            0
% 7.74/1.49  merged_defs_ncl:                        0
% 7.74/1.49  bin_hyper_res:                          0
% 7.74/1.49  prep_cycles:                            4
% 7.74/1.49  pred_elim_time:                         0.
% 7.74/1.49  splitting_time:                         0.
% 7.74/1.49  sem_filter_time:                        0.
% 7.74/1.49  monotx_time:                            0.001
% 7.74/1.49  subtype_inf_time:                       0.
% 7.74/1.49  
% 7.74/1.49  ------ Problem properties
% 7.74/1.49  
% 7.74/1.49  clauses:                                22
% 7.74/1.49  conjectures:                            3
% 7.74/1.49  epr:                                    3
% 7.74/1.49  horn:                                   22
% 7.74/1.49  ground:                                 3
% 7.74/1.49  unary:                                  5
% 7.74/1.49  binary:                                 13
% 7.74/1.49  lits:                                   43
% 7.74/1.49  lits_eq:                                10
% 7.74/1.49  fd_pure:                                0
% 7.74/1.49  fd_pseudo:                              0
% 7.74/1.49  fd_cond:                                0
% 7.74/1.49  fd_pseudo_cond:                         1
% 7.74/1.49  ac_symbols:                             0
% 7.74/1.49  
% 7.74/1.49  ------ Propositional Solver
% 7.74/1.49  
% 7.74/1.49  prop_solver_calls:                      32
% 7.74/1.49  prop_fast_solver_calls:                 724
% 7.74/1.49  smt_solver_calls:                       0
% 7.74/1.49  smt_fast_solver_calls:                  0
% 7.74/1.49  prop_num_of_clauses:                    13607
% 7.74/1.49  prop_preprocess_simplified:             24444
% 7.74/1.49  prop_fo_subsumed:                       7
% 7.74/1.49  prop_solver_time:                       0.
% 7.74/1.49  smt_solver_time:                        0.
% 7.74/1.49  smt_fast_solver_time:                   0.
% 7.74/1.49  prop_fast_solver_time:                  0.
% 7.74/1.49  prop_unsat_core_time:                   0.002
% 7.74/1.49  
% 7.74/1.49  ------ QBF
% 7.74/1.49  
% 7.74/1.49  qbf_q_res:                              0
% 7.74/1.49  qbf_num_tautologies:                    0
% 7.74/1.49  qbf_prep_cycles:                        0
% 7.74/1.49  
% 7.74/1.49  ------ BMC1
% 7.74/1.49  
% 7.74/1.49  bmc1_current_bound:                     -1
% 7.74/1.49  bmc1_last_solved_bound:                 -1
% 7.74/1.49  bmc1_unsat_core_size:                   -1
% 7.74/1.49  bmc1_unsat_core_parents_size:           -1
% 7.74/1.49  bmc1_merge_next_fun:                    0
% 7.74/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.74/1.49  
% 7.74/1.49  ------ Instantiation
% 7.74/1.49  
% 7.74/1.49  inst_num_of_clauses:                    3730
% 7.74/1.49  inst_num_in_passive:                    1512
% 7.74/1.49  inst_num_in_active:                     806
% 7.74/1.49  inst_num_in_unprocessed:                1413
% 7.74/1.49  inst_num_of_loops:                      910
% 7.74/1.49  inst_num_of_learning_restarts:          0
% 7.74/1.49  inst_num_moves_active_passive:          100
% 7.74/1.49  inst_lit_activity:                      0
% 7.74/1.49  inst_lit_activity_moves:                2
% 7.74/1.49  inst_num_tautologies:                   0
% 7.74/1.49  inst_num_prop_implied:                  0
% 7.74/1.49  inst_num_existing_simplified:           0
% 7.74/1.49  inst_num_eq_res_simplified:             0
% 7.74/1.49  inst_num_child_elim:                    0
% 7.74/1.49  inst_num_of_dismatching_blockings:      3006
% 7.74/1.49  inst_num_of_non_proper_insts:           4176
% 7.74/1.49  inst_num_of_duplicates:                 0
% 7.74/1.49  inst_inst_num_from_inst_to_res:         0
% 7.74/1.49  inst_dismatching_checking_time:         0.
% 7.74/1.49  
% 7.74/1.49  ------ Resolution
% 7.74/1.49  
% 7.74/1.49  res_num_of_clauses:                     0
% 7.74/1.49  res_num_in_passive:                     0
% 7.74/1.49  res_num_in_active:                      0
% 7.74/1.49  res_num_of_loops:                       113
% 7.74/1.49  res_forward_subset_subsumed:            393
% 7.74/1.49  res_backward_subset_subsumed:           6
% 7.74/1.49  res_forward_subsumed:                   0
% 7.74/1.49  res_backward_subsumed:                  0
% 7.74/1.49  res_forward_subsumption_resolution:     0
% 7.74/1.49  res_backward_subsumption_resolution:    0
% 7.74/1.49  res_clause_to_clause_subsumption:       4161
% 7.74/1.49  res_orphan_elimination:                 0
% 7.74/1.49  res_tautology_del:                      64
% 7.74/1.49  res_num_eq_res_simplified:              0
% 7.74/1.49  res_num_sel_changes:                    0
% 7.74/1.49  res_moves_from_active_to_pass:          0
% 7.74/1.49  
% 7.74/1.49  ------ Superposition
% 7.74/1.49  
% 7.74/1.49  sup_time_total:                         0.
% 7.74/1.49  sup_time_generating:                    0.
% 7.74/1.49  sup_time_sim_full:                      0.
% 7.74/1.49  sup_time_sim_immed:                     0.
% 7.74/1.49  
% 7.74/1.49  sup_num_of_clauses:                     655
% 7.74/1.49  sup_num_in_active:                      173
% 7.74/1.49  sup_num_in_passive:                     482
% 7.74/1.49  sup_num_of_loops:                       181
% 7.74/1.49  sup_fw_superposition:                   1094
% 7.74/1.49  sup_bw_superposition:                   816
% 7.74/1.49  sup_immediate_simplified:               668
% 7.74/1.49  sup_given_eliminated:                   1
% 7.74/1.49  comparisons_done:                       0
% 7.74/1.49  comparisons_avoided:                    0
% 7.74/1.49  
% 7.74/1.49  ------ Simplifications
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  sim_fw_subset_subsumed:                 25
% 7.74/1.49  sim_bw_subset_subsumed:                 12
% 7.74/1.49  sim_fw_subsumed:                        152
% 7.74/1.49  sim_bw_subsumed:                        4
% 7.74/1.49  sim_fw_subsumption_res:                 0
% 7.74/1.49  sim_bw_subsumption_res:                 0
% 7.74/1.49  sim_tautology_del:                      66
% 7.74/1.49  sim_eq_tautology_del:                   125
% 7.74/1.49  sim_eq_res_simp:                        0
% 7.74/1.49  sim_fw_demodulated:                     115
% 7.74/1.49  sim_bw_demodulated:                     6
% 7.74/1.49  sim_light_normalised:                   406
% 7.74/1.49  sim_joinable_taut:                      0
% 7.74/1.49  sim_joinable_simp:                      0
% 7.74/1.49  sim_ac_normalised:                      0
% 7.74/1.49  sim_smt_subsumption:                    0
% 7.74/1.49  
%------------------------------------------------------------------------------
