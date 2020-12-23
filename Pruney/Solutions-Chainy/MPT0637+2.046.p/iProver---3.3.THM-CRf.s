%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:03 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   99 (1759 expanded)
%              Number of clauses        :   55 ( 896 expanded)
%              Number of leaves         :   14 ( 339 expanded)
%              Depth                    :   21
%              Number of atoms          :  191 (2927 expanded)
%              Number of equality atoms :  113 (1531 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f30,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).

fof(f56,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f56,f40])).

cnf(c_7,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_522,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_521,plain,
    ( k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2001,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_522,c_521])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2002,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2001,c_11])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_524,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_761,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_524])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_517,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2151,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_517])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_514,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1194,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_522,c_514])).

cnf(c_2155,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2151,c_1194])).

cnf(c_45,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3918,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2155,c_45])).

cnf(c_3919,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3918])).

cnf(c_3928,plain,
    ( k7_relat_1(k6_relat_1(k4_xboole_0(X0,X1)),X0) = k6_relat_1(k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_761,c_3919])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_520,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2166,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_522,c_520])).

cnf(c_10057,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2)
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_522,c_2166])).

cnf(c_10066,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)
    | v1_relat_1(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10057,c_1194])).

cnf(c_12963,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_522,c_10066])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_523,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2050,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_523])).

cnf(c_2812,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2050,c_45])).

cnf(c_2818,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2812,c_522])).

cnf(c_2824,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_2818,c_514])).

cnf(c_12973,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_12963,c_1194,c_2824])).

cnf(c_12991,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,X2)),X1) = k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_3928,c_12973])).

cnf(c_13054,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,X2)),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_12991,c_1194])).

cnf(c_13438,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[status(thm)],[c_2002,c_13054])).

cnf(c_13480,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_13438,c_2002])).

cnf(c_13,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_518,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_13005,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12973,c_518])).

cnf(c_13905,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13005,c_2818])).

cnf(c_13914,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13480,c_13905])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_526,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14562,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0)
    | r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13914,c_526])).

cnf(c_14565,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14562,c_13914])).

cnf(c_14932,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)) = k6_relat_1(k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_14565,c_3928])).

cnf(c_15464,plain,
    ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_14932,c_2002])).

cnf(c_18,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1197,plain,
    ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1194,c_18])).

cnf(c_14744,plain,
    ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_14565,c_1197])).

cnf(c_15560,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_15464,c_14744])).

cnf(c_15938,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15560,c_14565])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.99/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/0.98  
% 3.99/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.99/0.98  
% 3.99/0.98  ------  iProver source info
% 3.99/0.98  
% 3.99/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.99/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.99/0.98  git: non_committed_changes: false
% 3.99/0.98  git: last_make_outside_of_git: false
% 3.99/0.98  
% 3.99/0.98  ------ 
% 3.99/0.98  
% 3.99/0.98  ------ Input Options
% 3.99/0.98  
% 3.99/0.98  --out_options                           all
% 3.99/0.98  --tptp_safe_out                         true
% 3.99/0.98  --problem_path                          ""
% 3.99/0.98  --include_path                          ""
% 3.99/0.98  --clausifier                            res/vclausify_rel
% 3.99/0.98  --clausifier_options                    --mode clausify
% 3.99/0.98  --stdin                                 false
% 3.99/0.98  --stats_out                             all
% 3.99/0.98  
% 3.99/0.98  ------ General Options
% 3.99/0.98  
% 3.99/0.98  --fof                                   false
% 3.99/0.98  --time_out_real                         305.
% 3.99/0.98  --time_out_virtual                      -1.
% 3.99/0.98  --symbol_type_check                     false
% 3.99/0.98  --clausify_out                          false
% 3.99/0.98  --sig_cnt_out                           false
% 3.99/0.98  --trig_cnt_out                          false
% 3.99/0.98  --trig_cnt_out_tolerance                1.
% 3.99/0.98  --trig_cnt_out_sk_spl                   false
% 3.99/0.98  --abstr_cl_out                          false
% 3.99/0.98  
% 3.99/0.98  ------ Global Options
% 3.99/0.98  
% 3.99/0.98  --schedule                              default
% 3.99/0.98  --add_important_lit                     false
% 3.99/0.98  --prop_solver_per_cl                    1000
% 3.99/0.98  --min_unsat_core                        false
% 3.99/0.98  --soft_assumptions                      false
% 3.99/0.98  --soft_lemma_size                       3
% 3.99/0.98  --prop_impl_unit_size                   0
% 3.99/0.98  --prop_impl_unit                        []
% 3.99/0.98  --share_sel_clauses                     true
% 3.99/0.98  --reset_solvers                         false
% 3.99/0.98  --bc_imp_inh                            [conj_cone]
% 3.99/0.98  --conj_cone_tolerance                   3.
% 3.99/0.98  --extra_neg_conj                        none
% 3.99/0.98  --large_theory_mode                     true
% 3.99/0.98  --prolific_symb_bound                   200
% 3.99/0.98  --lt_threshold                          2000
% 3.99/0.98  --clause_weak_htbl                      true
% 3.99/0.98  --gc_record_bc_elim                     false
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing Options
% 3.99/0.98  
% 3.99/0.98  --preprocessing_flag                    true
% 3.99/0.98  --time_out_prep_mult                    0.1
% 3.99/0.98  --splitting_mode                        input
% 3.99/0.98  --splitting_grd                         true
% 3.99/0.98  --splitting_cvd                         false
% 3.99/0.98  --splitting_cvd_svl                     false
% 3.99/0.98  --splitting_nvd                         32
% 3.99/0.98  --sub_typing                            true
% 3.99/0.98  --prep_gs_sim                           true
% 3.99/0.98  --prep_unflatten                        true
% 3.99/0.98  --prep_res_sim                          true
% 3.99/0.98  --prep_upred                            true
% 3.99/0.98  --prep_sem_filter                       exhaustive
% 3.99/0.98  --prep_sem_filter_out                   false
% 3.99/0.98  --pred_elim                             true
% 3.99/0.98  --res_sim_input                         true
% 3.99/0.98  --eq_ax_congr_red                       true
% 3.99/0.98  --pure_diseq_elim                       true
% 3.99/0.98  --brand_transform                       false
% 3.99/0.98  --non_eq_to_eq                          false
% 3.99/0.98  --prep_def_merge                        true
% 3.99/0.98  --prep_def_merge_prop_impl              false
% 3.99/0.98  --prep_def_merge_mbd                    true
% 3.99/0.98  --prep_def_merge_tr_red                 false
% 3.99/0.98  --prep_def_merge_tr_cl                  false
% 3.99/0.98  --smt_preprocessing                     true
% 3.99/0.98  --smt_ac_axioms                         fast
% 3.99/0.98  --preprocessed_out                      false
% 3.99/0.98  --preprocessed_stats                    false
% 3.99/0.98  
% 3.99/0.98  ------ Abstraction refinement Options
% 3.99/0.98  
% 3.99/0.98  --abstr_ref                             []
% 3.99/0.98  --abstr_ref_prep                        false
% 3.99/0.98  --abstr_ref_until_sat                   false
% 3.99/0.98  --abstr_ref_sig_restrict                funpre
% 3.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/0.98  --abstr_ref_under                       []
% 3.99/0.98  
% 3.99/0.98  ------ SAT Options
% 3.99/0.98  
% 3.99/0.98  --sat_mode                              false
% 3.99/0.98  --sat_fm_restart_options                ""
% 3.99/0.98  --sat_gr_def                            false
% 3.99/0.98  --sat_epr_types                         true
% 3.99/0.98  --sat_non_cyclic_types                  false
% 3.99/0.98  --sat_finite_models                     false
% 3.99/0.98  --sat_fm_lemmas                         false
% 3.99/0.98  --sat_fm_prep                           false
% 3.99/0.98  --sat_fm_uc_incr                        true
% 3.99/0.98  --sat_out_model                         small
% 3.99/0.98  --sat_out_clauses                       false
% 3.99/0.98  
% 3.99/0.98  ------ QBF Options
% 3.99/0.98  
% 3.99/0.98  --qbf_mode                              false
% 3.99/0.98  --qbf_elim_univ                         false
% 3.99/0.98  --qbf_dom_inst                          none
% 3.99/0.98  --qbf_dom_pre_inst                      false
% 3.99/0.98  --qbf_sk_in                             false
% 3.99/0.98  --qbf_pred_elim                         true
% 3.99/0.98  --qbf_split                             512
% 3.99/0.98  
% 3.99/0.98  ------ BMC1 Options
% 3.99/0.98  
% 3.99/0.98  --bmc1_incremental                      false
% 3.99/0.98  --bmc1_axioms                           reachable_all
% 3.99/0.98  --bmc1_min_bound                        0
% 3.99/0.98  --bmc1_max_bound                        -1
% 3.99/0.98  --bmc1_max_bound_default                -1
% 3.99/0.98  --bmc1_symbol_reachability              true
% 3.99/0.98  --bmc1_property_lemmas                  false
% 3.99/0.98  --bmc1_k_induction                      false
% 3.99/0.98  --bmc1_non_equiv_states                 false
% 3.99/0.98  --bmc1_deadlock                         false
% 3.99/0.98  --bmc1_ucm                              false
% 3.99/0.98  --bmc1_add_unsat_core                   none
% 3.99/0.98  --bmc1_unsat_core_children              false
% 3.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/0.98  --bmc1_out_stat                         full
% 3.99/0.98  --bmc1_ground_init                      false
% 3.99/0.98  --bmc1_pre_inst_next_state              false
% 3.99/0.98  --bmc1_pre_inst_state                   false
% 3.99/0.98  --bmc1_pre_inst_reach_state             false
% 3.99/0.98  --bmc1_out_unsat_core                   false
% 3.99/0.98  --bmc1_aig_witness_out                  false
% 3.99/0.98  --bmc1_verbose                          false
% 3.99/0.98  --bmc1_dump_clauses_tptp                false
% 3.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.99/0.98  --bmc1_dump_file                        -
% 3.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.99/0.98  --bmc1_ucm_extend_mode                  1
% 3.99/0.98  --bmc1_ucm_init_mode                    2
% 3.99/0.98  --bmc1_ucm_cone_mode                    none
% 3.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.99/0.98  --bmc1_ucm_relax_model                  4
% 3.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/0.98  --bmc1_ucm_layered_model                none
% 3.99/0.98  --bmc1_ucm_max_lemma_size               10
% 3.99/0.98  
% 3.99/0.98  ------ AIG Options
% 3.99/0.98  
% 3.99/0.98  --aig_mode                              false
% 3.99/0.98  
% 3.99/0.98  ------ Instantiation Options
% 3.99/0.98  
% 3.99/0.98  --instantiation_flag                    true
% 3.99/0.98  --inst_sos_flag                         false
% 3.99/0.98  --inst_sos_phase                        true
% 3.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/0.98  --inst_lit_sel_side                     num_symb
% 3.99/0.98  --inst_solver_per_active                1400
% 3.99/0.98  --inst_solver_calls_frac                1.
% 3.99/0.98  --inst_passive_queue_type               priority_queues
% 3.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/0.98  --inst_passive_queues_freq              [25;2]
% 3.99/0.98  --inst_dismatching                      true
% 3.99/0.98  --inst_eager_unprocessed_to_passive     true
% 3.99/0.98  --inst_prop_sim_given                   true
% 3.99/0.98  --inst_prop_sim_new                     false
% 3.99/0.98  --inst_subs_new                         false
% 3.99/0.98  --inst_eq_res_simp                      false
% 3.99/0.98  --inst_subs_given                       false
% 3.99/0.98  --inst_orphan_elimination               true
% 3.99/0.98  --inst_learning_loop_flag               true
% 3.99/0.98  --inst_learning_start                   3000
% 3.99/0.98  --inst_learning_factor                  2
% 3.99/0.98  --inst_start_prop_sim_after_learn       3
% 3.99/0.98  --inst_sel_renew                        solver
% 3.99/0.98  --inst_lit_activity_flag                true
% 3.99/0.98  --inst_restr_to_given                   false
% 3.99/0.98  --inst_activity_threshold               500
% 3.99/0.98  --inst_out_proof                        true
% 3.99/0.98  
% 3.99/0.98  ------ Resolution Options
% 3.99/0.98  
% 3.99/0.98  --resolution_flag                       true
% 3.99/0.98  --res_lit_sel                           adaptive
% 3.99/0.98  --res_lit_sel_side                      none
% 3.99/0.98  --res_ordering                          kbo
% 3.99/0.98  --res_to_prop_solver                    active
% 3.99/0.98  --res_prop_simpl_new                    false
% 3.99/0.98  --res_prop_simpl_given                  true
% 3.99/0.98  --res_passive_queue_type                priority_queues
% 3.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/0.98  --res_passive_queues_freq               [15;5]
% 3.99/0.98  --res_forward_subs                      full
% 3.99/0.98  --res_backward_subs                     full
% 3.99/0.98  --res_forward_subs_resolution           true
% 3.99/0.98  --res_backward_subs_resolution          true
% 3.99/0.98  --res_orphan_elimination                true
% 3.99/0.98  --res_time_limit                        2.
% 3.99/0.98  --res_out_proof                         true
% 3.99/0.98  
% 3.99/0.98  ------ Superposition Options
% 3.99/0.98  
% 3.99/0.98  --superposition_flag                    true
% 3.99/0.98  --sup_passive_queue_type                priority_queues
% 3.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.99/0.98  --demod_completeness_check              fast
% 3.99/0.98  --demod_use_ground                      true
% 3.99/0.98  --sup_to_prop_solver                    passive
% 3.99/0.98  --sup_prop_simpl_new                    true
% 3.99/0.98  --sup_prop_simpl_given                  true
% 3.99/0.98  --sup_fun_splitting                     false
% 3.99/0.98  --sup_smt_interval                      50000
% 3.99/0.98  
% 3.99/0.98  ------ Superposition Simplification Setup
% 3.99/0.98  
% 3.99/0.98  --sup_indices_passive                   []
% 3.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.98  --sup_full_bw                           [BwDemod]
% 3.99/0.98  --sup_immed_triv                        [TrivRules]
% 3.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.98  --sup_immed_bw_main                     []
% 3.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.98  
% 3.99/0.98  ------ Combination Options
% 3.99/0.98  
% 3.99/0.98  --comb_res_mult                         3
% 3.99/0.98  --comb_sup_mult                         2
% 3.99/0.98  --comb_inst_mult                        10
% 3.99/0.98  
% 3.99/0.98  ------ Debug Options
% 3.99/0.98  
% 3.99/0.98  --dbg_backtrace                         false
% 3.99/0.98  --dbg_dump_prop_clauses                 false
% 3.99/0.98  --dbg_dump_prop_clauses_file            -
% 3.99/0.98  --dbg_out_stat                          false
% 3.99/0.98  ------ Parsing...
% 3.99/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.99/0.98  ------ Proving...
% 3.99/0.98  ------ Problem Properties 
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  clauses                                 18
% 3.99/0.98  conjectures                             1
% 3.99/0.98  EPR                                     2
% 3.99/0.98  Horn                                    18
% 3.99/0.98  unary                                   8
% 3.99/0.98  binary                                  6
% 3.99/0.98  lits                                    33
% 3.99/0.98  lits eq                                 12
% 3.99/0.98  fd_pure                                 0
% 3.99/0.98  fd_pseudo                               0
% 3.99/0.98  fd_cond                                 0
% 3.99/0.98  fd_pseudo_cond                          1
% 3.99/0.98  AC symbols                              0
% 3.99/0.98  
% 3.99/0.98  ------ Schedule dynamic 5 is on 
% 3.99/0.98  
% 3.99/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  ------ 
% 3.99/0.98  Current options:
% 3.99/0.98  ------ 
% 3.99/0.98  
% 3.99/0.98  ------ Input Options
% 3.99/0.98  
% 3.99/0.98  --out_options                           all
% 3.99/0.98  --tptp_safe_out                         true
% 3.99/0.98  --problem_path                          ""
% 3.99/0.98  --include_path                          ""
% 3.99/0.98  --clausifier                            res/vclausify_rel
% 3.99/0.98  --clausifier_options                    --mode clausify
% 3.99/0.98  --stdin                                 false
% 3.99/0.98  --stats_out                             all
% 3.99/0.98  
% 3.99/0.98  ------ General Options
% 3.99/0.98  
% 3.99/0.98  --fof                                   false
% 3.99/0.98  --time_out_real                         305.
% 3.99/0.98  --time_out_virtual                      -1.
% 3.99/0.98  --symbol_type_check                     false
% 3.99/0.98  --clausify_out                          false
% 3.99/0.98  --sig_cnt_out                           false
% 3.99/0.98  --trig_cnt_out                          false
% 3.99/0.98  --trig_cnt_out_tolerance                1.
% 3.99/0.98  --trig_cnt_out_sk_spl                   false
% 3.99/0.98  --abstr_cl_out                          false
% 3.99/0.98  
% 3.99/0.98  ------ Global Options
% 3.99/0.98  
% 3.99/0.98  --schedule                              default
% 3.99/0.98  --add_important_lit                     false
% 3.99/0.98  --prop_solver_per_cl                    1000
% 3.99/0.98  --min_unsat_core                        false
% 3.99/0.98  --soft_assumptions                      false
% 3.99/0.98  --soft_lemma_size                       3
% 3.99/0.98  --prop_impl_unit_size                   0
% 3.99/0.98  --prop_impl_unit                        []
% 3.99/0.98  --share_sel_clauses                     true
% 3.99/0.98  --reset_solvers                         false
% 3.99/0.98  --bc_imp_inh                            [conj_cone]
% 3.99/0.98  --conj_cone_tolerance                   3.
% 3.99/0.98  --extra_neg_conj                        none
% 3.99/0.98  --large_theory_mode                     true
% 3.99/0.98  --prolific_symb_bound                   200
% 3.99/0.98  --lt_threshold                          2000
% 3.99/0.98  --clause_weak_htbl                      true
% 3.99/0.98  --gc_record_bc_elim                     false
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing Options
% 3.99/0.98  
% 3.99/0.98  --preprocessing_flag                    true
% 3.99/0.98  --time_out_prep_mult                    0.1
% 3.99/0.98  --splitting_mode                        input
% 3.99/0.98  --splitting_grd                         true
% 3.99/0.98  --splitting_cvd                         false
% 3.99/0.98  --splitting_cvd_svl                     false
% 3.99/0.98  --splitting_nvd                         32
% 3.99/0.98  --sub_typing                            true
% 3.99/0.98  --prep_gs_sim                           true
% 3.99/0.98  --prep_unflatten                        true
% 3.99/0.98  --prep_res_sim                          true
% 3.99/0.98  --prep_upred                            true
% 3.99/0.98  --prep_sem_filter                       exhaustive
% 3.99/0.98  --prep_sem_filter_out                   false
% 3.99/0.98  --pred_elim                             true
% 3.99/0.98  --res_sim_input                         true
% 3.99/0.98  --eq_ax_congr_red                       true
% 3.99/0.98  --pure_diseq_elim                       true
% 3.99/0.98  --brand_transform                       false
% 3.99/0.98  --non_eq_to_eq                          false
% 3.99/0.98  --prep_def_merge                        true
% 3.99/0.98  --prep_def_merge_prop_impl              false
% 3.99/0.98  --prep_def_merge_mbd                    true
% 3.99/0.98  --prep_def_merge_tr_red                 false
% 3.99/0.98  --prep_def_merge_tr_cl                  false
% 3.99/0.98  --smt_preprocessing                     true
% 3.99/0.98  --smt_ac_axioms                         fast
% 3.99/0.98  --preprocessed_out                      false
% 3.99/0.98  --preprocessed_stats                    false
% 3.99/0.98  
% 3.99/0.98  ------ Abstraction refinement Options
% 3.99/0.98  
% 3.99/0.98  --abstr_ref                             []
% 3.99/0.98  --abstr_ref_prep                        false
% 3.99/0.98  --abstr_ref_until_sat                   false
% 3.99/0.98  --abstr_ref_sig_restrict                funpre
% 3.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/0.98  --abstr_ref_under                       []
% 3.99/0.98  
% 3.99/0.98  ------ SAT Options
% 3.99/0.98  
% 3.99/0.98  --sat_mode                              false
% 3.99/0.98  --sat_fm_restart_options                ""
% 3.99/0.98  --sat_gr_def                            false
% 3.99/0.98  --sat_epr_types                         true
% 3.99/0.98  --sat_non_cyclic_types                  false
% 3.99/0.98  --sat_finite_models                     false
% 3.99/0.98  --sat_fm_lemmas                         false
% 3.99/0.98  --sat_fm_prep                           false
% 3.99/0.98  --sat_fm_uc_incr                        true
% 3.99/0.98  --sat_out_model                         small
% 3.99/0.98  --sat_out_clauses                       false
% 3.99/0.98  
% 3.99/0.98  ------ QBF Options
% 3.99/0.98  
% 3.99/0.98  --qbf_mode                              false
% 3.99/0.98  --qbf_elim_univ                         false
% 3.99/0.98  --qbf_dom_inst                          none
% 3.99/0.98  --qbf_dom_pre_inst                      false
% 3.99/0.98  --qbf_sk_in                             false
% 3.99/0.98  --qbf_pred_elim                         true
% 3.99/0.98  --qbf_split                             512
% 3.99/0.98  
% 3.99/0.98  ------ BMC1 Options
% 3.99/0.98  
% 3.99/0.98  --bmc1_incremental                      false
% 3.99/0.98  --bmc1_axioms                           reachable_all
% 3.99/0.98  --bmc1_min_bound                        0
% 3.99/0.98  --bmc1_max_bound                        -1
% 3.99/0.98  --bmc1_max_bound_default                -1
% 3.99/0.98  --bmc1_symbol_reachability              true
% 3.99/0.98  --bmc1_property_lemmas                  false
% 3.99/0.98  --bmc1_k_induction                      false
% 3.99/0.98  --bmc1_non_equiv_states                 false
% 3.99/0.98  --bmc1_deadlock                         false
% 3.99/0.98  --bmc1_ucm                              false
% 3.99/0.98  --bmc1_add_unsat_core                   none
% 3.99/0.98  --bmc1_unsat_core_children              false
% 3.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/0.98  --bmc1_out_stat                         full
% 3.99/0.98  --bmc1_ground_init                      false
% 3.99/0.98  --bmc1_pre_inst_next_state              false
% 3.99/0.98  --bmc1_pre_inst_state                   false
% 3.99/0.98  --bmc1_pre_inst_reach_state             false
% 3.99/0.98  --bmc1_out_unsat_core                   false
% 3.99/0.98  --bmc1_aig_witness_out                  false
% 3.99/0.98  --bmc1_verbose                          false
% 3.99/0.98  --bmc1_dump_clauses_tptp                false
% 3.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.99/0.98  --bmc1_dump_file                        -
% 3.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.99/0.98  --bmc1_ucm_extend_mode                  1
% 3.99/0.98  --bmc1_ucm_init_mode                    2
% 3.99/0.98  --bmc1_ucm_cone_mode                    none
% 3.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.99/0.98  --bmc1_ucm_relax_model                  4
% 3.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/0.98  --bmc1_ucm_layered_model                none
% 3.99/0.98  --bmc1_ucm_max_lemma_size               10
% 3.99/0.98  
% 3.99/0.98  ------ AIG Options
% 3.99/0.98  
% 3.99/0.98  --aig_mode                              false
% 3.99/0.98  
% 3.99/0.98  ------ Instantiation Options
% 3.99/0.98  
% 3.99/0.98  --instantiation_flag                    true
% 3.99/0.98  --inst_sos_flag                         false
% 3.99/0.98  --inst_sos_phase                        true
% 3.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/0.98  --inst_lit_sel_side                     none
% 3.99/0.98  --inst_solver_per_active                1400
% 3.99/0.98  --inst_solver_calls_frac                1.
% 3.99/0.98  --inst_passive_queue_type               priority_queues
% 3.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/0.98  --inst_passive_queues_freq              [25;2]
% 3.99/0.98  --inst_dismatching                      true
% 3.99/0.98  --inst_eager_unprocessed_to_passive     true
% 3.99/0.98  --inst_prop_sim_given                   true
% 3.99/0.98  --inst_prop_sim_new                     false
% 3.99/0.98  --inst_subs_new                         false
% 3.99/0.98  --inst_eq_res_simp                      false
% 3.99/0.98  --inst_subs_given                       false
% 3.99/0.98  --inst_orphan_elimination               true
% 3.99/0.98  --inst_learning_loop_flag               true
% 3.99/0.98  --inst_learning_start                   3000
% 3.99/0.98  --inst_learning_factor                  2
% 3.99/0.98  --inst_start_prop_sim_after_learn       3
% 3.99/0.98  --inst_sel_renew                        solver
% 3.99/0.98  --inst_lit_activity_flag                true
% 3.99/0.98  --inst_restr_to_given                   false
% 3.99/0.98  --inst_activity_threshold               500
% 3.99/0.98  --inst_out_proof                        true
% 3.99/0.98  
% 3.99/0.98  ------ Resolution Options
% 3.99/0.98  
% 3.99/0.98  --resolution_flag                       false
% 3.99/0.98  --res_lit_sel                           adaptive
% 3.99/0.98  --res_lit_sel_side                      none
% 3.99/0.98  --res_ordering                          kbo
% 3.99/0.98  --res_to_prop_solver                    active
% 3.99/0.98  --res_prop_simpl_new                    false
% 3.99/0.98  --res_prop_simpl_given                  true
% 3.99/0.98  --res_passive_queue_type                priority_queues
% 3.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/0.98  --res_passive_queues_freq               [15;5]
% 3.99/0.98  --res_forward_subs                      full
% 3.99/0.98  --res_backward_subs                     full
% 3.99/0.98  --res_forward_subs_resolution           true
% 3.99/0.98  --res_backward_subs_resolution          true
% 3.99/0.98  --res_orphan_elimination                true
% 3.99/0.98  --res_time_limit                        2.
% 3.99/0.98  --res_out_proof                         true
% 3.99/0.98  
% 3.99/0.98  ------ Superposition Options
% 3.99/0.98  
% 3.99/0.98  --superposition_flag                    true
% 3.99/0.98  --sup_passive_queue_type                priority_queues
% 3.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.99/0.98  --demod_completeness_check              fast
% 3.99/0.98  --demod_use_ground                      true
% 3.99/0.98  --sup_to_prop_solver                    passive
% 3.99/0.98  --sup_prop_simpl_new                    true
% 3.99/0.98  --sup_prop_simpl_given                  true
% 3.99/0.98  --sup_fun_splitting                     false
% 3.99/0.98  --sup_smt_interval                      50000
% 3.99/0.98  
% 3.99/0.98  ------ Superposition Simplification Setup
% 3.99/0.98  
% 3.99/0.98  --sup_indices_passive                   []
% 3.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.98  --sup_full_bw                           [BwDemod]
% 3.99/0.98  --sup_immed_triv                        [TrivRules]
% 3.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.98  --sup_immed_bw_main                     []
% 3.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.98  
% 3.99/0.98  ------ Combination Options
% 3.99/0.98  
% 3.99/0.98  --comb_res_mult                         3
% 3.99/0.98  --comb_sup_mult                         2
% 3.99/0.98  --comb_inst_mult                        10
% 3.99/0.98  
% 3.99/0.98  ------ Debug Options
% 3.99/0.98  
% 3.99/0.98  --dbg_backtrace                         false
% 3.99/0.98  --dbg_dump_prop_clauses                 false
% 3.99/0.98  --dbg_dump_prop_clauses_file            -
% 3.99/0.98  --dbg_out_stat                          false
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  ------ Proving...
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  % SZS status Theorem for theBenchmark.p
% 3.99/0.98  
% 3.99/0.98   Resolution empty clause
% 3.99/0.98  
% 3.99/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.99/0.98  
% 3.99/0.98  fof(f9,axiom,(
% 3.99/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f45,plain,(
% 3.99/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.99/0.98    inference(cnf_transformation,[],[f9])).
% 3.99/0.98  
% 3.99/0.98  fof(f10,axiom,(
% 3.99/0.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f22,plain,(
% 3.99/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.99/0.98    inference(ennf_transformation,[],[f10])).
% 3.99/0.98  
% 3.99/0.98  fof(f46,plain,(
% 3.99/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f22])).
% 3.99/0.98  
% 3.99/0.98  fof(f4,axiom,(
% 3.99/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f40,plain,(
% 3.99/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.99/0.98    inference(cnf_transformation,[],[f4])).
% 3.99/0.98  
% 3.99/0.98  fof(f61,plain,(
% 3.99/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 3.99/0.98    inference(definition_unfolding,[],[f46,f40])).
% 3.99/0.98  
% 3.99/0.98  fof(f12,axiom,(
% 3.99/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f48,plain,(
% 3.99/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.99/0.98    inference(cnf_transformation,[],[f12])).
% 3.99/0.98  
% 3.99/0.98  fof(f3,axiom,(
% 3.99/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f39,plain,(
% 3.99/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.99/0.98    inference(cnf_transformation,[],[f3])).
% 3.99/0.98  
% 3.99/0.98  fof(f59,plain,(
% 3.99/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.99/0.98    inference(definition_unfolding,[],[f39,f40])).
% 3.99/0.98  
% 3.99/0.98  fof(f2,axiom,(
% 3.99/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f38,plain,(
% 3.99/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f2])).
% 3.99/0.98  
% 3.99/0.98  fof(f58,plain,(
% 3.99/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 3.99/0.98    inference(definition_unfolding,[],[f38,f40])).
% 3.99/0.98  
% 3.99/0.98  fof(f14,axiom,(
% 3.99/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f25,plain,(
% 3.99/0.98    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.99/0.98    inference(ennf_transformation,[],[f14])).
% 3.99/0.98  
% 3.99/0.98  fof(f26,plain,(
% 3.99/0.98    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.99/0.98    inference(flattening,[],[f25])).
% 3.99/0.98  
% 3.99/0.98  fof(f52,plain,(
% 3.99/0.98    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f26])).
% 3.99/0.98  
% 3.99/0.98  fof(f17,axiom,(
% 3.99/0.98    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f29,plain,(
% 3.99/0.98    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.99/0.98    inference(ennf_transformation,[],[f17])).
% 3.99/0.98  
% 3.99/0.98  fof(f55,plain,(
% 3.99/0.98    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f29])).
% 3.99/0.98  
% 3.99/0.98  fof(f11,axiom,(
% 3.99/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f23,plain,(
% 3.99/0.98    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.99/0.98    inference(ennf_transformation,[],[f11])).
% 3.99/0.98  
% 3.99/0.98  fof(f47,plain,(
% 3.99/0.98    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f23])).
% 3.99/0.98  
% 3.99/0.98  fof(f8,axiom,(
% 3.99/0.98    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f20,plain,(
% 3.99/0.98    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.99/0.98    inference(ennf_transformation,[],[f8])).
% 3.99/0.98  
% 3.99/0.98  fof(f21,plain,(
% 3.99/0.98    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.99/0.98    inference(flattening,[],[f20])).
% 3.99/0.98  
% 3.99/0.98  fof(f44,plain,(
% 3.99/0.98    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f21])).
% 3.99/0.98  
% 3.99/0.98  fof(f13,axiom,(
% 3.99/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f24,plain,(
% 3.99/0.98    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.99/0.98    inference(ennf_transformation,[],[f13])).
% 3.99/0.98  
% 3.99/0.98  fof(f50,plain,(
% 3.99/0.98    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f24])).
% 3.99/0.98  
% 3.99/0.98  fof(f1,axiom,(
% 3.99/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f31,plain,(
% 3.99/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.99/0.98    inference(nnf_transformation,[],[f1])).
% 3.99/0.98  
% 3.99/0.98  fof(f32,plain,(
% 3.99/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.99/0.98    inference(flattening,[],[f31])).
% 3.99/0.98  
% 3.99/0.98  fof(f37,plain,(
% 3.99/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f32])).
% 3.99/0.98  
% 3.99/0.98  fof(f18,conjecture,(
% 3.99/0.98    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f19,negated_conjecture,(
% 3.99/0.98    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.99/0.98    inference(negated_conjecture,[],[f18])).
% 3.99/0.98  
% 3.99/0.98  fof(f30,plain,(
% 3.99/0.98    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.99/0.98    inference(ennf_transformation,[],[f19])).
% 3.99/0.98  
% 3.99/0.98  fof(f33,plain,(
% 3.99/0.98    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f34,plain,(
% 3.99/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).
% 3.99/0.98  
% 3.99/0.98  fof(f56,plain,(
% 3.99/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.99/0.98    inference(cnf_transformation,[],[f34])).
% 3.99/0.98  
% 3.99/0.98  fof(f62,plain,(
% 3.99/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.99/0.98    inference(definition_unfolding,[],[f56,f40])).
% 3.99/0.98  
% 3.99/0.98  cnf(c_7,plain,
% 3.99/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.99/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_522,plain,
% 3.99/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_8,plain,
% 3.99/0.98      ( ~ v1_relat_1(X0)
% 3.99/0.98      | k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 3.99/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_521,plain,
% 3.99/0.98      ( k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
% 3.99/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2001,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_522,c_521]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_11,plain,
% 3.99/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.99/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2002,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.99/0.98      inference(light_normalisation,[status(thm)],[c_2001,c_11]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_4,plain,
% 3.99/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.99/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_3,plain,
% 3.99/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 3.99/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_524,plain,
% 3.99/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_761,plain,
% 3.99/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_4,c_524]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_14,plain,
% 3.99/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.99/0.98      | ~ v1_relat_1(X0)
% 3.99/0.98      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 3.99/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_517,plain,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 3.99/0.98      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.99/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2151,plain,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 3.99/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.99/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_11,c_517]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_17,plain,
% 3.99/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.99/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_514,plain,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.99/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1194,plain,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_522,c_514]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2155,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.99/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.99/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.99/0.98      inference(demodulation,[status(thm)],[c_2151,c_1194]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_45,plain,
% 3.99/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_3918,plain,
% 3.99/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.99/0.98      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 3.99/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2155,c_45]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_3919,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.99/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.99/0.98      inference(renaming,[status(thm)],[c_3918]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_3928,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(k4_xboole_0(X0,X1)),X0) = k6_relat_1(k4_xboole_0(X0,X1)) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_761,c_3919]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_9,plain,
% 3.99/0.98      ( ~ v1_relat_1(X0)
% 3.99/0.98      | ~ v1_relat_1(X1)
% 3.99/0.98      | ~ v1_relat_1(X2)
% 3.99/0.98      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 3.99/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_520,plain,
% 3.99/0.98      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 3.99/0.98      | v1_relat_1(X1) != iProver_top
% 3.99/0.98      | v1_relat_1(X0) != iProver_top
% 3.99/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2166,plain,
% 3.99/0.98      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2))
% 3.99/0.98      | v1_relat_1(X1) != iProver_top
% 3.99/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_522,c_520]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_10057,plain,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2)
% 3.99/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_522,c_2166]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_10066,plain,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)
% 3.99/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.99/0.98      inference(light_normalisation,[status(thm)],[c_10057,c_1194]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_12963,plain,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_522,c_10066]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_6,plain,
% 3.99/0.98      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.99/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_523,plain,
% 3.99/0.98      ( v1_relat_1(X0) != iProver_top
% 3.99/0.98      | v1_relat_1(X1) != iProver_top
% 3.99/0.98      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2050,plain,
% 3.99/0.98      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 3.99/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 3.99/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_1194,c_523]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2812,plain,
% 3.99/0.98      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 3.99/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.99/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2050,c_45]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2818,plain,
% 3.99/0.98      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 3.99/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_2812,c_522]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2824,plain,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_2818,c_514]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_12973,plain,
% 3.99/0.98      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 3.99/0.98      inference(demodulation,[status(thm)],[c_12963,c_1194,c_2824]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_12991,plain,
% 3.99/0.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,X2)),X1) = k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X0)) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_3928,c_12973]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_13054,plain,
% 3.99/0.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,X2)),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,X2)) ),
% 3.99/0.98      inference(demodulation,[status(thm)],[c_12991,c_1194]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_13438,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_2002,c_13054]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_13480,plain,
% 3.99/0.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.99/0.98      inference(light_normalisation,[status(thm)],[c_13438,c_2002]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_13,plain,
% 3.99/0.98      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 3.99/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_518,plain,
% 3.99/0.98      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 3.99/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_13005,plain,
% 3.99/0.98      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 3.99/0.98      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_12973,c_518]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_13905,plain,
% 3.99/0.98      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top ),
% 3.99/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_13005,c_2818]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_13914,plain,
% 3.99/0.98      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) = iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_13480,c_13905]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_0,plain,
% 3.99/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.99/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_526,plain,
% 3.99/0.98      ( X0 = X1
% 3.99/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.99/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_14562,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0)
% 3.99/0.98      | r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_13914,c_526]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_14565,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.99/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_14562,c_13914]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_14932,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)) = k6_relat_1(k4_xboole_0(X0,X1)) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_14565,c_3928]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_15464,plain,
% 3.99/0.98      ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_14932,c_2002]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_18,negated_conjecture,
% 3.99/0.98      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 3.99/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1197,plain,
% 3.99/0.98      ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.99/0.98      inference(demodulation,[status(thm)],[c_1194,c_18]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_14744,plain,
% 3.99/0.98      ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 3.99/0.98      inference(demodulation,[status(thm)],[c_14565,c_1197]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_15560,plain,
% 3.99/0.98      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.99/0.98      inference(demodulation,[status(thm)],[c_15464,c_14744]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_15938,plain,
% 3.99/0.98      ( $false ),
% 3.99/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_15560,c_14565]) ).
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.99/0.98  
% 3.99/0.98  ------                               Statistics
% 3.99/0.98  
% 3.99/0.98  ------ General
% 3.99/0.98  
% 3.99/0.98  abstr_ref_over_cycles:                  0
% 3.99/0.98  abstr_ref_under_cycles:                 0
% 3.99/0.98  gc_basic_clause_elim:                   0
% 3.99/0.98  forced_gc_time:                         0
% 3.99/0.98  parsing_time:                           0.012
% 3.99/0.98  unif_index_cands_time:                  0.
% 3.99/0.98  unif_index_add_time:                    0.
% 3.99/0.98  orderings_time:                         0.
% 3.99/0.98  out_proof_time:                         0.009
% 3.99/0.98  total_time:                             0.465
% 3.99/0.98  num_of_symbols:                         43
% 3.99/0.98  num_of_terms:                           22146
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing
% 3.99/0.98  
% 3.99/0.98  num_of_splits:                          0
% 3.99/0.98  num_of_split_atoms:                     0
% 3.99/0.98  num_of_reused_defs:                     0
% 3.99/0.98  num_eq_ax_congr_red:                    18
% 3.99/0.98  num_of_sem_filtered_clauses:            1
% 3.99/0.98  num_of_subtypes:                        0
% 3.99/0.98  monotx_restored_types:                  0
% 3.99/0.98  sat_num_of_epr_types:                   0
% 3.99/0.98  sat_num_of_non_cyclic_types:            0
% 3.99/0.98  sat_guarded_non_collapsed_types:        0
% 3.99/0.98  num_pure_diseq_elim:                    0
% 3.99/0.98  simp_replaced_by:                       0
% 3.99/0.98  res_preprocessed:                       95
% 3.99/0.98  prep_upred:                             0
% 3.99/0.98  prep_unflattend:                        0
% 3.99/0.98  smt_new_axioms:                         0
% 3.99/0.98  pred_elim_cands:                        2
% 3.99/0.98  pred_elim:                              0
% 3.99/0.98  pred_elim_cl:                           0
% 3.99/0.98  pred_elim_cycles:                       2
% 3.99/0.98  merged_defs:                            0
% 3.99/0.98  merged_defs_ncl:                        0
% 3.99/0.98  bin_hyper_res:                          0
% 3.99/0.98  prep_cycles:                            4
% 3.99/0.98  pred_elim_time:                         0.
% 3.99/0.98  splitting_time:                         0.
% 3.99/0.98  sem_filter_time:                        0.
% 3.99/0.98  monotx_time:                            0.
% 3.99/0.98  subtype_inf_time:                       0.
% 3.99/0.98  
% 3.99/0.98  ------ Problem properties
% 3.99/0.98  
% 3.99/0.98  clauses:                                18
% 3.99/0.98  conjectures:                            1
% 3.99/0.98  epr:                                    2
% 3.99/0.98  horn:                                   18
% 3.99/0.98  ground:                                 1
% 3.99/0.98  unary:                                  8
% 3.99/0.98  binary:                                 6
% 3.99/0.98  lits:                                   33
% 3.99/0.98  lits_eq:                                12
% 3.99/0.98  fd_pure:                                0
% 3.99/0.98  fd_pseudo:                              0
% 3.99/0.98  fd_cond:                                0
% 3.99/0.98  fd_pseudo_cond:                         1
% 3.99/0.98  ac_symbols:                             0
% 3.99/0.98  
% 3.99/0.98  ------ Propositional Solver
% 3.99/0.98  
% 3.99/0.98  prop_solver_calls:                      29
% 3.99/0.98  prop_fast_solver_calls:                 571
% 3.99/0.98  smt_solver_calls:                       0
% 3.99/0.98  smt_fast_solver_calls:                  0
% 3.99/0.98  prop_num_of_clauses:                    6432
% 3.99/0.98  prop_preprocess_simplified:             11789
% 3.99/0.98  prop_fo_subsumed:                       5
% 3.99/0.98  prop_solver_time:                       0.
% 3.99/0.98  smt_solver_time:                        0.
% 3.99/0.98  smt_fast_solver_time:                   0.
% 3.99/0.98  prop_fast_solver_time:                  0.
% 3.99/0.98  prop_unsat_core_time:                   0.
% 3.99/0.98  
% 3.99/0.98  ------ QBF
% 3.99/0.98  
% 3.99/0.98  qbf_q_res:                              0
% 3.99/0.98  qbf_num_tautologies:                    0
% 3.99/0.98  qbf_prep_cycles:                        0
% 3.99/0.98  
% 3.99/0.98  ------ BMC1
% 3.99/0.98  
% 3.99/0.98  bmc1_current_bound:                     -1
% 3.99/0.98  bmc1_last_solved_bound:                 -1
% 3.99/0.98  bmc1_unsat_core_size:                   -1
% 3.99/0.98  bmc1_unsat_core_parents_size:           -1
% 3.99/0.98  bmc1_merge_next_fun:                    0
% 3.99/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.99/0.98  
% 3.99/0.98  ------ Instantiation
% 3.99/0.98  
% 3.99/0.98  inst_num_of_clauses:                    1835
% 3.99/0.98  inst_num_in_passive:                    496
% 3.99/0.98  inst_num_in_active:                     550
% 3.99/0.98  inst_num_in_unprocessed:                789
% 3.99/0.98  inst_num_of_loops:                      610
% 3.99/0.98  inst_num_of_learning_restarts:          0
% 3.99/0.98  inst_num_moves_active_passive:          59
% 3.99/0.98  inst_lit_activity:                      0
% 3.99/0.98  inst_lit_activity_moves:                1
% 3.99/0.98  inst_num_tautologies:                   0
% 3.99/0.98  inst_num_prop_implied:                  0
% 3.99/0.98  inst_num_existing_simplified:           0
% 3.99/0.98  inst_num_eq_res_simplified:             0
% 3.99/0.98  inst_num_child_elim:                    0
% 3.99/0.98  inst_num_of_dismatching_blockings:      697
% 3.99/0.98  inst_num_of_non_proper_insts:           1526
% 3.99/0.98  inst_num_of_duplicates:                 0
% 3.99/0.98  inst_inst_num_from_inst_to_res:         0
% 3.99/0.98  inst_dismatching_checking_time:         0.
% 3.99/0.98  
% 3.99/0.98  ------ Resolution
% 3.99/0.98  
% 3.99/0.98  res_num_of_clauses:                     0
% 3.99/0.98  res_num_in_passive:                     0
% 3.99/0.98  res_num_in_active:                      0
% 3.99/0.98  res_num_of_loops:                       99
% 3.99/0.98  res_forward_subset_subsumed:            182
% 3.99/0.98  res_backward_subset_subsumed:           2
% 3.99/0.98  res_forward_subsumed:                   0
% 3.99/0.98  res_backward_subsumed:                  0
% 3.99/0.98  res_forward_subsumption_resolution:     0
% 3.99/0.98  res_backward_subsumption_resolution:    0
% 3.99/0.98  res_clause_to_clause_subsumption:       2499
% 3.99/0.98  res_orphan_elimination:                 0
% 3.99/0.98  res_tautology_del:                      135
% 3.99/0.98  res_num_eq_res_simplified:              0
% 3.99/0.98  res_num_sel_changes:                    0
% 3.99/0.98  res_moves_from_active_to_pass:          0
% 3.99/0.98  
% 3.99/0.98  ------ Superposition
% 3.99/0.98  
% 3.99/0.98  sup_time_total:                         0.
% 3.99/0.98  sup_time_generating:                    0.
% 3.99/0.98  sup_time_sim_full:                      0.
% 3.99/0.98  sup_time_sim_immed:                     0.
% 3.99/0.98  
% 3.99/0.98  sup_num_of_clauses:                     428
% 3.99/0.98  sup_num_in_active:                      100
% 3.99/0.98  sup_num_in_passive:                     328
% 3.99/0.98  sup_num_of_loops:                       120
% 3.99/0.98  sup_fw_superposition:                   823
% 3.99/0.98  sup_bw_superposition:                   1097
% 3.99/0.98  sup_immediate_simplified:               1018
% 3.99/0.98  sup_given_eliminated:                   3
% 3.99/0.98  comparisons_done:                       0
% 3.99/0.98  comparisons_avoided:                    0
% 3.99/0.98  
% 3.99/0.98  ------ Simplifications
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  sim_fw_subset_subsumed:                 28
% 3.99/0.98  sim_bw_subset_subsumed:                 5
% 3.99/0.98  sim_fw_subsumed:                        375
% 3.99/0.98  sim_bw_subsumed:                        0
% 3.99/0.98  sim_fw_subsumption_res:                 7
% 3.99/0.98  sim_bw_subsumption_res:                 0
% 3.99/0.98  sim_tautology_del:                      3
% 3.99/0.98  sim_eq_tautology_del:                   146
% 3.99/0.98  sim_eq_res_simp:                        0
% 3.99/0.98  sim_fw_demodulated:                     200
% 3.99/0.98  sim_bw_demodulated:                     47
% 3.99/0.98  sim_light_normalised:                   598
% 3.99/0.98  sim_joinable_taut:                      0
% 3.99/0.98  sim_joinable_simp:                      0
% 3.99/0.98  sim_ac_normalised:                      0
% 3.99/0.98  sim_smt_subsumption:                    0
% 3.99/0.98  
%------------------------------------------------------------------------------
