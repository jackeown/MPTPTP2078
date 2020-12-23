%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:14 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 252 expanded)
%              Number of clauses        :   65 ( 112 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  212 ( 685 expanded)
%              Number of equality atoms :  109 ( 250 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
             => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
     => ( k5_relat_1(X1,sK2) != k5_relat_1(X1,k7_relat_1(sK2,X0))
        & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(sK2,X0)))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
            & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0))
          & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))
    & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f36,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_137,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_40,X0_41)),X0_41)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_378,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_40,X0_41)),X0_41) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_134,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_380,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_142,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) = X0_41 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_373,plain,
    ( k3_xboole_0(X0_41,X1_41) = X0_41
    | r1_tarski(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_606,plain,
    ( k3_xboole_0(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_380,c_373])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_144,plain,
    ( k3_xboole_0(X0_41,X1_41) = k3_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k3_xboole_0(X0_41,X2_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_372,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k3_xboole_0(X0_41,X2_41),X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_684,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k3_xboole_0(X2_41,X0_41),X1_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_144,c_372])).

cnf(c_865,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0_41) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X0_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_684])).

cnf(c_1050,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_378,c_865])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_762,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_763,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_876,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1125,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1050,c_14,c_763,c_876])).

cnf(c_5,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_139,plain,
    ( ~ r1_tarski(k2_relat_1(X0_40),X0_41)
    | ~ v1_relat_1(X0_40)
    | k8_relat_1(X0_41,X0_40) = X0_40 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_376,plain,
    ( k8_relat_1(X0_41,X0_40) = X0_40
    | r1_tarski(k2_relat_1(X0_40),X0_41) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_1241,plain,
    ( k8_relat_1(sK0,sK1) = sK1
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1125,c_376])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_178,plain,
    ( k8_relat_1(X0_41,X0_40) = X0_40
    | r1_tarski(k2_relat_1(X0_40),X0_41) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_180,plain,
    ( k8_relat_1(sK0,sK1) = sK1
    | r1_tarski(k2_relat_1(sK1),sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_1456,plain,
    ( k8_relat_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1241,c_13,c_14,c_180,c_763,c_876])).

cnf(c_132,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_382,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_132])).

cnf(c_133,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_381,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_3,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_141,plain,
    ( v1_relat_1(k6_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_374,plain,
    ( v1_relat_1(k6_relat_1(X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_138,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(X2_40)
    | k5_relat_1(k5_relat_1(X1_40,X0_40),X2_40) = k5_relat_1(X1_40,k5_relat_1(X0_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_377,plain,
    ( k5_relat_1(k5_relat_1(X0_40,X1_40),X2_40) = k5_relat_1(X0_40,k5_relat_1(X1_40,X2_40))
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(X2_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_1336,plain,
    ( k5_relat_1(X0_40,k5_relat_1(k6_relat_1(X0_41),X1_40)) = k5_relat_1(k5_relat_1(X0_40,k6_relat_1(X0_41)),X1_40)
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_374,c_377])).

cnf(c_5868,plain,
    ( k5_relat_1(k5_relat_1(X0_40,k6_relat_1(X0_41)),sK2) = k5_relat_1(X0_40,k5_relat_1(k6_relat_1(X0_41),sK2))
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_1336])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_136,plain,
    ( ~ v1_relat_1(X0_40)
    | k5_relat_1(k6_relat_1(X0_41),X0_40) = k7_relat_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_379,plain,
    ( k5_relat_1(k6_relat_1(X0_41),X0_40) = k7_relat_1(X0_40,X0_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_775,plain,
    ( k5_relat_1(k6_relat_1(X0_41),sK2) = k7_relat_1(sK2,X0_41) ),
    inference(superposition,[status(thm)],[c_381,c_379])).

cnf(c_5883,plain,
    ( k5_relat_1(k5_relat_1(X0_40,k6_relat_1(X0_41)),sK2) = k5_relat_1(X0_40,k7_relat_1(sK2,X0_41))
    | v1_relat_1(X0_40) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5868,c_775])).

cnf(c_6687,plain,
    ( k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0_41)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0_41)) ),
    inference(superposition,[status(thm)],[c_382,c_5883])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_140,plain,
    ( ~ v1_relat_1(X0_40)
    | k5_relat_1(X0_40,k6_relat_1(X0_41)) = k8_relat_1(X0_41,X0_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_375,plain,
    ( k5_relat_1(X0_40,k6_relat_1(X0_41)) = k8_relat_1(X0_41,X0_40)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_704,plain,
    ( k5_relat_1(sK1,k6_relat_1(X0_41)) = k8_relat_1(X0_41,sK1) ),
    inference(superposition,[status(thm)],[c_382,c_375])).

cnf(c_6693,plain,
    ( k5_relat_1(k8_relat_1(X0_41,sK1),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0_41)) ),
    inference(light_normalisation,[status(thm)],[c_6687,c_704])).

cnf(c_6702,plain,
    ( k5_relat_1(sK1,k7_relat_1(sK2,sK0)) = k5_relat_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1456,c_6693])).

cnf(c_146,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_527,plain,
    ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_148,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_477,plain,
    ( k5_relat_1(sK1,k7_relat_1(sK2,sK0)) != X0_40
    | k5_relat_1(sK1,sK2) != X0_40
    | k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_526,plain,
    ( k5_relat_1(sK1,k7_relat_1(sK2,sK0)) != k5_relat_1(sK1,sK2)
    | k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0))
    | k5_relat_1(sK1,sK2) != k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_9,negated_conjecture,
    ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_135,negated_conjecture,
    ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6702,c_527,c_526,c_135])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.20/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.03  
% 3.20/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/1.03  
% 3.20/1.03  ------  iProver source info
% 3.20/1.03  
% 3.20/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.20/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/1.03  git: non_committed_changes: false
% 3.20/1.03  git: last_make_outside_of_git: false
% 3.20/1.03  
% 3.20/1.03  ------ 
% 3.20/1.03  
% 3.20/1.03  ------ Input Options
% 3.20/1.03  
% 3.20/1.03  --out_options                           all
% 3.20/1.03  --tptp_safe_out                         true
% 3.20/1.03  --problem_path                          ""
% 3.20/1.03  --include_path                          ""
% 3.20/1.03  --clausifier                            res/vclausify_rel
% 3.20/1.03  --clausifier_options                    --mode clausify
% 3.20/1.03  --stdin                                 false
% 3.20/1.03  --stats_out                             all
% 3.20/1.03  
% 3.20/1.03  ------ General Options
% 3.20/1.03  
% 3.20/1.03  --fof                                   false
% 3.20/1.03  --time_out_real                         305.
% 3.20/1.03  --time_out_virtual                      -1.
% 3.20/1.03  --symbol_type_check                     false
% 3.20/1.03  --clausify_out                          false
% 3.20/1.03  --sig_cnt_out                           false
% 3.20/1.03  --trig_cnt_out                          false
% 3.20/1.03  --trig_cnt_out_tolerance                1.
% 3.20/1.03  --trig_cnt_out_sk_spl                   false
% 3.20/1.03  --abstr_cl_out                          false
% 3.20/1.03  
% 3.20/1.03  ------ Global Options
% 3.20/1.03  
% 3.20/1.03  --schedule                              default
% 3.20/1.03  --add_important_lit                     false
% 3.20/1.03  --prop_solver_per_cl                    1000
% 3.20/1.03  --min_unsat_core                        false
% 3.20/1.03  --soft_assumptions                      false
% 3.20/1.03  --soft_lemma_size                       3
% 3.20/1.03  --prop_impl_unit_size                   0
% 3.20/1.03  --prop_impl_unit                        []
% 3.20/1.03  --share_sel_clauses                     true
% 3.20/1.03  --reset_solvers                         false
% 3.20/1.03  --bc_imp_inh                            [conj_cone]
% 3.20/1.03  --conj_cone_tolerance                   3.
% 3.20/1.03  --extra_neg_conj                        none
% 3.20/1.03  --large_theory_mode                     true
% 3.20/1.03  --prolific_symb_bound                   200
% 3.20/1.03  --lt_threshold                          2000
% 3.20/1.03  --clause_weak_htbl                      true
% 3.20/1.03  --gc_record_bc_elim                     false
% 3.20/1.03  
% 3.20/1.03  ------ Preprocessing Options
% 3.20/1.03  
% 3.20/1.03  --preprocessing_flag                    true
% 3.20/1.03  --time_out_prep_mult                    0.1
% 3.20/1.03  --splitting_mode                        input
% 3.20/1.03  --splitting_grd                         true
% 3.20/1.03  --splitting_cvd                         false
% 3.20/1.03  --splitting_cvd_svl                     false
% 3.20/1.03  --splitting_nvd                         32
% 3.20/1.03  --sub_typing                            true
% 3.20/1.03  --prep_gs_sim                           true
% 3.20/1.03  --prep_unflatten                        true
% 3.20/1.03  --prep_res_sim                          true
% 3.20/1.03  --prep_upred                            true
% 3.20/1.03  --prep_sem_filter                       exhaustive
% 3.20/1.03  --prep_sem_filter_out                   false
% 3.20/1.03  --pred_elim                             true
% 3.20/1.03  --res_sim_input                         true
% 3.20/1.03  --eq_ax_congr_red                       true
% 3.20/1.03  --pure_diseq_elim                       true
% 3.20/1.03  --brand_transform                       false
% 3.20/1.03  --non_eq_to_eq                          false
% 3.20/1.03  --prep_def_merge                        true
% 3.20/1.03  --prep_def_merge_prop_impl              false
% 3.20/1.03  --prep_def_merge_mbd                    true
% 3.20/1.03  --prep_def_merge_tr_red                 false
% 3.20/1.03  --prep_def_merge_tr_cl                  false
% 3.20/1.03  --smt_preprocessing                     true
% 3.20/1.03  --smt_ac_axioms                         fast
% 3.20/1.03  --preprocessed_out                      false
% 3.20/1.03  --preprocessed_stats                    false
% 3.20/1.03  
% 3.20/1.03  ------ Abstraction refinement Options
% 3.20/1.03  
% 3.20/1.03  --abstr_ref                             []
% 3.20/1.03  --abstr_ref_prep                        false
% 3.20/1.03  --abstr_ref_until_sat                   false
% 3.20/1.03  --abstr_ref_sig_restrict                funpre
% 3.20/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.03  --abstr_ref_under                       []
% 3.20/1.03  
% 3.20/1.03  ------ SAT Options
% 3.20/1.03  
% 3.20/1.03  --sat_mode                              false
% 3.20/1.03  --sat_fm_restart_options                ""
% 3.20/1.03  --sat_gr_def                            false
% 3.20/1.03  --sat_epr_types                         true
% 3.20/1.03  --sat_non_cyclic_types                  false
% 3.20/1.03  --sat_finite_models                     false
% 3.20/1.03  --sat_fm_lemmas                         false
% 3.20/1.03  --sat_fm_prep                           false
% 3.20/1.03  --sat_fm_uc_incr                        true
% 3.20/1.03  --sat_out_model                         small
% 3.20/1.03  --sat_out_clauses                       false
% 3.20/1.03  
% 3.20/1.03  ------ QBF Options
% 3.20/1.03  
% 3.20/1.03  --qbf_mode                              false
% 3.20/1.03  --qbf_elim_univ                         false
% 3.20/1.03  --qbf_dom_inst                          none
% 3.20/1.03  --qbf_dom_pre_inst                      false
% 3.20/1.03  --qbf_sk_in                             false
% 3.20/1.03  --qbf_pred_elim                         true
% 3.20/1.03  --qbf_split                             512
% 3.20/1.03  
% 3.20/1.03  ------ BMC1 Options
% 3.20/1.03  
% 3.20/1.03  --bmc1_incremental                      false
% 3.20/1.03  --bmc1_axioms                           reachable_all
% 3.20/1.03  --bmc1_min_bound                        0
% 3.20/1.03  --bmc1_max_bound                        -1
% 3.20/1.03  --bmc1_max_bound_default                -1
% 3.20/1.03  --bmc1_symbol_reachability              true
% 3.20/1.03  --bmc1_property_lemmas                  false
% 3.20/1.03  --bmc1_k_induction                      false
% 3.20/1.03  --bmc1_non_equiv_states                 false
% 3.20/1.03  --bmc1_deadlock                         false
% 3.20/1.03  --bmc1_ucm                              false
% 3.20/1.03  --bmc1_add_unsat_core                   none
% 3.20/1.03  --bmc1_unsat_core_children              false
% 3.20/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.03  --bmc1_out_stat                         full
% 3.20/1.03  --bmc1_ground_init                      false
% 3.20/1.03  --bmc1_pre_inst_next_state              false
% 3.20/1.03  --bmc1_pre_inst_state                   false
% 3.20/1.03  --bmc1_pre_inst_reach_state             false
% 3.20/1.03  --bmc1_out_unsat_core                   false
% 3.20/1.03  --bmc1_aig_witness_out                  false
% 3.20/1.03  --bmc1_verbose                          false
% 3.20/1.03  --bmc1_dump_clauses_tptp                false
% 3.20/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.03  --bmc1_dump_file                        -
% 3.20/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.03  --bmc1_ucm_extend_mode                  1
% 3.20/1.03  --bmc1_ucm_init_mode                    2
% 3.20/1.03  --bmc1_ucm_cone_mode                    none
% 3.20/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.03  --bmc1_ucm_relax_model                  4
% 3.20/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.03  --bmc1_ucm_layered_model                none
% 3.20/1.03  --bmc1_ucm_max_lemma_size               10
% 3.20/1.03  
% 3.20/1.03  ------ AIG Options
% 3.20/1.03  
% 3.20/1.03  --aig_mode                              false
% 3.20/1.03  
% 3.20/1.03  ------ Instantiation Options
% 3.20/1.03  
% 3.20/1.03  --instantiation_flag                    true
% 3.20/1.03  --inst_sos_flag                         false
% 3.20/1.03  --inst_sos_phase                        true
% 3.20/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.03  --inst_lit_sel_side                     num_symb
% 3.20/1.03  --inst_solver_per_active                1400
% 3.20/1.03  --inst_solver_calls_frac                1.
% 3.20/1.03  --inst_passive_queue_type               priority_queues
% 3.20/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.03  --inst_passive_queues_freq              [25;2]
% 3.20/1.03  --inst_dismatching                      true
% 3.20/1.03  --inst_eager_unprocessed_to_passive     true
% 3.20/1.03  --inst_prop_sim_given                   true
% 3.20/1.03  --inst_prop_sim_new                     false
% 3.20/1.03  --inst_subs_new                         false
% 3.20/1.03  --inst_eq_res_simp                      false
% 3.20/1.03  --inst_subs_given                       false
% 3.20/1.03  --inst_orphan_elimination               true
% 3.20/1.03  --inst_learning_loop_flag               true
% 3.20/1.03  --inst_learning_start                   3000
% 3.20/1.03  --inst_learning_factor                  2
% 3.20/1.03  --inst_start_prop_sim_after_learn       3
% 3.20/1.03  --inst_sel_renew                        solver
% 3.20/1.03  --inst_lit_activity_flag                true
% 3.20/1.03  --inst_restr_to_given                   false
% 3.20/1.03  --inst_activity_threshold               500
% 3.20/1.03  --inst_out_proof                        true
% 3.20/1.03  
% 3.20/1.03  ------ Resolution Options
% 3.20/1.03  
% 3.20/1.03  --resolution_flag                       true
% 3.20/1.03  --res_lit_sel                           adaptive
% 3.20/1.03  --res_lit_sel_side                      none
% 3.20/1.03  --res_ordering                          kbo
% 3.20/1.03  --res_to_prop_solver                    active
% 3.20/1.03  --res_prop_simpl_new                    false
% 3.20/1.03  --res_prop_simpl_given                  true
% 3.20/1.03  --res_passive_queue_type                priority_queues
% 3.20/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.03  --res_passive_queues_freq               [15;5]
% 3.20/1.03  --res_forward_subs                      full
% 3.20/1.03  --res_backward_subs                     full
% 3.20/1.03  --res_forward_subs_resolution           true
% 3.20/1.03  --res_backward_subs_resolution          true
% 3.20/1.03  --res_orphan_elimination                true
% 3.20/1.03  --res_time_limit                        2.
% 3.20/1.03  --res_out_proof                         true
% 3.20/1.03  
% 3.20/1.03  ------ Superposition Options
% 3.20/1.03  
% 3.20/1.03  --superposition_flag                    true
% 3.20/1.03  --sup_passive_queue_type                priority_queues
% 3.20/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.03  --demod_completeness_check              fast
% 3.20/1.03  --demod_use_ground                      true
% 3.20/1.03  --sup_to_prop_solver                    passive
% 3.20/1.03  --sup_prop_simpl_new                    true
% 3.20/1.03  --sup_prop_simpl_given                  true
% 3.20/1.03  --sup_fun_splitting                     false
% 3.20/1.03  --sup_smt_interval                      50000
% 3.20/1.03  
% 3.20/1.03  ------ Superposition Simplification Setup
% 3.20/1.03  
% 3.20/1.03  --sup_indices_passive                   []
% 3.20/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.03  --sup_full_bw                           [BwDemod]
% 3.20/1.03  --sup_immed_triv                        [TrivRules]
% 3.20/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.03  --sup_immed_bw_main                     []
% 3.20/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.03  
% 3.20/1.03  ------ Combination Options
% 3.20/1.03  
% 3.20/1.03  --comb_res_mult                         3
% 3.20/1.03  --comb_sup_mult                         2
% 3.20/1.03  --comb_inst_mult                        10
% 3.20/1.03  
% 3.20/1.03  ------ Debug Options
% 3.20/1.03  
% 3.20/1.03  --dbg_backtrace                         false
% 3.20/1.03  --dbg_dump_prop_clauses                 false
% 3.20/1.03  --dbg_dump_prop_clauses_file            -
% 3.20/1.03  --dbg_out_stat                          false
% 3.20/1.03  ------ Parsing...
% 3.20/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/1.03  
% 3.20/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.20/1.03  
% 3.20/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/1.03  
% 3.20/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/1.03  ------ Proving...
% 3.20/1.03  ------ Problem Properties 
% 3.20/1.03  
% 3.20/1.03  
% 3.20/1.03  clauses                                 13
% 3.20/1.03  conjectures                             4
% 3.20/1.03  EPR                                     2
% 3.20/1.03  Horn                                    13
% 3.20/1.03  unary                                   6
% 3.20/1.03  binary                                  5
% 3.20/1.03  lits                                    23
% 3.20/1.03  lits eq                                 7
% 3.20/1.03  fd_pure                                 0
% 3.20/1.03  fd_pseudo                               0
% 3.20/1.03  fd_cond                                 0
% 3.20/1.03  fd_pseudo_cond                          0
% 3.20/1.03  AC symbols                              0
% 3.20/1.03  
% 3.20/1.03  ------ Schedule dynamic 5 is on 
% 3.20/1.03  
% 3.20/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/1.03  
% 3.20/1.03  
% 3.20/1.03  ------ 
% 3.20/1.03  Current options:
% 3.20/1.03  ------ 
% 3.20/1.03  
% 3.20/1.03  ------ Input Options
% 3.20/1.03  
% 3.20/1.03  --out_options                           all
% 3.20/1.03  --tptp_safe_out                         true
% 3.20/1.03  --problem_path                          ""
% 3.20/1.03  --include_path                          ""
% 3.20/1.03  --clausifier                            res/vclausify_rel
% 3.20/1.03  --clausifier_options                    --mode clausify
% 3.20/1.03  --stdin                                 false
% 3.20/1.03  --stats_out                             all
% 3.20/1.03  
% 3.20/1.03  ------ General Options
% 3.20/1.03  
% 3.20/1.03  --fof                                   false
% 3.20/1.03  --time_out_real                         305.
% 3.20/1.03  --time_out_virtual                      -1.
% 3.20/1.03  --symbol_type_check                     false
% 3.20/1.03  --clausify_out                          false
% 3.20/1.03  --sig_cnt_out                           false
% 3.20/1.03  --trig_cnt_out                          false
% 3.20/1.03  --trig_cnt_out_tolerance                1.
% 3.20/1.03  --trig_cnt_out_sk_spl                   false
% 3.20/1.03  --abstr_cl_out                          false
% 3.20/1.03  
% 3.20/1.03  ------ Global Options
% 3.20/1.03  
% 3.20/1.03  --schedule                              default
% 3.20/1.03  --add_important_lit                     false
% 3.20/1.03  --prop_solver_per_cl                    1000
% 3.20/1.03  --min_unsat_core                        false
% 3.20/1.03  --soft_assumptions                      false
% 3.20/1.03  --soft_lemma_size                       3
% 3.20/1.03  --prop_impl_unit_size                   0
% 3.20/1.03  --prop_impl_unit                        []
% 3.20/1.03  --share_sel_clauses                     true
% 3.20/1.03  --reset_solvers                         false
% 3.20/1.03  --bc_imp_inh                            [conj_cone]
% 3.20/1.03  --conj_cone_tolerance                   3.
% 3.20/1.03  --extra_neg_conj                        none
% 3.20/1.03  --large_theory_mode                     true
% 3.20/1.03  --prolific_symb_bound                   200
% 3.20/1.03  --lt_threshold                          2000
% 3.20/1.03  --clause_weak_htbl                      true
% 3.20/1.03  --gc_record_bc_elim                     false
% 3.20/1.03  
% 3.20/1.03  ------ Preprocessing Options
% 3.20/1.03  
% 3.20/1.03  --preprocessing_flag                    true
% 3.20/1.03  --time_out_prep_mult                    0.1
% 3.20/1.03  --splitting_mode                        input
% 3.20/1.03  --splitting_grd                         true
% 3.20/1.03  --splitting_cvd                         false
% 3.20/1.03  --splitting_cvd_svl                     false
% 3.20/1.03  --splitting_nvd                         32
% 3.20/1.03  --sub_typing                            true
% 3.20/1.03  --prep_gs_sim                           true
% 3.20/1.03  --prep_unflatten                        true
% 3.20/1.03  --prep_res_sim                          true
% 3.20/1.03  --prep_upred                            true
% 3.20/1.03  --prep_sem_filter                       exhaustive
% 3.20/1.03  --prep_sem_filter_out                   false
% 3.20/1.03  --pred_elim                             true
% 3.20/1.03  --res_sim_input                         true
% 3.20/1.03  --eq_ax_congr_red                       true
% 3.20/1.03  --pure_diseq_elim                       true
% 3.20/1.03  --brand_transform                       false
% 3.20/1.03  --non_eq_to_eq                          false
% 3.20/1.03  --prep_def_merge                        true
% 3.20/1.03  --prep_def_merge_prop_impl              false
% 3.20/1.03  --prep_def_merge_mbd                    true
% 3.20/1.03  --prep_def_merge_tr_red                 false
% 3.20/1.03  --prep_def_merge_tr_cl                  false
% 3.20/1.03  --smt_preprocessing                     true
% 3.20/1.03  --smt_ac_axioms                         fast
% 3.20/1.03  --preprocessed_out                      false
% 3.20/1.03  --preprocessed_stats                    false
% 3.20/1.03  
% 3.20/1.03  ------ Abstraction refinement Options
% 3.20/1.03  
% 3.20/1.03  --abstr_ref                             []
% 3.20/1.03  --abstr_ref_prep                        false
% 3.20/1.03  --abstr_ref_until_sat                   false
% 3.20/1.03  --abstr_ref_sig_restrict                funpre
% 3.20/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.03  --abstr_ref_under                       []
% 3.20/1.03  
% 3.20/1.03  ------ SAT Options
% 3.20/1.03  
% 3.20/1.03  --sat_mode                              false
% 3.20/1.03  --sat_fm_restart_options                ""
% 3.20/1.03  --sat_gr_def                            false
% 3.20/1.03  --sat_epr_types                         true
% 3.20/1.03  --sat_non_cyclic_types                  false
% 3.20/1.03  --sat_finite_models                     false
% 3.20/1.03  --sat_fm_lemmas                         false
% 3.20/1.03  --sat_fm_prep                           false
% 3.20/1.03  --sat_fm_uc_incr                        true
% 3.20/1.03  --sat_out_model                         small
% 3.20/1.03  --sat_out_clauses                       false
% 3.20/1.03  
% 3.20/1.03  ------ QBF Options
% 3.20/1.03  
% 3.20/1.03  --qbf_mode                              false
% 3.20/1.03  --qbf_elim_univ                         false
% 3.20/1.03  --qbf_dom_inst                          none
% 3.20/1.03  --qbf_dom_pre_inst                      false
% 3.20/1.03  --qbf_sk_in                             false
% 3.20/1.03  --qbf_pred_elim                         true
% 3.20/1.03  --qbf_split                             512
% 3.20/1.03  
% 3.20/1.03  ------ BMC1 Options
% 3.20/1.03  
% 3.20/1.03  --bmc1_incremental                      false
% 3.20/1.03  --bmc1_axioms                           reachable_all
% 3.20/1.03  --bmc1_min_bound                        0
% 3.20/1.03  --bmc1_max_bound                        -1
% 3.20/1.03  --bmc1_max_bound_default                -1
% 3.20/1.03  --bmc1_symbol_reachability              true
% 3.20/1.03  --bmc1_property_lemmas                  false
% 3.20/1.03  --bmc1_k_induction                      false
% 3.20/1.03  --bmc1_non_equiv_states                 false
% 3.20/1.03  --bmc1_deadlock                         false
% 3.20/1.03  --bmc1_ucm                              false
% 3.20/1.03  --bmc1_add_unsat_core                   none
% 3.20/1.03  --bmc1_unsat_core_children              false
% 3.20/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.03  --bmc1_out_stat                         full
% 3.20/1.03  --bmc1_ground_init                      false
% 3.20/1.03  --bmc1_pre_inst_next_state              false
% 3.20/1.03  --bmc1_pre_inst_state                   false
% 3.20/1.03  --bmc1_pre_inst_reach_state             false
% 3.20/1.03  --bmc1_out_unsat_core                   false
% 3.20/1.03  --bmc1_aig_witness_out                  false
% 3.20/1.03  --bmc1_verbose                          false
% 3.20/1.03  --bmc1_dump_clauses_tptp                false
% 3.20/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.03  --bmc1_dump_file                        -
% 3.20/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.03  --bmc1_ucm_extend_mode                  1
% 3.20/1.03  --bmc1_ucm_init_mode                    2
% 3.20/1.03  --bmc1_ucm_cone_mode                    none
% 3.20/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.03  --bmc1_ucm_relax_model                  4
% 3.20/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.03  --bmc1_ucm_layered_model                none
% 3.20/1.03  --bmc1_ucm_max_lemma_size               10
% 3.20/1.03  
% 3.20/1.03  ------ AIG Options
% 3.20/1.03  
% 3.20/1.03  --aig_mode                              false
% 3.20/1.03  
% 3.20/1.03  ------ Instantiation Options
% 3.20/1.03  
% 3.20/1.03  --instantiation_flag                    true
% 3.20/1.03  --inst_sos_flag                         false
% 3.20/1.03  --inst_sos_phase                        true
% 3.20/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.03  --inst_lit_sel_side                     none
% 3.20/1.03  --inst_solver_per_active                1400
% 3.20/1.03  --inst_solver_calls_frac                1.
% 3.20/1.03  --inst_passive_queue_type               priority_queues
% 3.20/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.03  --inst_passive_queues_freq              [25;2]
% 3.20/1.03  --inst_dismatching                      true
% 3.20/1.03  --inst_eager_unprocessed_to_passive     true
% 3.20/1.03  --inst_prop_sim_given                   true
% 3.20/1.03  --inst_prop_sim_new                     false
% 3.20/1.03  --inst_subs_new                         false
% 3.20/1.03  --inst_eq_res_simp                      false
% 3.20/1.03  --inst_subs_given                       false
% 3.20/1.03  --inst_orphan_elimination               true
% 3.20/1.03  --inst_learning_loop_flag               true
% 3.20/1.03  --inst_learning_start                   3000
% 3.20/1.03  --inst_learning_factor                  2
% 3.20/1.03  --inst_start_prop_sim_after_learn       3
% 3.20/1.03  --inst_sel_renew                        solver
% 3.20/1.03  --inst_lit_activity_flag                true
% 3.20/1.03  --inst_restr_to_given                   false
% 3.20/1.03  --inst_activity_threshold               500
% 3.20/1.03  --inst_out_proof                        true
% 3.20/1.03  
% 3.20/1.03  ------ Resolution Options
% 3.20/1.03  
% 3.20/1.03  --resolution_flag                       false
% 3.20/1.03  --res_lit_sel                           adaptive
% 3.20/1.03  --res_lit_sel_side                      none
% 3.20/1.03  --res_ordering                          kbo
% 3.20/1.03  --res_to_prop_solver                    active
% 3.20/1.03  --res_prop_simpl_new                    false
% 3.20/1.03  --res_prop_simpl_given                  true
% 3.20/1.03  --res_passive_queue_type                priority_queues
% 3.20/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.03  --res_passive_queues_freq               [15;5]
% 3.20/1.03  --res_forward_subs                      full
% 3.20/1.03  --res_backward_subs                     full
% 3.20/1.03  --res_forward_subs_resolution           true
% 3.20/1.03  --res_backward_subs_resolution          true
% 3.20/1.03  --res_orphan_elimination                true
% 3.20/1.03  --res_time_limit                        2.
% 3.20/1.03  --res_out_proof                         true
% 3.20/1.03  
% 3.20/1.03  ------ Superposition Options
% 3.20/1.03  
% 3.20/1.03  --superposition_flag                    true
% 3.20/1.03  --sup_passive_queue_type                priority_queues
% 3.20/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.03  --demod_completeness_check              fast
% 3.20/1.03  --demod_use_ground                      true
% 3.20/1.03  --sup_to_prop_solver                    passive
% 3.20/1.03  --sup_prop_simpl_new                    true
% 3.20/1.03  --sup_prop_simpl_given                  true
% 3.20/1.03  --sup_fun_splitting                     false
% 3.20/1.03  --sup_smt_interval                      50000
% 3.20/1.03  
% 3.20/1.03  ------ Superposition Simplification Setup
% 3.20/1.03  
% 3.20/1.03  --sup_indices_passive                   []
% 3.20/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.03  --sup_full_bw                           [BwDemod]
% 3.20/1.03  --sup_immed_triv                        [TrivRules]
% 3.20/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.03  --sup_immed_bw_main                     []
% 3.20/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.03  
% 3.20/1.03  ------ Combination Options
% 3.20/1.03  
% 3.20/1.03  --comb_res_mult                         3
% 3.20/1.03  --comb_sup_mult                         2
% 3.20/1.03  --comb_inst_mult                        10
% 3.20/1.03  
% 3.20/1.03  ------ Debug Options
% 3.20/1.03  
% 3.20/1.03  --dbg_backtrace                         false
% 3.20/1.03  --dbg_dump_prop_clauses                 false
% 3.20/1.03  --dbg_dump_prop_clauses_file            -
% 3.20/1.03  --dbg_out_stat                          false
% 3.20/1.03  
% 3.20/1.03  
% 3.20/1.03  
% 3.20/1.03  
% 3.20/1.03  ------ Proving...
% 3.20/1.03  
% 3.20/1.03  
% 3.20/1.03  % SZS status Theorem for theBenchmark.p
% 3.20/1.03  
% 3.20/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/1.03  
% 3.20/1.03  fof(f8,axiom,(
% 3.20/1.03    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f18,plain,(
% 3.20/1.03    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.20/1.03    inference(ennf_transformation,[],[f8])).
% 3.20/1.03  
% 3.20/1.03  fof(f32,plain,(
% 3.20/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.20/1.03    inference(cnf_transformation,[],[f18])).
% 3.20/1.03  
% 3.20/1.03  fof(f10,conjecture,(
% 3.20/1.03    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f11,negated_conjecture,(
% 3.20/1.03    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 3.20/1.03    inference(negated_conjecture,[],[f10])).
% 3.20/1.03  
% 3.20/1.03  fof(f20,plain,(
% 3.20/1.03    ? [X0,X1] : (? [X2] : ((k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 3.20/1.03    inference(ennf_transformation,[],[f11])).
% 3.20/1.03  
% 3.20/1.03  fof(f21,plain,(
% 3.20/1.03    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 3.20/1.03    inference(flattening,[],[f20])).
% 3.20/1.03  
% 3.20/1.03  fof(f23,plain,(
% 3.20/1.03    ( ! [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) => (k5_relat_1(X1,sK2) != k5_relat_1(X1,k7_relat_1(sK2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(sK2,X0))) & v1_relat_1(sK2))) )),
% 3.20/1.03    introduced(choice_axiom,[])).
% 3.20/1.03  
% 3.20/1.03  fof(f22,plain,(
% 3.20/1.03    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 3.20/1.03    introduced(choice_axiom,[])).
% 3.20/1.03  
% 3.20/1.03  fof(f24,plain,(
% 3.20/1.03    (k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 3.20/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 3.20/1.03  
% 3.20/1.03  fof(f36,plain,(
% 3.20/1.03    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 3.20/1.03    inference(cnf_transformation,[],[f24])).
% 3.20/1.03  
% 3.20/1.03  fof(f3,axiom,(
% 3.20/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f13,plain,(
% 3.20/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.20/1.03    inference(ennf_transformation,[],[f3])).
% 3.20/1.03  
% 3.20/1.03  fof(f27,plain,(
% 3.20/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.20/1.03    inference(cnf_transformation,[],[f13])).
% 3.20/1.03  
% 3.20/1.03  fof(f1,axiom,(
% 3.20/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f25,plain,(
% 3.20/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.20/1.03    inference(cnf_transformation,[],[f1])).
% 3.20/1.03  
% 3.20/1.03  fof(f2,axiom,(
% 3.20/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f12,plain,(
% 3.20/1.03    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.20/1.03    inference(ennf_transformation,[],[f2])).
% 3.20/1.03  
% 3.20/1.03  fof(f26,plain,(
% 3.20/1.03    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.20/1.03    inference(cnf_transformation,[],[f12])).
% 3.20/1.03  
% 3.20/1.03  fof(f35,plain,(
% 3.20/1.03    v1_relat_1(sK2)),
% 3.20/1.03    inference(cnf_transformation,[],[f24])).
% 3.20/1.03  
% 3.20/1.03  fof(f6,axiom,(
% 3.20/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f15,plain,(
% 3.20/1.03    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.20/1.03    inference(ennf_transformation,[],[f6])).
% 3.20/1.03  
% 3.20/1.03  fof(f16,plain,(
% 3.20/1.03    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.20/1.03    inference(flattening,[],[f15])).
% 3.20/1.03  
% 3.20/1.03  fof(f30,plain,(
% 3.20/1.03    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.20/1.03    inference(cnf_transformation,[],[f16])).
% 3.20/1.03  
% 3.20/1.03  fof(f34,plain,(
% 3.20/1.03    v1_relat_1(sK1)),
% 3.20/1.03    inference(cnf_transformation,[],[f24])).
% 3.20/1.03  
% 3.20/1.03  fof(f4,axiom,(
% 3.20/1.03    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f28,plain,(
% 3.20/1.03    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.20/1.03    inference(cnf_transformation,[],[f4])).
% 3.20/1.03  
% 3.20/1.03  fof(f7,axiom,(
% 3.20/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f17,plain,(
% 3.20/1.03    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.20/1.03    inference(ennf_transformation,[],[f7])).
% 3.20/1.03  
% 3.20/1.03  fof(f31,plain,(
% 3.20/1.03    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.20/1.03    inference(cnf_transformation,[],[f17])).
% 3.20/1.03  
% 3.20/1.03  fof(f9,axiom,(
% 3.20/1.03    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f19,plain,(
% 3.20/1.03    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.20/1.03    inference(ennf_transformation,[],[f9])).
% 3.20/1.03  
% 3.20/1.03  fof(f33,plain,(
% 3.20/1.03    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.20/1.03    inference(cnf_transformation,[],[f19])).
% 3.20/1.03  
% 3.20/1.03  fof(f5,axiom,(
% 3.20/1.03    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 3.20/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.03  
% 3.20/1.03  fof(f14,plain,(
% 3.20/1.03    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 3.20/1.03    inference(ennf_transformation,[],[f5])).
% 3.20/1.03  
% 3.20/1.03  fof(f29,plain,(
% 3.20/1.03    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 3.20/1.03    inference(cnf_transformation,[],[f14])).
% 3.20/1.03  
% 3.20/1.03  fof(f37,plain,(
% 3.20/1.03    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 3.20/1.03    inference(cnf_transformation,[],[f24])).
% 3.20/1.03  
% 3.20/1.03  cnf(c_7,plain,
% 3.20/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.20/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_137,plain,
% 3.20/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(X0_40,X0_41)),X0_41)
% 3.20/1.03      | ~ v1_relat_1(X0_40) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_378,plain,
% 3.20/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(X0_40,X0_41)),X0_41) = iProver_top
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_10,negated_conjecture,
% 3.20/1.03      ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
% 3.20/1.03      inference(cnf_transformation,[],[f36]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_134,negated_conjecture,
% 3.20/1.03      ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_380,plain,
% 3.20/1.03      ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) = iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_134]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_2,plain,
% 3.20/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.20/1.03      inference(cnf_transformation,[],[f27]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_142,plain,
% 3.20/1.03      ( ~ r1_tarski(X0_41,X1_41) | k3_xboole_0(X0_41,X1_41) = X0_41 ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_373,plain,
% 3.20/1.03      ( k3_xboole_0(X0_41,X1_41) = X0_41
% 3.20/1.03      | r1_tarski(X0_41,X1_41) != iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_142]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_606,plain,
% 3.20/1.03      ( k3_xboole_0(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) = k2_relat_1(sK1) ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_380,c_373]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_0,plain,
% 3.20/1.03      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.20/1.03      inference(cnf_transformation,[],[f25]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_144,plain,
% 3.20/1.03      ( k3_xboole_0(X0_41,X1_41) = k3_xboole_0(X1_41,X0_41) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_1,plain,
% 3.20/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 3.20/1.03      inference(cnf_transformation,[],[f26]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_143,plain,
% 3.20/1.03      ( ~ r1_tarski(X0_41,X1_41)
% 3.20/1.03      | r1_tarski(k3_xboole_0(X0_41,X2_41),X1_41) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_372,plain,
% 3.20/1.03      ( r1_tarski(X0_41,X1_41) != iProver_top
% 3.20/1.03      | r1_tarski(k3_xboole_0(X0_41,X2_41),X1_41) = iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_684,plain,
% 3.20/1.03      ( r1_tarski(X0_41,X1_41) != iProver_top
% 3.20/1.03      | r1_tarski(k3_xboole_0(X2_41,X0_41),X1_41) = iProver_top ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_144,c_372]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_865,plain,
% 3.20/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0_41) != iProver_top
% 3.20/1.03      | r1_tarski(k2_relat_1(sK1),X0_41) = iProver_top ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_606,c_684]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_1050,plain,
% 3.20/1.03      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top
% 3.20/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_378,c_865]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_11,negated_conjecture,
% 3.20/1.03      ( v1_relat_1(sK2) ),
% 3.20/1.03      inference(cnf_transformation,[],[f35]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_14,plain,
% 3.20/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_762,plain,
% 3.20/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0)
% 3.20/1.03      | ~ v1_relat_1(sK2) ),
% 3.20/1.03      inference(instantiation,[status(thm)],[c_137]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_763,plain,
% 3.20/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0) = iProver_top
% 3.20/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_876,plain,
% 3.20/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0) != iProver_top
% 3.20/1.03      | r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 3.20/1.03      inference(instantiation,[status(thm)],[c_865]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_1125,plain,
% 3.20/1.03      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 3.20/1.03      inference(global_propositional_subsumption,
% 3.20/1.03                [status(thm)],
% 3.20/1.03                [c_1050,c_14,c_763,c_876]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_5,plain,
% 3.20/1.03      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.20/1.03      | ~ v1_relat_1(X0)
% 3.20/1.03      | k8_relat_1(X1,X0) = X0 ),
% 3.20/1.03      inference(cnf_transformation,[],[f30]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_139,plain,
% 3.20/1.03      ( ~ r1_tarski(k2_relat_1(X0_40),X0_41)
% 3.20/1.03      | ~ v1_relat_1(X0_40)
% 3.20/1.03      | k8_relat_1(X0_41,X0_40) = X0_40 ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_376,plain,
% 3.20/1.03      ( k8_relat_1(X0_41,X0_40) = X0_40
% 3.20/1.03      | r1_tarski(k2_relat_1(X0_40),X0_41) != iProver_top
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_1241,plain,
% 3.20/1.03      ( k8_relat_1(sK0,sK1) = sK1 | v1_relat_1(sK1) != iProver_top ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_1125,c_376]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_12,negated_conjecture,
% 3.20/1.03      ( v1_relat_1(sK1) ),
% 3.20/1.03      inference(cnf_transformation,[],[f34]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_13,plain,
% 3.20/1.03      ( v1_relat_1(sK1) = iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_178,plain,
% 3.20/1.03      ( k8_relat_1(X0_41,X0_40) = X0_40
% 3.20/1.03      | r1_tarski(k2_relat_1(X0_40),X0_41) != iProver_top
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_180,plain,
% 3.20/1.03      ( k8_relat_1(sK0,sK1) = sK1
% 3.20/1.03      | r1_tarski(k2_relat_1(sK1),sK0) != iProver_top
% 3.20/1.03      | v1_relat_1(sK1) != iProver_top ),
% 3.20/1.03      inference(instantiation,[status(thm)],[c_178]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_1456,plain,
% 3.20/1.03      ( k8_relat_1(sK0,sK1) = sK1 ),
% 3.20/1.03      inference(global_propositional_subsumption,
% 3.20/1.03                [status(thm)],
% 3.20/1.03                [c_1241,c_13,c_14,c_180,c_763,c_876]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_132,negated_conjecture,
% 3.20/1.03      ( v1_relat_1(sK1) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_382,plain,
% 3.20/1.03      ( v1_relat_1(sK1) = iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_132]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_133,negated_conjecture,
% 3.20/1.03      ( v1_relat_1(sK2) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_381,plain,
% 3.20/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_133]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_3,plain,
% 3.20/1.03      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.20/1.03      inference(cnf_transformation,[],[f28]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_141,plain,
% 3.20/1.03      ( v1_relat_1(k6_relat_1(X0_41)) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_374,plain,
% 3.20/1.03      ( v1_relat_1(k6_relat_1(X0_41)) = iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_141]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_6,plain,
% 3.20/1.03      ( ~ v1_relat_1(X0)
% 3.20/1.03      | ~ v1_relat_1(X1)
% 3.20/1.03      | ~ v1_relat_1(X2)
% 3.20/1.03      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 3.20/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_138,plain,
% 3.20/1.03      ( ~ v1_relat_1(X0_40)
% 3.20/1.03      | ~ v1_relat_1(X1_40)
% 3.20/1.03      | ~ v1_relat_1(X2_40)
% 3.20/1.03      | k5_relat_1(k5_relat_1(X1_40,X0_40),X2_40) = k5_relat_1(X1_40,k5_relat_1(X0_40,X2_40)) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_377,plain,
% 3.20/1.03      ( k5_relat_1(k5_relat_1(X0_40,X1_40),X2_40) = k5_relat_1(X0_40,k5_relat_1(X1_40,X2_40))
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top
% 3.20/1.03      | v1_relat_1(X1_40) != iProver_top
% 3.20/1.03      | v1_relat_1(X2_40) != iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_1336,plain,
% 3.20/1.03      ( k5_relat_1(X0_40,k5_relat_1(k6_relat_1(X0_41),X1_40)) = k5_relat_1(k5_relat_1(X0_40,k6_relat_1(X0_41)),X1_40)
% 3.20/1.03      | v1_relat_1(X1_40) != iProver_top
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_374,c_377]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_5868,plain,
% 3.20/1.03      ( k5_relat_1(k5_relat_1(X0_40,k6_relat_1(X0_41)),sK2) = k5_relat_1(X0_40,k5_relat_1(k6_relat_1(X0_41),sK2))
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_381,c_1336]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_8,plain,
% 3.20/1.03      ( ~ v1_relat_1(X0)
% 3.20/1.03      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.20/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_136,plain,
% 3.20/1.03      ( ~ v1_relat_1(X0_40)
% 3.20/1.03      | k5_relat_1(k6_relat_1(X0_41),X0_40) = k7_relat_1(X0_40,X0_41) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_379,plain,
% 3.20/1.03      ( k5_relat_1(k6_relat_1(X0_41),X0_40) = k7_relat_1(X0_40,X0_41)
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_775,plain,
% 3.20/1.03      ( k5_relat_1(k6_relat_1(X0_41),sK2) = k7_relat_1(sK2,X0_41) ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_381,c_379]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_5883,plain,
% 3.20/1.03      ( k5_relat_1(k5_relat_1(X0_40,k6_relat_1(X0_41)),sK2) = k5_relat_1(X0_40,k7_relat_1(sK2,X0_41))
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 3.20/1.03      inference(light_normalisation,[status(thm)],[c_5868,c_775]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_6687,plain,
% 3.20/1.03      ( k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0_41)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0_41)) ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_382,c_5883]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_4,plain,
% 3.20/1.03      ( ~ v1_relat_1(X0)
% 3.20/1.03      | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 3.20/1.03      inference(cnf_transformation,[],[f29]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_140,plain,
% 3.20/1.03      ( ~ v1_relat_1(X0_40)
% 3.20/1.03      | k5_relat_1(X0_40,k6_relat_1(X0_41)) = k8_relat_1(X0_41,X0_40) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_375,plain,
% 3.20/1.03      ( k5_relat_1(X0_40,k6_relat_1(X0_41)) = k8_relat_1(X0_41,X0_40)
% 3.20/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 3.20/1.03      inference(predicate_to_equality,[status(thm)],[c_140]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_704,plain,
% 3.20/1.03      ( k5_relat_1(sK1,k6_relat_1(X0_41)) = k8_relat_1(X0_41,sK1) ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_382,c_375]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_6693,plain,
% 3.20/1.03      ( k5_relat_1(k8_relat_1(X0_41,sK1),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0_41)) ),
% 3.20/1.03      inference(light_normalisation,[status(thm)],[c_6687,c_704]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_6702,plain,
% 3.20/1.03      ( k5_relat_1(sK1,k7_relat_1(sK2,sK0)) = k5_relat_1(sK1,sK2) ),
% 3.20/1.03      inference(superposition,[status(thm)],[c_1456,c_6693]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_146,plain,( X0_40 = X0_40 ),theory(equality) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_527,plain,
% 3.20/1.03      ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 3.20/1.03      inference(instantiation,[status(thm)],[c_146]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_148,plain,
% 3.20/1.03      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 3.20/1.03      theory(equality) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_477,plain,
% 3.20/1.03      ( k5_relat_1(sK1,k7_relat_1(sK2,sK0)) != X0_40
% 3.20/1.03      | k5_relat_1(sK1,sK2) != X0_40
% 3.20/1.03      | k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
% 3.20/1.03      inference(instantiation,[status(thm)],[c_148]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_526,plain,
% 3.20/1.03      ( k5_relat_1(sK1,k7_relat_1(sK2,sK0)) != k5_relat_1(sK1,sK2)
% 3.20/1.03      | k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0))
% 3.20/1.03      | k5_relat_1(sK1,sK2) != k5_relat_1(sK1,sK2) ),
% 3.20/1.03      inference(instantiation,[status(thm)],[c_477]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_9,negated_conjecture,
% 3.20/1.03      ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
% 3.20/1.03      inference(cnf_transformation,[],[f37]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(c_135,negated_conjecture,
% 3.20/1.03      ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
% 3.20/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 3.20/1.03  
% 3.20/1.03  cnf(contradiction,plain,
% 3.20/1.03      ( $false ),
% 3.20/1.03      inference(minisat,[status(thm)],[c_6702,c_527,c_526,c_135]) ).
% 3.20/1.03  
% 3.20/1.03  
% 3.20/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/1.03  
% 3.20/1.03  ------                               Statistics
% 3.20/1.03  
% 3.20/1.03  ------ General
% 3.20/1.03  
% 3.20/1.03  abstr_ref_over_cycles:                  0
% 3.20/1.03  abstr_ref_under_cycles:                 0
% 3.20/1.03  gc_basic_clause_elim:                   0
% 3.20/1.03  forced_gc_time:                         0
% 3.20/1.03  parsing_time:                           0.01
% 3.20/1.03  unif_index_cands_time:                  0.
% 3.20/1.03  unif_index_add_time:                    0.
% 3.20/1.03  orderings_time:                         0.
% 3.20/1.03  out_proof_time:                         0.009
% 3.20/1.03  total_time:                             0.216
% 3.20/1.03  num_of_symbols:                         48
% 3.20/1.03  num_of_terms:                           6387
% 3.20/1.03  
% 3.20/1.03  ------ Preprocessing
% 3.20/1.03  
% 3.20/1.03  num_of_splits:                          0
% 3.20/1.03  num_of_split_atoms:                     0
% 3.20/1.03  num_of_reused_defs:                     0
% 3.20/1.03  num_eq_ax_congr_red:                    10
% 3.20/1.03  num_of_sem_filtered_clauses:            1
% 3.20/1.03  num_of_subtypes:                        2
% 3.20/1.03  monotx_restored_types:                  0
% 3.20/1.03  sat_num_of_epr_types:                   0
% 3.20/1.03  sat_num_of_non_cyclic_types:            0
% 3.20/1.03  sat_guarded_non_collapsed_types:        2
% 3.20/1.03  num_pure_diseq_elim:                    0
% 3.20/1.03  simp_replaced_by:                       0
% 3.20/1.03  res_preprocessed:                       60
% 3.20/1.03  prep_upred:                             0
% 3.20/1.03  prep_unflattend:                        0
% 3.20/1.03  smt_new_axioms:                         0
% 3.20/1.03  pred_elim_cands:                        2
% 3.20/1.03  pred_elim:                              0
% 3.20/1.03  pred_elim_cl:                           0
% 3.20/1.03  pred_elim_cycles:                       1
% 3.20/1.03  merged_defs:                            0
% 3.20/1.03  merged_defs_ncl:                        0
% 3.20/1.03  bin_hyper_res:                          0
% 3.20/1.03  prep_cycles:                            3
% 3.20/1.03  pred_elim_time:                         0.
% 3.20/1.03  splitting_time:                         0.
% 3.20/1.03  sem_filter_time:                        0.
% 3.20/1.03  monotx_time:                            0.
% 3.20/1.03  subtype_inf_time:                       0.
% 3.20/1.03  
% 3.20/1.03  ------ Problem properties
% 3.20/1.03  
% 3.20/1.03  clauses:                                13
% 3.20/1.03  conjectures:                            4
% 3.20/1.03  epr:                                    2
% 3.20/1.03  horn:                                   13
% 3.20/1.03  ground:                                 4
% 3.20/1.03  unary:                                  6
% 3.20/1.03  binary:                                 5
% 3.20/1.03  lits:                                   23
% 3.20/1.03  lits_eq:                                7
% 3.20/1.03  fd_pure:                                0
% 3.20/1.03  fd_pseudo:                              0
% 3.20/1.03  fd_cond:                                0
% 3.20/1.03  fd_pseudo_cond:                         0
% 3.20/1.03  ac_symbols:                             0
% 3.20/1.03  
% 3.20/1.03  ------ Propositional Solver
% 3.20/1.03  
% 3.20/1.03  prop_solver_calls:                      25
% 3.20/1.03  prop_fast_solver_calls:                 368
% 3.20/1.03  smt_solver_calls:                       0
% 3.20/1.03  smt_fast_solver_calls:                  0
% 3.20/1.03  prop_num_of_clauses:                    2711
% 3.20/1.03  prop_preprocess_simplified:             7557
% 3.20/1.03  prop_fo_subsumed:                       4
% 3.20/1.03  prop_solver_time:                       0.
% 3.20/1.03  smt_solver_time:                        0.
% 3.20/1.03  smt_fast_solver_time:                   0.
% 3.20/1.03  prop_fast_solver_time:                  0.
% 3.20/1.03  prop_unsat_core_time:                   0.
% 3.20/1.03  
% 3.20/1.03  ------ QBF
% 3.20/1.03  
% 3.20/1.03  qbf_q_res:                              0
% 3.20/1.03  qbf_num_tautologies:                    0
% 3.20/1.03  qbf_prep_cycles:                        0
% 3.20/1.03  
% 3.20/1.03  ------ BMC1
% 3.20/1.03  
% 3.20/1.03  bmc1_current_bound:                     -1
% 3.20/1.03  bmc1_last_solved_bound:                 -1
% 3.20/1.03  bmc1_unsat_core_size:                   -1
% 3.20/1.03  bmc1_unsat_core_parents_size:           -1
% 3.20/1.03  bmc1_merge_next_fun:                    0
% 3.20/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.03  
% 3.20/1.03  ------ Instantiation
% 3.20/1.03  
% 3.20/1.03  inst_num_of_clauses:                    1047
% 3.20/1.03  inst_num_in_passive:                    446
% 3.20/1.03  inst_num_in_active:                     413
% 3.20/1.03  inst_num_in_unprocessed:                190
% 3.20/1.03  inst_num_of_loops:                      420
% 3.20/1.03  inst_num_of_learning_restarts:          0
% 3.20/1.03  inst_num_moves_active_passive:          4
% 3.20/1.03  inst_lit_activity:                      0
% 3.20/1.03  inst_lit_activity_moves:                0
% 3.20/1.03  inst_num_tautologies:                   0
% 3.20/1.03  inst_num_prop_implied:                  0
% 3.20/1.03  inst_num_existing_simplified:           0
% 3.20/1.03  inst_num_eq_res_simplified:             0
% 3.20/1.03  inst_num_child_elim:                    0
% 3.20/1.03  inst_num_of_dismatching_blockings:      475
% 3.20/1.03  inst_num_of_non_proper_insts:           917
% 3.20/1.03  inst_num_of_duplicates:                 0
% 3.20/1.03  inst_inst_num_from_inst_to_res:         0
% 3.20/1.03  inst_dismatching_checking_time:         0.
% 3.20/1.03  
% 3.20/1.03  ------ Resolution
% 3.20/1.03  
% 3.20/1.03  res_num_of_clauses:                     0
% 3.20/1.03  res_num_in_passive:                     0
% 3.20/1.03  res_num_in_active:                      0
% 3.20/1.03  res_num_of_loops:                       63
% 3.20/1.03  res_forward_subset_subsumed:            111
% 3.20/1.03  res_backward_subset_subsumed:           6
% 3.20/1.03  res_forward_subsumed:                   0
% 3.20/1.03  res_backward_subsumed:                  0
% 3.20/1.03  res_forward_subsumption_resolution:     0
% 3.20/1.03  res_backward_subsumption_resolution:    0
% 3.20/1.03  res_clause_to_clause_subsumption:       382
% 3.20/1.03  res_orphan_elimination:                 0
% 3.20/1.03  res_tautology_del:                      113
% 3.20/1.03  res_num_eq_res_simplified:              0
% 3.20/1.03  res_num_sel_changes:                    0
% 3.20/1.03  res_moves_from_active_to_pass:          0
% 3.20/1.03  
% 3.20/1.03  ------ Superposition
% 3.20/1.03  
% 3.20/1.03  sup_time_total:                         0.
% 3.20/1.03  sup_time_generating:                    0.
% 3.20/1.03  sup_time_sim_full:                      0.
% 3.20/1.03  sup_time_sim_immed:                     0.
% 3.20/1.03  
% 3.20/1.03  sup_num_of_clauses:                     126
% 3.20/1.03  sup_num_in_active:                      84
% 3.20/1.03  sup_num_in_passive:                     42
% 3.20/1.03  sup_num_of_loops:                       83
% 3.20/1.03  sup_fw_superposition:                   139
% 3.20/1.03  sup_bw_superposition:                   76
% 3.20/1.03  sup_immediate_simplified:               33
% 3.20/1.03  sup_given_eliminated:                   0
% 3.20/1.03  comparisons_done:                       0
% 3.20/1.03  comparisons_avoided:                    0
% 3.20/1.03  
% 3.20/1.03  ------ Simplifications
% 3.20/1.03  
% 3.20/1.03  
% 3.20/1.03  sim_fw_subset_subsumed:                 0
% 3.20/1.03  sim_bw_subset_subsumed:                 1
% 3.20/1.03  sim_fw_subsumed:                        2
% 3.20/1.03  sim_bw_subsumed:                        0
% 3.20/1.03  sim_fw_subsumption_res:                 0
% 3.20/1.03  sim_bw_subsumption_res:                 0
% 3.20/1.03  sim_tautology_del:                      11
% 3.20/1.03  sim_eq_tautology_del:                   2
% 3.20/1.03  sim_eq_res_simp:                        0
% 3.20/1.03  sim_fw_demodulated:                     4
% 3.20/1.03  sim_bw_demodulated:                     4
% 3.20/1.03  sim_light_normalised:                   24
% 3.20/1.03  sim_joinable_taut:                      0
% 3.20/1.03  sim_joinable_simp:                      0
% 3.20/1.03  sim_ac_normalised:                      0
% 3.20/1.03  sim_smt_subsumption:                    0
% 3.20/1.03  
%------------------------------------------------------------------------------
