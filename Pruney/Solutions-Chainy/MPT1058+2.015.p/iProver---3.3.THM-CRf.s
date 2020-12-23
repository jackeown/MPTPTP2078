%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:14 EST 2020

% Result     : Theorem 43.24s
% Output     : CNFRefutation 43.24s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 265 expanded)
%              Number of clauses        :   49 (  75 expanded)
%              Number of leaves         :   18 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  178 ( 435 expanded)
%              Number of equality atoms :  113 ( 286 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f96,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f65,f91,f91])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f64,f68,f68])).

fof(f97,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f69,f90,f91])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f95,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f63,f68,f68,f90])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k6_subset_1(k2_relat_1(X1),k6_subset_1(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f70,f90])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4)
        & r1_tarski(k10_relat_1(X0,sK4),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2)
          & r1_tarski(k10_relat_1(sK2,X2),X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    & r1_tarski(k10_relat_1(sK2,sK4),sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f52,f51])).

fof(f88,plain,(
    r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f83,f90])).

fof(f89,plain,(
    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_241,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1074,plain,
    ( X0 != X1
    | k10_relat_1(sK2,sK4) != X1
    | k10_relat_1(sK2,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_1518,plain,
    ( X0 != k10_relat_1(sK2,sK4)
    | k10_relat_1(sK2,sK4) = X0
    | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_149439,plain,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4)
    | k10_relat_1(sK2,sK4) = k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4)))
    | k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) != k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_10,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_11,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1036,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_11])).

cnf(c_6,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_660,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_646,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1828,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_646])).

cnf(c_23,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_50,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7785,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1828,c_47,c_50])).

cnf(c_7794,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_660,c_7785])).

cnf(c_109626,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1036,c_7794])).

cnf(c_9,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1799,plain,
    ( k6_subset_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k6_subset_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_1036,c_9])).

cnf(c_1801,plain,
    ( k6_subset_1(X0,k6_subset_1(X1,k6_subset_1(X1,X0))) = k6_subset_1(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1799,c_11])).

cnf(c_649,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k6_subset_1(k2_relat_1(X0),k6_subset_1(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_658,plain,
    ( k10_relat_1(X0,k6_subset_1(k2_relat_1(X0),k6_subset_1(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4188,plain,
    ( k10_relat_1(k6_relat_1(X0),k6_subset_1(k2_relat_1(k6_relat_1(X0)),k6_subset_1(k2_relat_1(k6_relat_1(X0)),X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_649,c_658])).

cnf(c_4193,plain,
    ( k10_relat_1(k6_relat_1(X0),k6_subset_1(X0,k6_subset_1(X0,X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_4188,c_14])).

cnf(c_4388,plain,
    ( k10_relat_1(k6_relat_1(X0),k6_subset_1(X1,k6_subset_1(X1,X0))) = k10_relat_1(k6_relat_1(X0),k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1801,c_4193])).

cnf(c_4416,plain,
    ( k10_relat_1(k6_relat_1(X0),k6_subset_1(X1,k6_subset_1(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_4388,c_4193])).

cnf(c_109673,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_109626,c_11,c_4416])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_644,plain,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7795,plain,
    ( k9_relat_1(k6_relat_1(sK3),k10_relat_1(k6_relat_1(sK3),k10_relat_1(sK2,sK4))) = k10_relat_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_644,c_7785])).

cnf(c_111103,plain,
    ( k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_109673,c_7795])).

cnf(c_924,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X0
    | k10_relat_1(sK2,sK4) != X0
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_33043,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4)))
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    | k10_relat_1(sK2,sK4) != k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(X1,k6_subset_1(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_952,plain,
    ( ~ v1_relat_1(sK2)
    | k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_13909,plain,
    ( ~ v1_relat_1(sK2)
    | k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_2189,plain,
    ( X0 != X1
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X1
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_8399,plain,
    ( X0 != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_13908,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4)))
    | k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_8399])).

cnf(c_240,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3104,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_1073,plain,
    ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_28,negated_conjecture,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_149439,c_111103,c_33043,c_13909,c_13908,c_3104,c_1073,c_28,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 43.24/6.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.24/6.03  
% 43.24/6.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.24/6.03  
% 43.24/6.03  ------  iProver source info
% 43.24/6.03  
% 43.24/6.03  git: date: 2020-06-30 10:37:57 +0100
% 43.24/6.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.24/6.03  git: non_committed_changes: false
% 43.24/6.03  git: last_make_outside_of_git: false
% 43.24/6.03  
% 43.24/6.03  ------ 
% 43.24/6.03  
% 43.24/6.03  ------ Input Options
% 43.24/6.03  
% 43.24/6.03  --out_options                           all
% 43.24/6.03  --tptp_safe_out                         true
% 43.24/6.03  --problem_path                          ""
% 43.24/6.03  --include_path                          ""
% 43.24/6.03  --clausifier                            res/vclausify_rel
% 43.24/6.03  --clausifier_options                    --mode clausify
% 43.24/6.03  --stdin                                 false
% 43.24/6.03  --stats_out                             sel
% 43.24/6.03  
% 43.24/6.03  ------ General Options
% 43.24/6.03  
% 43.24/6.03  --fof                                   false
% 43.24/6.03  --time_out_real                         604.99
% 43.24/6.03  --time_out_virtual                      -1.
% 43.24/6.03  --symbol_type_check                     false
% 43.24/6.03  --clausify_out                          false
% 43.24/6.03  --sig_cnt_out                           false
% 43.24/6.03  --trig_cnt_out                          false
% 43.24/6.03  --trig_cnt_out_tolerance                1.
% 43.24/6.03  --trig_cnt_out_sk_spl                   false
% 43.24/6.03  --abstr_cl_out                          false
% 43.24/6.03  
% 43.24/6.03  ------ Global Options
% 43.24/6.03  
% 43.24/6.03  --schedule                              none
% 43.24/6.03  --add_important_lit                     false
% 43.24/6.03  --prop_solver_per_cl                    1000
% 43.24/6.03  --min_unsat_core                        false
% 43.24/6.03  --soft_assumptions                      false
% 43.24/6.03  --soft_lemma_size                       3
% 43.24/6.03  --prop_impl_unit_size                   0
% 43.24/6.03  --prop_impl_unit                        []
% 43.24/6.03  --share_sel_clauses                     true
% 43.24/6.03  --reset_solvers                         false
% 43.24/6.03  --bc_imp_inh                            [conj_cone]
% 43.24/6.03  --conj_cone_tolerance                   3.
% 43.24/6.03  --extra_neg_conj                        none
% 43.24/6.03  --large_theory_mode                     true
% 43.24/6.03  --prolific_symb_bound                   200
% 43.24/6.03  --lt_threshold                          2000
% 43.24/6.03  --clause_weak_htbl                      true
% 43.24/6.03  --gc_record_bc_elim                     false
% 43.24/6.03  
% 43.24/6.03  ------ Preprocessing Options
% 43.24/6.03  
% 43.24/6.03  --preprocessing_flag                    true
% 43.24/6.03  --time_out_prep_mult                    0.1
% 43.24/6.03  --splitting_mode                        input
% 43.24/6.03  --splitting_grd                         true
% 43.24/6.03  --splitting_cvd                         false
% 43.24/6.03  --splitting_cvd_svl                     false
% 43.24/6.03  --splitting_nvd                         32
% 43.24/6.03  --sub_typing                            true
% 43.24/6.03  --prep_gs_sim                           false
% 43.24/6.03  --prep_unflatten                        true
% 43.24/6.03  --prep_res_sim                          true
% 43.24/6.03  --prep_upred                            true
% 43.24/6.03  --prep_sem_filter                       exhaustive
% 43.24/6.03  --prep_sem_filter_out                   false
% 43.24/6.03  --pred_elim                             false
% 43.24/6.03  --res_sim_input                         true
% 43.24/6.03  --eq_ax_congr_red                       true
% 43.24/6.03  --pure_diseq_elim                       true
% 43.24/6.03  --brand_transform                       false
% 43.24/6.03  --non_eq_to_eq                          false
% 43.24/6.03  --prep_def_merge                        true
% 43.24/6.03  --prep_def_merge_prop_impl              false
% 43.24/6.03  --prep_def_merge_mbd                    true
% 43.24/6.03  --prep_def_merge_tr_red                 false
% 43.24/6.03  --prep_def_merge_tr_cl                  false
% 43.24/6.03  --smt_preprocessing                     true
% 43.24/6.03  --smt_ac_axioms                         fast
% 43.24/6.03  --preprocessed_out                      false
% 43.24/6.03  --preprocessed_stats                    false
% 43.24/6.03  
% 43.24/6.03  ------ Abstraction refinement Options
% 43.24/6.03  
% 43.24/6.03  --abstr_ref                             []
% 43.24/6.03  --abstr_ref_prep                        false
% 43.24/6.03  --abstr_ref_until_sat                   false
% 43.24/6.03  --abstr_ref_sig_restrict                funpre
% 43.24/6.03  --abstr_ref_af_restrict_to_split_sk     false
% 43.24/6.03  --abstr_ref_under                       []
% 43.24/6.03  
% 43.24/6.03  ------ SAT Options
% 43.24/6.03  
% 43.24/6.03  --sat_mode                              false
% 43.24/6.03  --sat_fm_restart_options                ""
% 43.24/6.03  --sat_gr_def                            false
% 43.24/6.03  --sat_epr_types                         true
% 43.24/6.03  --sat_non_cyclic_types                  false
% 43.24/6.03  --sat_finite_models                     false
% 43.24/6.03  --sat_fm_lemmas                         false
% 43.24/6.03  --sat_fm_prep                           false
% 43.24/6.03  --sat_fm_uc_incr                        true
% 43.24/6.03  --sat_out_model                         small
% 43.24/6.03  --sat_out_clauses                       false
% 43.24/6.03  
% 43.24/6.03  ------ QBF Options
% 43.24/6.03  
% 43.24/6.03  --qbf_mode                              false
% 43.24/6.03  --qbf_elim_univ                         false
% 43.24/6.03  --qbf_dom_inst                          none
% 43.24/6.03  --qbf_dom_pre_inst                      false
% 43.24/6.03  --qbf_sk_in                             false
% 43.24/6.03  --qbf_pred_elim                         true
% 43.24/6.03  --qbf_split                             512
% 43.24/6.03  
% 43.24/6.03  ------ BMC1 Options
% 43.24/6.03  
% 43.24/6.03  --bmc1_incremental                      false
% 43.24/6.03  --bmc1_axioms                           reachable_all
% 43.24/6.03  --bmc1_min_bound                        0
% 43.24/6.03  --bmc1_max_bound                        -1
% 43.24/6.03  --bmc1_max_bound_default                -1
% 43.24/6.03  --bmc1_symbol_reachability              true
% 43.24/6.03  --bmc1_property_lemmas                  false
% 43.24/6.03  --bmc1_k_induction                      false
% 43.24/6.03  --bmc1_non_equiv_states                 false
% 43.24/6.03  --bmc1_deadlock                         false
% 43.24/6.03  --bmc1_ucm                              false
% 43.24/6.03  --bmc1_add_unsat_core                   none
% 43.24/6.03  --bmc1_unsat_core_children              false
% 43.24/6.03  --bmc1_unsat_core_extrapolate_axioms    false
% 43.24/6.03  --bmc1_out_stat                         full
% 43.24/6.03  --bmc1_ground_init                      false
% 43.24/6.03  --bmc1_pre_inst_next_state              false
% 43.24/6.03  --bmc1_pre_inst_state                   false
% 43.24/6.03  --bmc1_pre_inst_reach_state             false
% 43.24/6.03  --bmc1_out_unsat_core                   false
% 43.24/6.03  --bmc1_aig_witness_out                  false
% 43.24/6.03  --bmc1_verbose                          false
% 43.24/6.03  --bmc1_dump_clauses_tptp                false
% 43.24/6.03  --bmc1_dump_unsat_core_tptp             false
% 43.24/6.03  --bmc1_dump_file                        -
% 43.24/6.03  --bmc1_ucm_expand_uc_limit              128
% 43.24/6.03  --bmc1_ucm_n_expand_iterations          6
% 43.24/6.03  --bmc1_ucm_extend_mode                  1
% 43.24/6.03  --bmc1_ucm_init_mode                    2
% 43.24/6.03  --bmc1_ucm_cone_mode                    none
% 43.24/6.03  --bmc1_ucm_reduced_relation_type        0
% 43.24/6.03  --bmc1_ucm_relax_model                  4
% 43.24/6.03  --bmc1_ucm_full_tr_after_sat            true
% 43.24/6.03  --bmc1_ucm_expand_neg_assumptions       false
% 43.24/6.03  --bmc1_ucm_layered_model                none
% 43.24/6.03  --bmc1_ucm_max_lemma_size               10
% 43.24/6.03  
% 43.24/6.03  ------ AIG Options
% 43.24/6.03  
% 43.24/6.03  --aig_mode                              false
% 43.24/6.03  
% 43.24/6.03  ------ Instantiation Options
% 43.24/6.03  
% 43.24/6.03  --instantiation_flag                    true
% 43.24/6.03  --inst_sos_flag                         false
% 43.24/6.03  --inst_sos_phase                        true
% 43.24/6.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.24/6.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.24/6.03  --inst_lit_sel_side                     num_symb
% 43.24/6.03  --inst_solver_per_active                1400
% 43.24/6.03  --inst_solver_calls_frac                1.
% 43.24/6.03  --inst_passive_queue_type               priority_queues
% 43.24/6.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.24/6.03  --inst_passive_queues_freq              [25;2]
% 43.24/6.03  --inst_dismatching                      true
% 43.24/6.03  --inst_eager_unprocessed_to_passive     true
% 43.24/6.03  --inst_prop_sim_given                   true
% 43.24/6.03  --inst_prop_sim_new                     false
% 43.24/6.03  --inst_subs_new                         false
% 43.24/6.03  --inst_eq_res_simp                      false
% 43.24/6.03  --inst_subs_given                       false
% 43.24/6.03  --inst_orphan_elimination               true
% 43.24/6.03  --inst_learning_loop_flag               true
% 43.24/6.03  --inst_learning_start                   3000
% 43.24/6.03  --inst_learning_factor                  2
% 43.24/6.03  --inst_start_prop_sim_after_learn       3
% 43.24/6.03  --inst_sel_renew                        solver
% 43.24/6.03  --inst_lit_activity_flag                true
% 43.24/6.03  --inst_restr_to_given                   false
% 43.24/6.03  --inst_activity_threshold               500
% 43.24/6.03  --inst_out_proof                        true
% 43.24/6.03  
% 43.24/6.03  ------ Resolution Options
% 43.24/6.03  
% 43.24/6.03  --resolution_flag                       true
% 43.24/6.03  --res_lit_sel                           adaptive
% 43.24/6.03  --res_lit_sel_side                      none
% 43.24/6.03  --res_ordering                          kbo
% 43.24/6.03  --res_to_prop_solver                    active
% 43.24/6.03  --res_prop_simpl_new                    false
% 43.24/6.03  --res_prop_simpl_given                  true
% 43.24/6.03  --res_passive_queue_type                priority_queues
% 43.24/6.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.24/6.03  --res_passive_queues_freq               [15;5]
% 43.24/6.03  --res_forward_subs                      full
% 43.24/6.03  --res_backward_subs                     full
% 43.24/6.03  --res_forward_subs_resolution           true
% 43.24/6.03  --res_backward_subs_resolution          true
% 43.24/6.03  --res_orphan_elimination                true
% 43.24/6.03  --res_time_limit                        2.
% 43.24/6.03  --res_out_proof                         true
% 43.24/6.03  
% 43.24/6.03  ------ Superposition Options
% 43.24/6.03  
% 43.24/6.03  --superposition_flag                    true
% 43.24/6.03  --sup_passive_queue_type                priority_queues
% 43.24/6.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.24/6.03  --sup_passive_queues_freq               [1;4]
% 43.24/6.03  --demod_completeness_check              fast
% 43.24/6.03  --demod_use_ground                      true
% 43.24/6.03  --sup_to_prop_solver                    passive
% 43.24/6.03  --sup_prop_simpl_new                    true
% 43.24/6.03  --sup_prop_simpl_given                  true
% 43.24/6.03  --sup_fun_splitting                     false
% 43.24/6.03  --sup_smt_interval                      50000
% 43.24/6.03  
% 43.24/6.03  ------ Superposition Simplification Setup
% 43.24/6.03  
% 43.24/6.03  --sup_indices_passive                   []
% 43.24/6.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.24/6.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.24/6.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.24/6.03  --sup_full_triv                         [TrivRules;PropSubs]
% 43.24/6.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.24/6.03  --sup_full_bw                           [BwDemod]
% 43.24/6.03  --sup_immed_triv                        [TrivRules]
% 43.24/6.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.24/6.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.24/6.03  --sup_immed_bw_main                     []
% 43.24/6.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.24/6.03  --sup_input_triv                        [Unflattening;TrivRules]
% 43.24/6.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.24/6.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.24/6.03  
% 43.24/6.03  ------ Combination Options
% 43.24/6.03  
% 43.24/6.03  --comb_res_mult                         3
% 43.24/6.03  --comb_sup_mult                         2
% 43.24/6.03  --comb_inst_mult                        10
% 43.24/6.03  
% 43.24/6.03  ------ Debug Options
% 43.24/6.03  
% 43.24/6.03  --dbg_backtrace                         false
% 43.24/6.03  --dbg_dump_prop_clauses                 false
% 43.24/6.03  --dbg_dump_prop_clauses_file            -
% 43.24/6.03  --dbg_out_stat                          false
% 43.24/6.03  ------ Parsing...
% 43.24/6.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.24/6.03  
% 43.24/6.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 43.24/6.03  
% 43.24/6.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.24/6.03  
% 43.24/6.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.24/6.03  ------ Proving...
% 43.24/6.03  ------ Problem Properties 
% 43.24/6.03  
% 43.24/6.03  
% 43.24/6.03  clauses                                 32
% 43.24/6.03  conjectures                             4
% 43.24/6.03  EPR                                     7
% 43.24/6.03  Horn                                    29
% 43.24/6.03  unary                                   15
% 43.24/6.03  binary                                  7
% 43.24/6.03  lits                                    71
% 43.24/6.03  lits eq                                 17
% 43.24/6.03  fd_pure                                 0
% 43.24/6.03  fd_pseudo                               0
% 43.24/6.03  fd_cond                                 1
% 43.24/6.03  fd_pseudo_cond                          3
% 43.24/6.03  AC symbols                              0
% 43.24/6.03  
% 43.24/6.03  ------ Input Options Time Limit: Unbounded
% 43.24/6.03  
% 43.24/6.03  
% 43.24/6.03  ------ 
% 43.24/6.03  Current options:
% 43.24/6.03  ------ 
% 43.24/6.03  
% 43.24/6.03  ------ Input Options
% 43.24/6.03  
% 43.24/6.03  --out_options                           all
% 43.24/6.03  --tptp_safe_out                         true
% 43.24/6.03  --problem_path                          ""
% 43.24/6.03  --include_path                          ""
% 43.24/6.03  --clausifier                            res/vclausify_rel
% 43.24/6.03  --clausifier_options                    --mode clausify
% 43.24/6.03  --stdin                                 false
% 43.24/6.03  --stats_out                             sel
% 43.24/6.03  
% 43.24/6.03  ------ General Options
% 43.24/6.03  
% 43.24/6.03  --fof                                   false
% 43.24/6.03  --time_out_real                         604.99
% 43.24/6.03  --time_out_virtual                      -1.
% 43.24/6.03  --symbol_type_check                     false
% 43.24/6.03  --clausify_out                          false
% 43.24/6.03  --sig_cnt_out                           false
% 43.24/6.03  --trig_cnt_out                          false
% 43.24/6.03  --trig_cnt_out_tolerance                1.
% 43.24/6.03  --trig_cnt_out_sk_spl                   false
% 43.24/6.03  --abstr_cl_out                          false
% 43.24/6.03  
% 43.24/6.03  ------ Global Options
% 43.24/6.03  
% 43.24/6.03  --schedule                              none
% 43.24/6.03  --add_important_lit                     false
% 43.24/6.03  --prop_solver_per_cl                    1000
% 43.24/6.03  --min_unsat_core                        false
% 43.24/6.03  --soft_assumptions                      false
% 43.24/6.03  --soft_lemma_size                       3
% 43.24/6.03  --prop_impl_unit_size                   0
% 43.24/6.03  --prop_impl_unit                        []
% 43.24/6.03  --share_sel_clauses                     true
% 43.24/6.03  --reset_solvers                         false
% 43.24/6.03  --bc_imp_inh                            [conj_cone]
% 43.24/6.03  --conj_cone_tolerance                   3.
% 43.24/6.03  --extra_neg_conj                        none
% 43.24/6.03  --large_theory_mode                     true
% 43.24/6.03  --prolific_symb_bound                   200
% 43.24/6.03  --lt_threshold                          2000
% 43.24/6.03  --clause_weak_htbl                      true
% 43.24/6.03  --gc_record_bc_elim                     false
% 43.24/6.03  
% 43.24/6.03  ------ Preprocessing Options
% 43.24/6.03  
% 43.24/6.03  --preprocessing_flag                    true
% 43.24/6.03  --time_out_prep_mult                    0.1
% 43.24/6.03  --splitting_mode                        input
% 43.24/6.03  --splitting_grd                         true
% 43.24/6.03  --splitting_cvd                         false
% 43.24/6.03  --splitting_cvd_svl                     false
% 43.24/6.03  --splitting_nvd                         32
% 43.24/6.03  --sub_typing                            true
% 43.24/6.03  --prep_gs_sim                           false
% 43.24/6.03  --prep_unflatten                        true
% 43.24/6.03  --prep_res_sim                          true
% 43.24/6.03  --prep_upred                            true
% 43.24/6.03  --prep_sem_filter                       exhaustive
% 43.24/6.03  --prep_sem_filter_out                   false
% 43.24/6.03  --pred_elim                             false
% 43.24/6.03  --res_sim_input                         true
% 43.24/6.03  --eq_ax_congr_red                       true
% 43.24/6.03  --pure_diseq_elim                       true
% 43.24/6.03  --brand_transform                       false
% 43.24/6.03  --non_eq_to_eq                          false
% 43.24/6.03  --prep_def_merge                        true
% 43.24/6.03  --prep_def_merge_prop_impl              false
% 43.24/6.03  --prep_def_merge_mbd                    true
% 43.24/6.03  --prep_def_merge_tr_red                 false
% 43.24/6.03  --prep_def_merge_tr_cl                  false
% 43.24/6.03  --smt_preprocessing                     true
% 43.24/6.03  --smt_ac_axioms                         fast
% 43.24/6.03  --preprocessed_out                      false
% 43.24/6.03  --preprocessed_stats                    false
% 43.24/6.03  
% 43.24/6.03  ------ Abstraction refinement Options
% 43.24/6.03  
% 43.24/6.03  --abstr_ref                             []
% 43.24/6.03  --abstr_ref_prep                        false
% 43.24/6.03  --abstr_ref_until_sat                   false
% 43.24/6.03  --abstr_ref_sig_restrict                funpre
% 43.24/6.03  --abstr_ref_af_restrict_to_split_sk     false
% 43.24/6.03  --abstr_ref_under                       []
% 43.24/6.03  
% 43.24/6.03  ------ SAT Options
% 43.24/6.03  
% 43.24/6.03  --sat_mode                              false
% 43.24/6.03  --sat_fm_restart_options                ""
% 43.24/6.03  --sat_gr_def                            false
% 43.24/6.03  --sat_epr_types                         true
% 43.24/6.03  --sat_non_cyclic_types                  false
% 43.24/6.03  --sat_finite_models                     false
% 43.24/6.03  --sat_fm_lemmas                         false
% 43.24/6.03  --sat_fm_prep                           false
% 43.24/6.03  --sat_fm_uc_incr                        true
% 43.24/6.03  --sat_out_model                         small
% 43.24/6.03  --sat_out_clauses                       false
% 43.24/6.03  
% 43.24/6.03  ------ QBF Options
% 43.24/6.03  
% 43.24/6.03  --qbf_mode                              false
% 43.24/6.03  --qbf_elim_univ                         false
% 43.24/6.03  --qbf_dom_inst                          none
% 43.24/6.03  --qbf_dom_pre_inst                      false
% 43.24/6.03  --qbf_sk_in                             false
% 43.24/6.03  --qbf_pred_elim                         true
% 43.24/6.03  --qbf_split                             512
% 43.24/6.03  
% 43.24/6.03  ------ BMC1 Options
% 43.24/6.03  
% 43.24/6.03  --bmc1_incremental                      false
% 43.24/6.03  --bmc1_axioms                           reachable_all
% 43.24/6.03  --bmc1_min_bound                        0
% 43.24/6.03  --bmc1_max_bound                        -1
% 43.24/6.03  --bmc1_max_bound_default                -1
% 43.24/6.03  --bmc1_symbol_reachability              true
% 43.24/6.03  --bmc1_property_lemmas                  false
% 43.24/6.03  --bmc1_k_induction                      false
% 43.24/6.03  --bmc1_non_equiv_states                 false
% 43.24/6.03  --bmc1_deadlock                         false
% 43.24/6.03  --bmc1_ucm                              false
% 43.24/6.03  --bmc1_add_unsat_core                   none
% 43.24/6.03  --bmc1_unsat_core_children              false
% 43.24/6.03  --bmc1_unsat_core_extrapolate_axioms    false
% 43.24/6.03  --bmc1_out_stat                         full
% 43.24/6.03  --bmc1_ground_init                      false
% 43.24/6.03  --bmc1_pre_inst_next_state              false
% 43.24/6.03  --bmc1_pre_inst_state                   false
% 43.24/6.03  --bmc1_pre_inst_reach_state             false
% 43.24/6.03  --bmc1_out_unsat_core                   false
% 43.24/6.03  --bmc1_aig_witness_out                  false
% 43.24/6.03  --bmc1_verbose                          false
% 43.24/6.03  --bmc1_dump_clauses_tptp                false
% 43.24/6.03  --bmc1_dump_unsat_core_tptp             false
% 43.24/6.03  --bmc1_dump_file                        -
% 43.24/6.03  --bmc1_ucm_expand_uc_limit              128
% 43.24/6.03  --bmc1_ucm_n_expand_iterations          6
% 43.24/6.03  --bmc1_ucm_extend_mode                  1
% 43.24/6.03  --bmc1_ucm_init_mode                    2
% 43.24/6.03  --bmc1_ucm_cone_mode                    none
% 43.24/6.03  --bmc1_ucm_reduced_relation_type        0
% 43.24/6.03  --bmc1_ucm_relax_model                  4
% 43.24/6.03  --bmc1_ucm_full_tr_after_sat            true
% 43.24/6.03  --bmc1_ucm_expand_neg_assumptions       false
% 43.24/6.03  --bmc1_ucm_layered_model                none
% 43.24/6.03  --bmc1_ucm_max_lemma_size               10
% 43.24/6.03  
% 43.24/6.03  ------ AIG Options
% 43.24/6.03  
% 43.24/6.03  --aig_mode                              false
% 43.24/6.03  
% 43.24/6.03  ------ Instantiation Options
% 43.24/6.03  
% 43.24/6.03  --instantiation_flag                    true
% 43.24/6.03  --inst_sos_flag                         false
% 43.24/6.03  --inst_sos_phase                        true
% 43.24/6.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.24/6.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.24/6.03  --inst_lit_sel_side                     num_symb
% 43.24/6.03  --inst_solver_per_active                1400
% 43.24/6.03  --inst_solver_calls_frac                1.
% 43.24/6.03  --inst_passive_queue_type               priority_queues
% 43.24/6.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.24/6.03  --inst_passive_queues_freq              [25;2]
% 43.24/6.03  --inst_dismatching                      true
% 43.24/6.03  --inst_eager_unprocessed_to_passive     true
% 43.24/6.03  --inst_prop_sim_given                   true
% 43.24/6.03  --inst_prop_sim_new                     false
% 43.24/6.03  --inst_subs_new                         false
% 43.24/6.03  --inst_eq_res_simp                      false
% 43.24/6.03  --inst_subs_given                       false
% 43.24/6.03  --inst_orphan_elimination               true
% 43.24/6.03  --inst_learning_loop_flag               true
% 43.24/6.03  --inst_learning_start                   3000
% 43.24/6.03  --inst_learning_factor                  2
% 43.24/6.03  --inst_start_prop_sim_after_learn       3
% 43.24/6.03  --inst_sel_renew                        solver
% 43.24/6.03  --inst_lit_activity_flag                true
% 43.24/6.03  --inst_restr_to_given                   false
% 43.24/6.03  --inst_activity_threshold               500
% 43.24/6.03  --inst_out_proof                        true
% 43.24/6.03  
% 43.24/6.03  ------ Resolution Options
% 43.24/6.03  
% 43.24/6.03  --resolution_flag                       true
% 43.24/6.03  --res_lit_sel                           adaptive
% 43.24/6.03  --res_lit_sel_side                      none
% 43.24/6.03  --res_ordering                          kbo
% 43.24/6.03  --res_to_prop_solver                    active
% 43.24/6.03  --res_prop_simpl_new                    false
% 43.24/6.03  --res_prop_simpl_given                  true
% 43.24/6.03  --res_passive_queue_type                priority_queues
% 43.24/6.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.24/6.03  --res_passive_queues_freq               [15;5]
% 43.24/6.03  --res_forward_subs                      full
% 43.24/6.03  --res_backward_subs                     full
% 43.24/6.03  --res_forward_subs_resolution           true
% 43.24/6.03  --res_backward_subs_resolution          true
% 43.24/6.03  --res_orphan_elimination                true
% 43.24/6.03  --res_time_limit                        2.
% 43.24/6.03  --res_out_proof                         true
% 43.24/6.03  
% 43.24/6.03  ------ Superposition Options
% 43.24/6.03  
% 43.24/6.03  --superposition_flag                    true
% 43.24/6.03  --sup_passive_queue_type                priority_queues
% 43.24/6.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.24/6.03  --sup_passive_queues_freq               [1;4]
% 43.24/6.03  --demod_completeness_check              fast
% 43.24/6.03  --demod_use_ground                      true
% 43.24/6.03  --sup_to_prop_solver                    passive
% 43.24/6.03  --sup_prop_simpl_new                    true
% 43.24/6.03  --sup_prop_simpl_given                  true
% 43.24/6.03  --sup_fun_splitting                     false
% 43.24/6.03  --sup_smt_interval                      50000
% 43.24/6.03  
% 43.24/6.03  ------ Superposition Simplification Setup
% 43.24/6.03  
% 43.24/6.03  --sup_indices_passive                   []
% 43.24/6.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.24/6.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.24/6.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.24/6.03  --sup_full_triv                         [TrivRules;PropSubs]
% 43.24/6.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.24/6.03  --sup_full_bw                           [BwDemod]
% 43.24/6.03  --sup_immed_triv                        [TrivRules]
% 43.24/6.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.24/6.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.24/6.03  --sup_immed_bw_main                     []
% 43.24/6.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.24/6.03  --sup_input_triv                        [Unflattening;TrivRules]
% 43.24/6.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.24/6.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.24/6.03  
% 43.24/6.03  ------ Combination Options
% 43.24/6.03  
% 43.24/6.03  --comb_res_mult                         3
% 43.24/6.03  --comb_sup_mult                         2
% 43.24/6.03  --comb_inst_mult                        10
% 43.24/6.03  
% 43.24/6.03  ------ Debug Options
% 43.24/6.03  
% 43.24/6.03  --dbg_backtrace                         false
% 43.24/6.03  --dbg_dump_prop_clauses                 false
% 43.24/6.03  --dbg_dump_prop_clauses_file            -
% 43.24/6.03  --dbg_out_stat                          false
% 43.24/6.03  
% 43.24/6.03  
% 43.24/6.03  
% 43.24/6.03  
% 43.24/6.03  ------ Proving...
% 43.24/6.03  
% 43.24/6.03  
% 43.24/6.03  % SZS status Theorem for theBenchmark.p
% 43.24/6.03  
% 43.24/6.03  % SZS output start CNFRefutation for theBenchmark.p
% 43.24/6.03  
% 43.24/6.03  fof(f10,axiom,(
% 43.24/6.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f65,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 43.24/6.03    inference(cnf_transformation,[],[f10])).
% 43.24/6.03  
% 43.24/6.03  fof(f11,axiom,(
% 43.24/6.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f66,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 43.24/6.03    inference(cnf_transformation,[],[f11])).
% 43.24/6.03  
% 43.24/6.03  fof(f12,axiom,(
% 43.24/6.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f67,plain,(
% 43.24/6.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.24/6.03    inference(cnf_transformation,[],[f12])).
% 43.24/6.03  
% 43.24/6.03  fof(f91,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 43.24/6.03    inference(definition_unfolding,[],[f66,f67])).
% 43.24/6.03  
% 43.24/6.03  fof(f96,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 43.24/6.03    inference(definition_unfolding,[],[f65,f91,f91])).
% 43.24/6.03  
% 43.24/6.03  fof(f14,axiom,(
% 43.24/6.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f69,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 43.24/6.03    inference(cnf_transformation,[],[f14])).
% 43.24/6.03  
% 43.24/6.03  fof(f9,axiom,(
% 43.24/6.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f64,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.24/6.03    inference(cnf_transformation,[],[f9])).
% 43.24/6.03  
% 43.24/6.03  fof(f13,axiom,(
% 43.24/6.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f68,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 43.24/6.03    inference(cnf_transformation,[],[f13])).
% 43.24/6.03  
% 43.24/6.03  fof(f90,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 43.24/6.03    inference(definition_unfolding,[],[f64,f68,f68])).
% 43.24/6.03  
% 43.24/6.03  fof(f97,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 43.24/6.03    inference(definition_unfolding,[],[f69,f90,f91])).
% 43.24/6.03  
% 43.24/6.03  fof(f5,axiom,(
% 43.24/6.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f60,plain,(
% 43.24/6.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 43.24/6.03    inference(cnf_transformation,[],[f5])).
% 43.24/6.03  
% 43.24/6.03  fof(f93,plain,(
% 43.24/6.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 43.24/6.03    inference(definition_unfolding,[],[f60,f68])).
% 43.24/6.03  
% 43.24/6.03  fof(f17,axiom,(
% 43.24/6.03    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f73,plain,(
% 43.24/6.03    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 43.24/6.03    inference(cnf_transformation,[],[f17])).
% 43.24/6.03  
% 43.24/6.03  fof(f22,axiom,(
% 43.24/6.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f37,plain,(
% 43.24/6.03    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 43.24/6.03    inference(ennf_transformation,[],[f22])).
% 43.24/6.03  
% 43.24/6.03  fof(f38,plain,(
% 43.24/6.03    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 43.24/6.03    inference(flattening,[],[f37])).
% 43.24/6.03  
% 43.24/6.03  fof(f84,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 43.24/6.03    inference(cnf_transformation,[],[f38])).
% 43.24/6.03  
% 43.24/6.03  fof(f19,axiom,(
% 43.24/6.03    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f80,plain,(
% 43.24/6.03    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 43.24/6.03    inference(cnf_transformation,[],[f19])).
% 43.24/6.03  
% 43.24/6.03  fof(f81,plain,(
% 43.24/6.03    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 43.24/6.03    inference(cnf_transformation,[],[f19])).
% 43.24/6.03  
% 43.24/6.03  fof(f8,axiom,(
% 43.24/6.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f63,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.24/6.03    inference(cnf_transformation,[],[f8])).
% 43.24/6.03  
% 43.24/6.03  fof(f95,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 43.24/6.03    inference(definition_unfolding,[],[f63,f68,f68,f90])).
% 43.24/6.03  
% 43.24/6.03  fof(f15,axiom,(
% 43.24/6.03    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f30,plain,(
% 43.24/6.03    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 43.24/6.03    inference(ennf_transformation,[],[f15])).
% 43.24/6.03  
% 43.24/6.03  fof(f70,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 43.24/6.03    inference(cnf_transformation,[],[f30])).
% 43.24/6.03  
% 43.24/6.03  fof(f98,plain,(
% 43.24/6.03    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k6_subset_1(k2_relat_1(X1),k6_subset_1(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 43.24/6.03    inference(definition_unfolding,[],[f70,f90])).
% 43.24/6.03  
% 43.24/6.03  fof(f24,conjecture,(
% 43.24/6.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f25,negated_conjecture,(
% 43.24/6.03    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 43.24/6.03    inference(negated_conjecture,[],[f24])).
% 43.24/6.03  
% 43.24/6.03  fof(f40,plain,(
% 43.24/6.03    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 43.24/6.03    inference(ennf_transformation,[],[f25])).
% 43.24/6.03  
% 43.24/6.03  fof(f41,plain,(
% 43.24/6.03    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 43.24/6.03    inference(flattening,[],[f40])).
% 43.24/6.03  
% 43.24/6.03  fof(f52,plain,(
% 43.24/6.03    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4) & r1_tarski(k10_relat_1(X0,sK4),sK3))) )),
% 43.24/6.03    introduced(choice_axiom,[])).
% 43.24/6.03  
% 43.24/6.03  fof(f51,plain,(
% 43.24/6.03    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2) & r1_tarski(k10_relat_1(sK2,X2),X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 43.24/6.03    introduced(choice_axiom,[])).
% 43.24/6.03  
% 43.24/6.03  fof(f53,plain,(
% 43.24/6.03    (k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) & r1_tarski(k10_relat_1(sK2,sK4),sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 43.24/6.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f52,f51])).
% 43.24/6.03  
% 43.24/6.03  fof(f88,plain,(
% 43.24/6.03    r1_tarski(k10_relat_1(sK2,sK4),sK3)),
% 43.24/6.03    inference(cnf_transformation,[],[f53])).
% 43.24/6.03  
% 43.24/6.03  fof(f21,axiom,(
% 43.24/6.03    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 43.24/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.24/6.03  
% 43.24/6.03  fof(f36,plain,(
% 43.24/6.03    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 43.24/6.03    inference(ennf_transformation,[],[f21])).
% 43.24/6.03  
% 43.24/6.03  fof(f83,plain,(
% 43.24/6.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 43.24/6.03    inference(cnf_transformation,[],[f36])).
% 43.24/6.03  
% 43.24/6.03  fof(f99,plain,(
% 43.24/6.03    ( ! [X2,X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 43.24/6.03    inference(definition_unfolding,[],[f83,f90])).
% 43.24/6.03  
% 43.24/6.03  fof(f89,plain,(
% 43.24/6.03    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)),
% 43.24/6.03    inference(cnf_transformation,[],[f53])).
% 43.24/6.03  
% 43.24/6.03  fof(f86,plain,(
% 43.24/6.03    v1_relat_1(sK2)),
% 43.24/6.03    inference(cnf_transformation,[],[f53])).
% 43.24/6.03  
% 43.24/6.03  cnf(c_241,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_1074,plain,
% 43.24/6.03      ( X0 != X1
% 43.24/6.03      | k10_relat_1(sK2,sK4) != X1
% 43.24/6.03      | k10_relat_1(sK2,sK4) = X0 ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_241]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_1518,plain,
% 43.24/6.03      ( X0 != k10_relat_1(sK2,sK4)
% 43.24/6.03      | k10_relat_1(sK2,sK4) = X0
% 43.24/6.03      | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_1074]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_149439,plain,
% 43.24/6.03      ( k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4)
% 43.24/6.03      | k10_relat_1(sK2,sK4) = k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4)))
% 43.24/6.03      | k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) != k10_relat_1(sK2,sK4) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_1518]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_10,plain,
% 43.24/6.03      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 43.24/6.03      inference(cnf_transformation,[],[f96]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_11,plain,
% 43.24/6.03      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
% 43.24/6.03      inference(cnf_transformation,[],[f97]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_1036,plain,
% 43.24/6.03      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_10,c_11]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_6,plain,
% 43.24/6.03      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 43.24/6.03      inference(cnf_transformation,[],[f93]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_660,plain,
% 43.24/6.03      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 43.24/6.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_14,plain,
% 43.24/6.03      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 43.24/6.03      inference(cnf_transformation,[],[f73]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_26,plain,
% 43.24/6.03      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 43.24/6.03      | ~ v1_funct_1(X1)
% 43.24/6.03      | ~ v1_relat_1(X1)
% 43.24/6.03      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 43.24/6.03      inference(cnf_transformation,[],[f84]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_646,plain,
% 43.24/6.03      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 43.24/6.03      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 43.24/6.03      | v1_funct_1(X0) != iProver_top
% 43.24/6.03      | v1_relat_1(X0) != iProver_top ),
% 43.24/6.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_1828,plain,
% 43.24/6.03      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
% 43.24/6.03      | r1_tarski(X1,X0) != iProver_top
% 43.24/6.03      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 43.24/6.03      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_14,c_646]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_23,plain,
% 43.24/6.03      ( v1_relat_1(k6_relat_1(X0)) ),
% 43.24/6.03      inference(cnf_transformation,[],[f80]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_47,plain,
% 43.24/6.03      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 43.24/6.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_22,plain,
% 43.24/6.03      ( v1_funct_1(k6_relat_1(X0)) ),
% 43.24/6.03      inference(cnf_transformation,[],[f81]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_50,plain,
% 43.24/6.03      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 43.24/6.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_7785,plain,
% 43.24/6.03      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
% 43.24/6.03      | r1_tarski(X1,X0) != iProver_top ),
% 43.24/6.03      inference(global_propositional_subsumption,
% 43.24/6.03                [status(thm)],
% 43.24/6.03                [c_1828,c_47,c_50]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_7794,plain,
% 43.24/6.03      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_660,c_7785]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_109626,plain,
% 43.24/6.03      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_1036,c_7794]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_9,plain,
% 43.24/6.03      ( k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
% 43.24/6.03      inference(cnf_transformation,[],[f95]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_1799,plain,
% 43.24/6.03      ( k6_subset_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k6_subset_1(X0,X1) ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_1036,c_9]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_1801,plain,
% 43.24/6.03      ( k6_subset_1(X0,k6_subset_1(X1,k6_subset_1(X1,X0))) = k6_subset_1(X0,X1) ),
% 43.24/6.03      inference(demodulation,[status(thm)],[c_1799,c_11]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_649,plain,
% 43.24/6.03      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 43.24/6.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_12,plain,
% 43.24/6.03      ( ~ v1_relat_1(X0)
% 43.24/6.03      | k10_relat_1(X0,k6_subset_1(k2_relat_1(X0),k6_subset_1(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 43.24/6.03      inference(cnf_transformation,[],[f98]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_658,plain,
% 43.24/6.03      ( k10_relat_1(X0,k6_subset_1(k2_relat_1(X0),k6_subset_1(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 43.24/6.03      | v1_relat_1(X0) != iProver_top ),
% 43.24/6.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_4188,plain,
% 43.24/6.03      ( k10_relat_1(k6_relat_1(X0),k6_subset_1(k2_relat_1(k6_relat_1(X0)),k6_subset_1(k2_relat_1(k6_relat_1(X0)),X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_649,c_658]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_4193,plain,
% 43.24/6.03      ( k10_relat_1(k6_relat_1(X0),k6_subset_1(X0,k6_subset_1(X0,X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 43.24/6.03      inference(light_normalisation,[status(thm)],[c_4188,c_14]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_4388,plain,
% 43.24/6.03      ( k10_relat_1(k6_relat_1(X0),k6_subset_1(X1,k6_subset_1(X1,X0))) = k10_relat_1(k6_relat_1(X0),k6_subset_1(X0,k6_subset_1(X0,X1))) ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_1801,c_4193]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_4416,plain,
% 43.24/6.03      ( k10_relat_1(k6_relat_1(X0),k6_subset_1(X1,k6_subset_1(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 43.24/6.03      inference(light_normalisation,[status(thm)],[c_4388,c_4193]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_109673,plain,
% 43.24/6.03      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
% 43.24/6.03      inference(demodulation,[status(thm)],[c_109626,c_11,c_4416]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_29,negated_conjecture,
% 43.24/6.03      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
% 43.24/6.03      inference(cnf_transformation,[],[f88]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_644,plain,
% 43.24/6.03      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) = iProver_top ),
% 43.24/6.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_7795,plain,
% 43.24/6.03      ( k9_relat_1(k6_relat_1(sK3),k10_relat_1(k6_relat_1(sK3),k10_relat_1(sK2,sK4))) = k10_relat_1(sK2,sK4) ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_644,c_7785]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_111103,plain,
% 43.24/6.03      ( k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(sK2,sK4) ),
% 43.24/6.03      inference(superposition,[status(thm)],[c_109673,c_7795]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_924,plain,
% 43.24/6.03      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X0
% 43.24/6.03      | k10_relat_1(sK2,sK4) != X0
% 43.24/6.03      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_241]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_33043,plain,
% 43.24/6.03      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4)))
% 43.24/6.03      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4)
% 43.24/6.03      | k10_relat_1(sK2,sK4) != k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_924]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_25,plain,
% 43.24/6.03      ( ~ v1_relat_1(X0)
% 43.24/6.03      | k6_subset_1(X1,k6_subset_1(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 43.24/6.03      inference(cnf_transformation,[],[f99]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_952,plain,
% 43.24/6.03      ( ~ v1_relat_1(sK2)
% 43.24/6.03      | k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_25]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_13909,plain,
% 43.24/6.03      ( ~ v1_relat_1(sK2)
% 43.24/6.03      | k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_952]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_2189,plain,
% 43.24/6.03      ( X0 != X1
% 43.24/6.03      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X1
% 43.24/6.03      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0 ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_241]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_8399,plain,
% 43.24/6.03      ( X0 != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
% 43.24/6.03      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0
% 43.24/6.03      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_2189]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_13908,plain,
% 43.24/6.03      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
% 43.24/6.03      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4)))
% 43.24/6.03      | k6_subset_1(sK3,k6_subset_1(sK3,k10_relat_1(sK2,sK4))) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_8399]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_240,plain,( X0 = X0 ),theory(equality) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_3104,plain,
% 43.24/6.03      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_240]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_1073,plain,
% 43.24/6.03      ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
% 43.24/6.03      inference(instantiation,[status(thm)],[c_240]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_28,negated_conjecture,
% 43.24/6.03      ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 43.24/6.03      inference(cnf_transformation,[],[f89]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(c_31,negated_conjecture,
% 43.24/6.03      ( v1_relat_1(sK2) ),
% 43.24/6.03      inference(cnf_transformation,[],[f86]) ).
% 43.24/6.03  
% 43.24/6.03  cnf(contradiction,plain,
% 43.24/6.03      ( $false ),
% 43.24/6.03      inference(minisat,
% 43.24/6.03                [status(thm)],
% 43.24/6.03                [c_149439,c_111103,c_33043,c_13909,c_13908,c_3104,c_1073,
% 43.24/6.03                 c_28,c_31]) ).
% 43.24/6.03  
% 43.24/6.03  
% 43.24/6.03  % SZS output end CNFRefutation for theBenchmark.p
% 43.24/6.03  
% 43.24/6.03  ------                               Statistics
% 43.24/6.03  
% 43.24/6.03  ------ Selected
% 43.24/6.03  
% 43.24/6.03  total_time:                             5.037
% 43.24/6.03  
%------------------------------------------------------------------------------
