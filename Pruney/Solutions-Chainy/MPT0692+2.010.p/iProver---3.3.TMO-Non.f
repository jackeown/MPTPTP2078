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

% Result     : Timeout 59.65s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   92 ( 164 expanded)
%              Number of clauses        :   44 (  52 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  225 ( 470 expanded)
%              Number of equality atoms :   91 ( 166 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,
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

fof(f30,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).

fof(f46,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_605,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_611,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_612,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1400,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_612])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_614,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2785,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_614])).

cnf(c_2974,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k2_relat_1(sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_605,c_2785])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_613,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3199,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2974,c_613])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_603,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_610,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_606,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1123,plain,
    ( k6_subset_1(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_614])).

cnf(c_1597,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,k9_relat_1(X0,k10_relat_1(X0,X1)))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_1123])).

cnf(c_8432,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_603,c_1597])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_604,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_608,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1587,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_608])).

cnf(c_16,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6778,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1587,c_16])).

cnf(c_8448,plain,
    ( k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8432,c_6778])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_609,plain,
    ( k10_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_233070,plain,
    ( k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0
    | r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8448,c_609])).

cnf(c_234320,plain,
    ( r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top
    | k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_233070,c_16])).

cnf(c_234321,plain,
    ( k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0
    | r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_234320])).

cnf(c_234330,plain,
    ( k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3199,c_234321])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1167,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(resolution,[status(thm)],[c_0,c_12])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1332,plain,
    ( ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_1167,c_10])).

cnf(c_809,plain,
    ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_234330,c_1332,c_809,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.65/7.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.65/7.99  
% 59.65/7.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.65/7.99  
% 59.65/7.99  ------  iProver source info
% 59.65/7.99  
% 59.65/7.99  git: date: 2020-06-30 10:37:57 +0100
% 59.65/7.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.65/7.99  git: non_committed_changes: false
% 59.65/7.99  git: last_make_outside_of_git: false
% 59.65/7.99  
% 59.65/7.99  ------ 
% 59.65/7.99  
% 59.65/7.99  ------ Input Options
% 59.65/7.99  
% 59.65/7.99  --out_options                           all
% 59.65/7.99  --tptp_safe_out                         true
% 59.65/7.99  --problem_path                          ""
% 59.65/7.99  --include_path                          ""
% 59.65/7.99  --clausifier                            res/vclausify_rel
% 59.65/7.99  --clausifier_options                    --mode clausify
% 59.65/7.99  --stdin                                 false
% 59.65/7.99  --stats_out                             sel
% 59.65/7.99  
% 59.65/7.99  ------ General Options
% 59.65/7.99  
% 59.65/7.99  --fof                                   false
% 59.65/7.99  --time_out_real                         604.99
% 59.65/7.99  --time_out_virtual                      -1.
% 59.65/7.99  --symbol_type_check                     false
% 59.65/7.99  --clausify_out                          false
% 59.65/7.99  --sig_cnt_out                           false
% 59.65/7.99  --trig_cnt_out                          false
% 59.65/7.99  --trig_cnt_out_tolerance                1.
% 59.65/7.99  --trig_cnt_out_sk_spl                   false
% 59.65/7.99  --abstr_cl_out                          false
% 59.65/7.99  
% 59.65/7.99  ------ Global Options
% 59.65/7.99  
% 59.65/7.99  --schedule                              none
% 59.65/7.99  --add_important_lit                     false
% 59.65/7.99  --prop_solver_per_cl                    1000
% 59.65/7.99  --min_unsat_core                        false
% 59.65/7.99  --soft_assumptions                      false
% 59.65/7.99  --soft_lemma_size                       3
% 59.65/7.99  --prop_impl_unit_size                   0
% 59.65/7.99  --prop_impl_unit                        []
% 59.65/7.99  --share_sel_clauses                     true
% 59.65/7.99  --reset_solvers                         false
% 59.65/7.99  --bc_imp_inh                            [conj_cone]
% 59.65/7.99  --conj_cone_tolerance                   3.
% 59.65/7.99  --extra_neg_conj                        none
% 59.65/7.99  --large_theory_mode                     true
% 59.65/7.99  --prolific_symb_bound                   200
% 59.65/7.99  --lt_threshold                          2000
% 59.65/7.99  --clause_weak_htbl                      true
% 59.65/7.99  --gc_record_bc_elim                     false
% 59.65/7.99  
% 59.65/7.99  ------ Preprocessing Options
% 59.65/7.99  
% 59.65/7.99  --preprocessing_flag                    true
% 59.65/7.99  --time_out_prep_mult                    0.1
% 59.65/7.99  --splitting_mode                        input
% 59.65/7.99  --splitting_grd                         true
% 59.65/7.99  --splitting_cvd                         false
% 59.65/7.99  --splitting_cvd_svl                     false
% 59.65/7.99  --splitting_nvd                         32
% 59.65/7.99  --sub_typing                            true
% 59.65/7.99  --prep_gs_sim                           false
% 59.65/7.99  --prep_unflatten                        true
% 59.65/7.99  --prep_res_sim                          true
% 59.65/7.99  --prep_upred                            true
% 59.65/7.99  --prep_sem_filter                       exhaustive
% 59.65/7.99  --prep_sem_filter_out                   false
% 59.65/7.99  --pred_elim                             false
% 59.65/7.99  --res_sim_input                         true
% 59.65/7.99  --eq_ax_congr_red                       true
% 59.65/7.99  --pure_diseq_elim                       true
% 59.65/7.99  --brand_transform                       false
% 59.65/7.99  --non_eq_to_eq                          false
% 59.65/7.99  --prep_def_merge                        true
% 59.65/7.99  --prep_def_merge_prop_impl              false
% 59.65/7.99  --prep_def_merge_mbd                    true
% 59.65/7.99  --prep_def_merge_tr_red                 false
% 59.65/7.99  --prep_def_merge_tr_cl                  false
% 59.65/7.99  --smt_preprocessing                     true
% 59.65/7.99  --smt_ac_axioms                         fast
% 59.65/7.99  --preprocessed_out                      false
% 59.65/7.99  --preprocessed_stats                    false
% 59.65/7.99  
% 59.65/7.99  ------ Abstraction refinement Options
% 59.65/7.99  
% 59.65/7.99  --abstr_ref                             []
% 59.65/7.99  --abstr_ref_prep                        false
% 59.65/7.99  --abstr_ref_until_sat                   false
% 59.65/7.99  --abstr_ref_sig_restrict                funpre
% 59.65/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.65/7.99  --abstr_ref_under                       []
% 59.65/7.99  
% 59.65/7.99  ------ SAT Options
% 59.65/7.99  
% 59.65/7.99  --sat_mode                              false
% 59.65/7.99  --sat_fm_restart_options                ""
% 59.65/7.99  --sat_gr_def                            false
% 59.65/7.99  --sat_epr_types                         true
% 59.65/7.99  --sat_non_cyclic_types                  false
% 59.65/7.99  --sat_finite_models                     false
% 59.65/7.99  --sat_fm_lemmas                         false
% 59.65/7.99  --sat_fm_prep                           false
% 59.65/7.99  --sat_fm_uc_incr                        true
% 59.65/7.99  --sat_out_model                         small
% 59.65/7.99  --sat_out_clauses                       false
% 59.65/7.99  
% 59.65/7.99  ------ QBF Options
% 59.65/7.99  
% 59.65/7.99  --qbf_mode                              false
% 59.65/7.99  --qbf_elim_univ                         false
% 59.65/7.99  --qbf_dom_inst                          none
% 59.65/7.99  --qbf_dom_pre_inst                      false
% 59.65/7.99  --qbf_sk_in                             false
% 59.65/7.99  --qbf_pred_elim                         true
% 59.65/7.99  --qbf_split                             512
% 59.65/7.99  
% 59.65/7.99  ------ BMC1 Options
% 59.65/7.99  
% 59.65/7.99  --bmc1_incremental                      false
% 59.65/7.99  --bmc1_axioms                           reachable_all
% 59.65/7.99  --bmc1_min_bound                        0
% 59.65/7.99  --bmc1_max_bound                        -1
% 59.65/7.99  --bmc1_max_bound_default                -1
% 59.65/7.99  --bmc1_symbol_reachability              true
% 59.65/7.99  --bmc1_property_lemmas                  false
% 59.65/7.99  --bmc1_k_induction                      false
% 59.65/7.99  --bmc1_non_equiv_states                 false
% 59.65/7.99  --bmc1_deadlock                         false
% 59.65/7.99  --bmc1_ucm                              false
% 59.65/7.99  --bmc1_add_unsat_core                   none
% 59.65/7.99  --bmc1_unsat_core_children              false
% 59.65/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.65/7.99  --bmc1_out_stat                         full
% 59.65/7.99  --bmc1_ground_init                      false
% 59.65/7.99  --bmc1_pre_inst_next_state              false
% 59.65/7.99  --bmc1_pre_inst_state                   false
% 59.65/7.99  --bmc1_pre_inst_reach_state             false
% 59.65/7.99  --bmc1_out_unsat_core                   false
% 59.65/7.99  --bmc1_aig_witness_out                  false
% 59.65/7.99  --bmc1_verbose                          false
% 59.65/7.99  --bmc1_dump_clauses_tptp                false
% 59.65/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.65/7.99  --bmc1_dump_file                        -
% 59.65/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.65/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.65/7.99  --bmc1_ucm_extend_mode                  1
% 59.65/7.99  --bmc1_ucm_init_mode                    2
% 59.65/7.99  --bmc1_ucm_cone_mode                    none
% 59.65/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.65/7.99  --bmc1_ucm_relax_model                  4
% 59.65/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.65/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.65/7.99  --bmc1_ucm_layered_model                none
% 59.65/7.99  --bmc1_ucm_max_lemma_size               10
% 59.65/7.99  
% 59.65/7.99  ------ AIG Options
% 59.65/7.99  
% 59.65/7.99  --aig_mode                              false
% 59.65/7.99  
% 59.65/7.99  ------ Instantiation Options
% 59.65/7.99  
% 59.65/7.99  --instantiation_flag                    true
% 59.65/7.99  --inst_sos_flag                         false
% 59.65/7.99  --inst_sos_phase                        true
% 59.65/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.65/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.65/7.99  --inst_lit_sel_side                     num_symb
% 59.65/7.99  --inst_solver_per_active                1400
% 59.65/7.99  --inst_solver_calls_frac                1.
% 59.65/7.99  --inst_passive_queue_type               priority_queues
% 59.65/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.65/7.99  --inst_passive_queues_freq              [25;2]
% 59.65/7.99  --inst_dismatching                      true
% 59.65/7.99  --inst_eager_unprocessed_to_passive     true
% 59.65/7.99  --inst_prop_sim_given                   true
% 59.65/7.99  --inst_prop_sim_new                     false
% 59.65/7.99  --inst_subs_new                         false
% 59.65/7.99  --inst_eq_res_simp                      false
% 59.65/7.99  --inst_subs_given                       false
% 59.65/7.99  --inst_orphan_elimination               true
% 59.65/7.99  --inst_learning_loop_flag               true
% 59.65/7.99  --inst_learning_start                   3000
% 59.65/7.99  --inst_learning_factor                  2
% 59.65/7.99  --inst_start_prop_sim_after_learn       3
% 59.65/7.99  --inst_sel_renew                        solver
% 59.65/7.99  --inst_lit_activity_flag                true
% 59.65/7.99  --inst_restr_to_given                   false
% 59.65/7.99  --inst_activity_threshold               500
% 59.65/7.99  --inst_out_proof                        true
% 59.65/7.99  
% 59.65/7.99  ------ Resolution Options
% 59.65/7.99  
% 59.65/7.99  --resolution_flag                       true
% 59.65/7.99  --res_lit_sel                           adaptive
% 59.65/7.99  --res_lit_sel_side                      none
% 59.65/7.99  --res_ordering                          kbo
% 59.65/7.99  --res_to_prop_solver                    active
% 59.65/7.99  --res_prop_simpl_new                    false
% 59.65/7.99  --res_prop_simpl_given                  true
% 59.65/7.99  --res_passive_queue_type                priority_queues
% 59.65/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.65/7.99  --res_passive_queues_freq               [15;5]
% 59.65/7.99  --res_forward_subs                      full
% 59.65/7.99  --res_backward_subs                     full
% 59.65/7.99  --res_forward_subs_resolution           true
% 59.65/7.99  --res_backward_subs_resolution          true
% 59.65/7.99  --res_orphan_elimination                true
% 59.65/7.99  --res_time_limit                        2.
% 59.65/7.99  --res_out_proof                         true
% 59.65/7.99  
% 59.65/7.99  ------ Superposition Options
% 59.65/7.99  
% 59.65/7.99  --superposition_flag                    true
% 59.65/7.99  --sup_passive_queue_type                priority_queues
% 59.65/7.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.65/7.99  --sup_passive_queues_freq               [1;4]
% 59.65/7.99  --demod_completeness_check              fast
% 59.65/7.99  --demod_use_ground                      true
% 59.65/7.99  --sup_to_prop_solver                    passive
% 59.65/7.99  --sup_prop_simpl_new                    true
% 59.65/7.99  --sup_prop_simpl_given                  true
% 59.65/7.99  --sup_fun_splitting                     false
% 59.65/7.99  --sup_smt_interval                      50000
% 59.65/7.99  
% 59.65/7.99  ------ Superposition Simplification Setup
% 59.65/7.99  
% 59.65/7.99  --sup_indices_passive                   []
% 59.65/7.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.65/7.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.65/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.65/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.65/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.65/7.99  --sup_full_bw                           [BwDemod]
% 59.65/7.99  --sup_immed_triv                        [TrivRules]
% 59.65/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.65/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.65/7.99  --sup_immed_bw_main                     []
% 59.65/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.65/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.65/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.65/7.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.65/7.99  
% 59.65/7.99  ------ Combination Options
% 59.65/7.99  
% 59.65/7.99  --comb_res_mult                         3
% 59.65/7.99  --comb_sup_mult                         2
% 59.65/7.99  --comb_inst_mult                        10
% 59.65/7.99  
% 59.65/7.99  ------ Debug Options
% 59.65/7.99  
% 59.65/7.99  --dbg_backtrace                         false
% 59.65/7.99  --dbg_dump_prop_clauses                 false
% 59.65/7.99  --dbg_dump_prop_clauses_file            -
% 59.65/7.99  --dbg_out_stat                          false
% 59.65/7.99  ------ Parsing...
% 59.65/7.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.65/7.99  
% 59.65/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 59.65/7.99  
% 59.65/7.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.65/7.99  
% 59.65/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.65/7.99  ------ Proving...
% 59.65/7.99  ------ Problem Properties 
% 59.65/7.99  
% 59.65/7.99  
% 59.65/7.99  clauses                                 15
% 59.65/7.99  conjectures                             4
% 59.65/7.99  EPR                                     5
% 59.65/7.99  Horn                                    15
% 59.65/7.99  unary                                   6
% 59.65/7.99  binary                                  3
% 59.65/7.99  lits                                    31
% 59.65/7.99  lits eq                                 7
% 59.65/7.99  fd_pure                                 0
% 59.65/7.99  fd_pseudo                               0
% 59.65/7.99  fd_cond                                 1
% 59.65/7.99  fd_pseudo_cond                          1
% 59.65/7.99  AC symbols                              0
% 59.65/7.99  
% 59.65/7.99  ------ Input Options Time Limit: Unbounded
% 59.65/7.99  
% 59.65/7.99  
% 59.65/7.99  ------ 
% 59.65/7.99  Current options:
% 59.65/7.99  ------ 
% 59.65/7.99  
% 59.65/7.99  ------ Input Options
% 59.65/7.99  
% 59.65/7.99  --out_options                           all
% 59.65/7.99  --tptp_safe_out                         true
% 59.65/7.99  --problem_path                          ""
% 59.65/7.99  --include_path                          ""
% 59.65/7.99  --clausifier                            res/vclausify_rel
% 59.65/7.99  --clausifier_options                    --mode clausify
% 59.65/7.99  --stdin                                 false
% 59.65/7.99  --stats_out                             sel
% 59.65/7.99  
% 59.65/7.99  ------ General Options
% 59.65/7.99  
% 59.65/7.99  --fof                                   false
% 59.65/7.99  --time_out_real                         604.99
% 59.65/7.99  --time_out_virtual                      -1.
% 59.65/7.99  --symbol_type_check                     false
% 59.65/7.99  --clausify_out                          false
% 59.65/7.99  --sig_cnt_out                           false
% 59.65/7.99  --trig_cnt_out                          false
% 59.65/7.99  --trig_cnt_out_tolerance                1.
% 59.65/7.99  --trig_cnt_out_sk_spl                   false
% 59.65/7.99  --abstr_cl_out                          false
% 59.65/7.99  
% 59.65/7.99  ------ Global Options
% 59.65/7.99  
% 59.65/7.99  --schedule                              none
% 59.65/7.99  --add_important_lit                     false
% 59.65/7.99  --prop_solver_per_cl                    1000
% 59.65/7.99  --min_unsat_core                        false
% 59.65/7.99  --soft_assumptions                      false
% 59.65/7.99  --soft_lemma_size                       3
% 59.65/7.99  --prop_impl_unit_size                   0
% 59.65/7.99  --prop_impl_unit                        []
% 59.65/7.99  --share_sel_clauses                     true
% 59.65/7.99  --reset_solvers                         false
% 59.65/7.99  --bc_imp_inh                            [conj_cone]
% 59.65/7.99  --conj_cone_tolerance                   3.
% 59.65/7.99  --extra_neg_conj                        none
% 59.65/7.99  --large_theory_mode                     true
% 59.65/7.99  --prolific_symb_bound                   200
% 59.65/7.99  --lt_threshold                          2000
% 59.65/7.99  --clause_weak_htbl                      true
% 59.65/7.99  --gc_record_bc_elim                     false
% 59.65/7.99  
% 59.65/7.99  ------ Preprocessing Options
% 59.65/7.99  
% 59.65/7.99  --preprocessing_flag                    true
% 59.65/7.99  --time_out_prep_mult                    0.1
% 59.65/7.99  --splitting_mode                        input
% 59.65/7.99  --splitting_grd                         true
% 59.65/7.99  --splitting_cvd                         false
% 59.65/7.99  --splitting_cvd_svl                     false
% 59.65/7.99  --splitting_nvd                         32
% 59.65/7.99  --sub_typing                            true
% 59.65/7.99  --prep_gs_sim                           false
% 59.65/7.99  --prep_unflatten                        true
% 59.65/7.99  --prep_res_sim                          true
% 59.65/7.99  --prep_upred                            true
% 59.65/7.99  --prep_sem_filter                       exhaustive
% 59.65/7.99  --prep_sem_filter_out                   false
% 59.65/7.99  --pred_elim                             false
% 59.65/7.99  --res_sim_input                         true
% 59.65/7.99  --eq_ax_congr_red                       true
% 59.65/7.99  --pure_diseq_elim                       true
% 59.65/7.99  --brand_transform                       false
% 59.65/7.99  --non_eq_to_eq                          false
% 59.65/7.99  --prep_def_merge                        true
% 59.65/7.99  --prep_def_merge_prop_impl              false
% 59.65/7.99  --prep_def_merge_mbd                    true
% 59.65/7.99  --prep_def_merge_tr_red                 false
% 59.65/7.99  --prep_def_merge_tr_cl                  false
% 59.65/7.99  --smt_preprocessing                     true
% 59.65/7.99  --smt_ac_axioms                         fast
% 59.65/7.99  --preprocessed_out                      false
% 59.65/7.99  --preprocessed_stats                    false
% 59.65/7.99  
% 59.65/7.99  ------ Abstraction refinement Options
% 59.65/7.99  
% 59.65/7.99  --abstr_ref                             []
% 59.65/7.99  --abstr_ref_prep                        false
% 59.65/7.99  --abstr_ref_until_sat                   false
% 59.65/7.99  --abstr_ref_sig_restrict                funpre
% 59.65/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.65/7.99  --abstr_ref_under                       []
% 59.65/7.99  
% 59.65/7.99  ------ SAT Options
% 59.65/7.99  
% 59.65/7.99  --sat_mode                              false
% 59.65/7.99  --sat_fm_restart_options                ""
% 59.65/7.99  --sat_gr_def                            false
% 59.65/7.99  --sat_epr_types                         true
% 59.65/7.99  --sat_non_cyclic_types                  false
% 59.65/7.99  --sat_finite_models                     false
% 59.65/7.99  --sat_fm_lemmas                         false
% 59.65/7.99  --sat_fm_prep                           false
% 59.65/7.99  --sat_fm_uc_incr                        true
% 59.65/7.99  --sat_out_model                         small
% 59.65/7.99  --sat_out_clauses                       false
% 59.65/7.99  
% 59.65/7.99  ------ QBF Options
% 59.65/7.99  
% 59.65/7.99  --qbf_mode                              false
% 59.65/7.99  --qbf_elim_univ                         false
% 59.65/7.99  --qbf_dom_inst                          none
% 59.65/7.99  --qbf_dom_pre_inst                      false
% 59.65/7.99  --qbf_sk_in                             false
% 59.65/7.99  --qbf_pred_elim                         true
% 59.65/7.99  --qbf_split                             512
% 59.65/7.99  
% 59.65/7.99  ------ BMC1 Options
% 59.65/7.99  
% 59.65/7.99  --bmc1_incremental                      false
% 59.65/7.99  --bmc1_axioms                           reachable_all
% 59.65/7.99  --bmc1_min_bound                        0
% 59.65/7.99  --bmc1_max_bound                        -1
% 59.65/7.99  --bmc1_max_bound_default                -1
% 59.65/7.99  --bmc1_symbol_reachability              true
% 59.65/7.99  --bmc1_property_lemmas                  false
% 59.65/7.99  --bmc1_k_induction                      false
% 59.65/7.99  --bmc1_non_equiv_states                 false
% 59.65/7.99  --bmc1_deadlock                         false
% 59.65/7.99  --bmc1_ucm                              false
% 59.65/7.99  --bmc1_add_unsat_core                   none
% 59.65/7.99  --bmc1_unsat_core_children              false
% 59.65/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.65/7.99  --bmc1_out_stat                         full
% 59.65/7.99  --bmc1_ground_init                      false
% 59.65/7.99  --bmc1_pre_inst_next_state              false
% 59.65/7.99  --bmc1_pre_inst_state                   false
% 59.65/7.99  --bmc1_pre_inst_reach_state             false
% 59.65/7.99  --bmc1_out_unsat_core                   false
% 59.65/7.99  --bmc1_aig_witness_out                  false
% 59.65/7.99  --bmc1_verbose                          false
% 59.65/7.99  --bmc1_dump_clauses_tptp                false
% 59.65/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.65/7.99  --bmc1_dump_file                        -
% 59.65/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.65/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.65/7.99  --bmc1_ucm_extend_mode                  1
% 59.65/7.99  --bmc1_ucm_init_mode                    2
% 59.65/7.99  --bmc1_ucm_cone_mode                    none
% 59.65/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.65/7.99  --bmc1_ucm_relax_model                  4
% 59.65/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.65/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.65/7.99  --bmc1_ucm_layered_model                none
% 59.65/7.99  --bmc1_ucm_max_lemma_size               10
% 59.65/7.99  
% 59.65/7.99  ------ AIG Options
% 59.65/7.99  
% 59.65/7.99  --aig_mode                              false
% 59.65/7.99  
% 59.65/7.99  ------ Instantiation Options
% 59.65/7.99  
% 59.65/7.99  --instantiation_flag                    true
% 59.65/7.99  --inst_sos_flag                         false
% 59.65/7.99  --inst_sos_phase                        true
% 59.65/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.65/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.65/7.99  --inst_lit_sel_side                     num_symb
% 59.65/7.99  --inst_solver_per_active                1400
% 59.65/7.99  --inst_solver_calls_frac                1.
% 59.65/7.99  --inst_passive_queue_type               priority_queues
% 59.65/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.65/7.99  --inst_passive_queues_freq              [25;2]
% 59.65/7.99  --inst_dismatching                      true
% 59.65/7.99  --inst_eager_unprocessed_to_passive     true
% 59.65/7.99  --inst_prop_sim_given                   true
% 59.65/7.99  --inst_prop_sim_new                     false
% 59.65/7.99  --inst_subs_new                         false
% 59.65/7.99  --inst_eq_res_simp                      false
% 59.65/7.99  --inst_subs_given                       false
% 59.65/7.99  --inst_orphan_elimination               true
% 59.65/7.99  --inst_learning_loop_flag               true
% 59.65/7.99  --inst_learning_start                   3000
% 59.65/7.99  --inst_learning_factor                  2
% 59.65/7.99  --inst_start_prop_sim_after_learn       3
% 59.65/7.99  --inst_sel_renew                        solver
% 59.65/7.99  --inst_lit_activity_flag                true
% 59.65/7.99  --inst_restr_to_given                   false
% 59.65/7.99  --inst_activity_threshold               500
% 59.65/7.99  --inst_out_proof                        true
% 59.65/7.99  
% 59.65/7.99  ------ Resolution Options
% 59.65/7.99  
% 59.65/7.99  --resolution_flag                       true
% 59.65/7.99  --res_lit_sel                           adaptive
% 59.65/7.99  --res_lit_sel_side                      none
% 59.65/7.99  --res_ordering                          kbo
% 59.65/7.99  --res_to_prop_solver                    active
% 59.65/7.99  --res_prop_simpl_new                    false
% 59.65/7.99  --res_prop_simpl_given                  true
% 59.65/7.99  --res_passive_queue_type                priority_queues
% 59.65/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.65/7.99  --res_passive_queues_freq               [15;5]
% 59.65/7.99  --res_forward_subs                      full
% 59.65/7.99  --res_backward_subs                     full
% 59.65/7.99  --res_forward_subs_resolution           true
% 59.65/7.99  --res_backward_subs_resolution          true
% 59.65/7.99  --res_orphan_elimination                true
% 59.65/7.99  --res_time_limit                        2.
% 59.65/7.99  --res_out_proof                         true
% 59.65/7.99  
% 59.65/7.99  ------ Superposition Options
% 59.65/7.99  
% 59.65/7.99  --superposition_flag                    true
% 59.65/7.99  --sup_passive_queue_type                priority_queues
% 59.65/7.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.65/7.99  --sup_passive_queues_freq               [1;4]
% 59.65/7.99  --demod_completeness_check              fast
% 59.65/7.99  --demod_use_ground                      true
% 59.65/7.99  --sup_to_prop_solver                    passive
% 59.65/7.99  --sup_prop_simpl_new                    true
% 59.65/7.99  --sup_prop_simpl_given                  true
% 59.65/7.99  --sup_fun_splitting                     false
% 59.65/7.99  --sup_smt_interval                      50000
% 59.65/7.99  
% 59.65/7.99  ------ Superposition Simplification Setup
% 59.65/7.99  
% 59.65/7.99  --sup_indices_passive                   []
% 59.65/7.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.65/7.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.65/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.65/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.65/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.65/7.99  --sup_full_bw                           [BwDemod]
% 59.65/7.99  --sup_immed_triv                        [TrivRules]
% 59.65/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.65/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.65/7.99  --sup_immed_bw_main                     []
% 59.65/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.65/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.65/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.65/7.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.65/7.99  
% 59.65/7.99  ------ Combination Options
% 59.65/7.99  
% 59.65/7.99  --comb_res_mult                         3
% 59.65/7.99  --comb_sup_mult                         2
% 59.65/7.99  --comb_inst_mult                        10
% 59.65/7.99  
% 59.65/7.99  ------ Debug Options
% 59.65/7.99  
% 59.65/7.99  --dbg_backtrace                         false
% 59.65/7.99  --dbg_dump_prop_clauses                 false
% 59.65/7.99  --dbg_dump_prop_clauses_file            -
% 59.65/7.99  --dbg_out_stat                          false
% 59.65/7.99  
% 59.65/7.99  
% 59.65/7.99  
% 59.65/7.99  
% 59.65/7.99  ------ Proving...
% 59.65/7.99  
% 59.65/7.99  
% 59.65/7.99  % SZS status Theorem for theBenchmark.p
% 59.65/7.99  
% 59.65/7.99  % SZS output start CNFRefutation for theBenchmark.p
% 59.65/7.99  
% 59.65/7.99  fof(f11,conjecture,(
% 59.65/7.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f12,negated_conjecture,(
% 59.65/7.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 59.65/7.99    inference(negated_conjecture,[],[f11])).
% 59.65/7.99  
% 59.65/7.99  fof(f24,plain,(
% 59.65/7.99    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 59.65/7.99    inference(ennf_transformation,[],[f12])).
% 59.65/7.99  
% 59.65/7.99  fof(f25,plain,(
% 59.65/7.99    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 59.65/7.99    inference(flattening,[],[f24])).
% 59.65/7.99  
% 59.65/7.99  fof(f29,plain,(
% 59.65/7.99    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 59.65/7.99    introduced(choice_axiom,[])).
% 59.65/7.99  
% 59.65/7.99  fof(f30,plain,(
% 59.65/7.99    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 59.65/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).
% 59.65/7.99  
% 59.65/7.99  fof(f46,plain,(
% 59.65/7.99    r1_tarski(sK0,k2_relat_1(sK1))),
% 59.65/7.99    inference(cnf_transformation,[],[f30])).
% 59.65/7.99  
% 59.65/7.99  fof(f4,axiom,(
% 59.65/7.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f37,plain,(
% 59.65/7.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f4])).
% 59.65/7.99  
% 59.65/7.99  fof(f5,axiom,(
% 59.65/7.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f38,plain,(
% 59.65/7.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f5])).
% 59.65/7.99  
% 59.65/7.99  fof(f50,plain,(
% 59.65/7.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 59.65/7.99    inference(definition_unfolding,[],[f37,f38])).
% 59.65/7.99  
% 59.65/7.99  fof(f3,axiom,(
% 59.65/7.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f13,plain,(
% 59.65/7.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 59.65/7.99    inference(ennf_transformation,[],[f3])).
% 59.65/7.99  
% 59.65/7.99  fof(f14,plain,(
% 59.65/7.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 59.65/7.99    inference(flattening,[],[f13])).
% 59.65/7.99  
% 59.65/7.99  fof(f36,plain,(
% 59.65/7.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f14])).
% 59.65/7.99  
% 59.65/7.99  fof(f2,axiom,(
% 59.65/7.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f28,plain,(
% 59.65/7.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 59.65/7.99    inference(nnf_transformation,[],[f2])).
% 59.65/7.99  
% 59.65/7.99  fof(f35,plain,(
% 59.65/7.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f28])).
% 59.65/7.99  
% 59.65/7.99  fof(f48,plain,(
% 59.65/7.99    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 59.65/7.99    inference(definition_unfolding,[],[f35,f38])).
% 59.65/7.99  
% 59.65/7.99  fof(f34,plain,(
% 59.65/7.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 59.65/7.99    inference(cnf_transformation,[],[f28])).
% 59.65/7.99  
% 59.65/7.99  fof(f49,plain,(
% 59.65/7.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 59.65/7.99    inference(definition_unfolding,[],[f34,f38])).
% 59.65/7.99  
% 59.65/7.99  fof(f44,plain,(
% 59.65/7.99    v1_relat_1(sK1)),
% 59.65/7.99    inference(cnf_transformation,[],[f30])).
% 59.65/7.99  
% 59.65/7.99  fof(f6,axiom,(
% 59.65/7.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f15,plain,(
% 59.65/7.99    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 59.65/7.99    inference(ennf_transformation,[],[f6])).
% 59.65/7.99  
% 59.65/7.99  fof(f39,plain,(
% 59.65/7.99    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f15])).
% 59.65/7.99  
% 59.65/7.99  fof(f10,axiom,(
% 59.65/7.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f22,plain,(
% 59.65/7.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 59.65/7.99    inference(ennf_transformation,[],[f10])).
% 59.65/7.99  
% 59.65/7.99  fof(f23,plain,(
% 59.65/7.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 59.65/7.99    inference(flattening,[],[f22])).
% 59.65/7.99  
% 59.65/7.99  fof(f43,plain,(
% 59.65/7.99    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f23])).
% 59.65/7.99  
% 59.65/7.99  fof(f45,plain,(
% 59.65/7.99    v1_funct_1(sK1)),
% 59.65/7.99    inference(cnf_transformation,[],[f30])).
% 59.65/7.99  
% 59.65/7.99  fof(f8,axiom,(
% 59.65/7.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f18,plain,(
% 59.65/7.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 59.65/7.99    inference(ennf_transformation,[],[f8])).
% 59.65/7.99  
% 59.65/7.99  fof(f19,plain,(
% 59.65/7.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 59.65/7.99    inference(flattening,[],[f18])).
% 59.65/7.99  
% 59.65/7.99  fof(f41,plain,(
% 59.65/7.99    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f19])).
% 59.65/7.99  
% 59.65/7.99  fof(f7,axiom,(
% 59.65/7.99    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f16,plain,(
% 59.65/7.99    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 59.65/7.99    inference(ennf_transformation,[],[f7])).
% 59.65/7.99  
% 59.65/7.99  fof(f17,plain,(
% 59.65/7.99    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 59.65/7.99    inference(flattening,[],[f16])).
% 59.65/7.99  
% 59.65/7.99  fof(f40,plain,(
% 59.65/7.99    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f17])).
% 59.65/7.99  
% 59.65/7.99  fof(f1,axiom,(
% 59.65/7.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f26,plain,(
% 59.65/7.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.65/7.99    inference(nnf_transformation,[],[f1])).
% 59.65/7.99  
% 59.65/7.99  fof(f27,plain,(
% 59.65/7.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.65/7.99    inference(flattening,[],[f26])).
% 59.65/7.99  
% 59.65/7.99  fof(f33,plain,(
% 59.65/7.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f27])).
% 59.65/7.99  
% 59.65/7.99  fof(f47,plain,(
% 59.65/7.99    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0),
% 59.65/7.99    inference(cnf_transformation,[],[f30])).
% 59.65/7.99  
% 59.65/7.99  fof(f9,axiom,(
% 59.65/7.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 59.65/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.65/7.99  
% 59.65/7.99  fof(f20,plain,(
% 59.65/7.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 59.65/7.99    inference(ennf_transformation,[],[f9])).
% 59.65/7.99  
% 59.65/7.99  fof(f21,plain,(
% 59.65/7.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 59.65/7.99    inference(flattening,[],[f20])).
% 59.65/7.99  
% 59.65/7.99  fof(f42,plain,(
% 59.65/7.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 59.65/7.99    inference(cnf_transformation,[],[f21])).
% 59.65/7.99  
% 59.65/7.99  cnf(c_13,negated_conjecture,
% 59.65/7.99      ( r1_tarski(sK0,k2_relat_1(sK1)) ),
% 59.65/7.99      inference(cnf_transformation,[],[f46]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_605,plain,
% 59.65/7.99      ( r1_tarski(sK0,k2_relat_1(sK1)) = iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_6,plain,
% 59.65/7.99      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 59.65/7.99      inference(cnf_transformation,[],[f50]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_611,plain,
% 59.65/7.99      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_5,plain,
% 59.65/7.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 59.65/7.99      inference(cnf_transformation,[],[f36]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_612,plain,
% 59.65/7.99      ( r1_tarski(X0,X1) != iProver_top
% 59.65/7.99      | r1_tarski(X1,X2) != iProver_top
% 59.65/7.99      | r1_tarski(X0,X2) = iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_1400,plain,
% 59.65/7.99      ( r1_tarski(X0,X1) != iProver_top
% 59.65/7.99      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_611,c_612]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_3,plain,
% 59.65/7.99      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 59.65/7.99      inference(cnf_transformation,[],[f48]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_614,plain,
% 59.65/7.99      ( k6_subset_1(X0,X1) = k1_xboole_0
% 59.65/7.99      | r1_tarski(X0,X1) != iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_2785,plain,
% 59.65/7.99      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 59.65/7.99      | r1_tarski(X0,X2) != iProver_top ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_1400,c_614]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_2974,plain,
% 59.65/7.99      ( k6_subset_1(k6_subset_1(sK0,X0),k2_relat_1(sK1)) = k1_xboole_0 ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_605,c_2785]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_4,plain,
% 59.65/7.99      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 59.65/7.99      inference(cnf_transformation,[],[f49]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_613,plain,
% 59.65/7.99      ( k6_subset_1(X0,X1) != k1_xboole_0
% 59.65/7.99      | r1_tarski(X0,X1) = iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_3199,plain,
% 59.65/7.99      ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1)) = iProver_top ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_2974,c_613]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_15,negated_conjecture,
% 59.65/7.99      ( v1_relat_1(sK1) ),
% 59.65/7.99      inference(cnf_transformation,[],[f44]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_603,plain,
% 59.65/7.99      ( v1_relat_1(sK1) = iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_7,plain,
% 59.65/7.99      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 59.65/7.99      inference(cnf_transformation,[],[f39]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_610,plain,
% 59.65/7.99      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 59.65/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_11,plain,
% 59.65/7.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 59.65/7.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 59.65/7.99      | ~ v1_relat_1(X1) ),
% 59.65/7.99      inference(cnf_transformation,[],[f43]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_606,plain,
% 59.65/7.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 59.65/7.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 59.65/7.99      | v1_relat_1(X1) != iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_1123,plain,
% 59.65/7.99      ( k6_subset_1(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = k1_xboole_0
% 59.65/7.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 59.65/7.99      | v1_relat_1(X1) != iProver_top ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_606,c_614]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_1597,plain,
% 59.65/7.99      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,k9_relat_1(X0,k10_relat_1(X0,X1)))) = k1_xboole_0
% 59.65/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_610,c_1123]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_8432,plain,
% 59.65/7.99      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k1_xboole_0 ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_603,c_1597]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_14,negated_conjecture,
% 59.65/7.99      ( v1_funct_1(sK1) ),
% 59.65/7.99      inference(cnf_transformation,[],[f45]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_604,plain,
% 59.65/7.99      ( v1_funct_1(sK1) = iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_9,plain,
% 59.65/7.99      ( ~ v1_funct_1(X0)
% 59.65/7.99      | ~ v1_relat_1(X0)
% 59.65/7.99      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 59.65/7.99      inference(cnf_transformation,[],[f41]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_608,plain,
% 59.65/7.99      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 59.65/7.99      | v1_funct_1(X0) != iProver_top
% 59.65/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_1587,plain,
% 59.65/7.99      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
% 59.65/7.99      | v1_relat_1(sK1) != iProver_top ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_604,c_608]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_16,plain,
% 59.65/7.99      ( v1_relat_1(sK1) = iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_6778,plain,
% 59.65/7.99      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 59.65/7.99      inference(global_propositional_subsumption,
% 59.65/7.99                [status(thm)],
% 59.65/7.99                [c_1587,c_16]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_8448,plain,
% 59.65/7.99      ( k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k1_xboole_0 ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_8432,c_6778]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_8,plain,
% 59.65/7.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 59.65/7.99      | ~ v1_relat_1(X1)
% 59.65/7.99      | k10_relat_1(X1,X0) != k1_xboole_0
% 59.65/7.99      | k1_xboole_0 = X0 ),
% 59.65/7.99      inference(cnf_transformation,[],[f40]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_609,plain,
% 59.65/7.99      ( k10_relat_1(X0,X1) != k1_xboole_0
% 59.65/7.99      | k1_xboole_0 = X1
% 59.65/7.99      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 59.65/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.65/7.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_233070,plain,
% 59.65/7.99      ( k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0
% 59.65/7.99      | r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top
% 59.65/7.99      | v1_relat_1(sK1) != iProver_top ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_8448,c_609]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_234320,plain,
% 59.65/7.99      ( r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top
% 59.65/7.99      | k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0 ),
% 59.65/7.99      inference(global_propositional_subsumption,
% 59.65/7.99                [status(thm)],
% 59.65/7.99                [c_233070,c_16]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_234321,plain,
% 59.65/7.99      ( k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k1_xboole_0
% 59.65/7.99      | r1_tarski(k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k2_relat_1(sK1)) != iProver_top ),
% 59.65/7.99      inference(renaming,[status(thm)],[c_234320]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_234330,plain,
% 59.65/7.99      ( k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) = k1_xboole_0 ),
% 59.65/7.99      inference(superposition,[status(thm)],[c_3199,c_234321]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_0,plain,
% 59.65/7.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 59.65/7.99      inference(cnf_transformation,[],[f33]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_12,negated_conjecture,
% 59.65/7.99      ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
% 59.65/7.99      inference(cnf_transformation,[],[f47]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_1167,plain,
% 59.65/7.99      ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
% 59.65/7.99      | ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
% 59.65/7.99      inference(resolution,[status(thm)],[c_0,c_12]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_10,plain,
% 59.65/7.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 59.65/7.99      | ~ v1_funct_1(X0)
% 59.65/7.99      | ~ v1_relat_1(X0) ),
% 59.65/7.99      inference(cnf_transformation,[],[f42]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_1332,plain,
% 59.65/7.99      ( ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
% 59.65/7.99      | ~ v1_funct_1(sK1)
% 59.65/7.99      | ~ v1_relat_1(sK1) ),
% 59.65/7.99      inference(resolution,[status(thm)],[c_1167,c_10]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(c_809,plain,
% 59.65/7.99      ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
% 59.65/7.99      | k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) != k1_xboole_0 ),
% 59.65/7.99      inference(instantiation,[status(thm)],[c_4]) ).
% 59.65/7.99  
% 59.65/7.99  cnf(contradiction,plain,
% 59.65/7.99      ( $false ),
% 59.65/7.99      inference(minisat,[status(thm)],[c_234330,c_1332,c_809,c_14,c_15]) ).
% 59.65/7.99  
% 59.65/7.99  
% 59.65/7.99  % SZS output end CNFRefutation for theBenchmark.p
% 59.65/7.99  
% 59.65/7.99  ------                               Statistics
% 59.65/7.99  
% 59.65/7.99  ------ Selected
% 59.65/7.99  
% 59.65/7.99  total_time:                             7.473
% 59.65/7.99  
%------------------------------------------------------------------------------
