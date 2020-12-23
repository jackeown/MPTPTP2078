%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:08 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 652 expanded)
%              Number of clauses        :   60 ( 200 expanded)
%              Number of leaves         :   12 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          :  238 (2251 expanded)
%              Number of equality atoms :   91 ( 404 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f37,f36,f36])).

fof(f42,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f36,f36])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f45,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_491,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_497,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_502,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1050,plain,
    ( k2_xboole_0(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = X1
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_502])).

cnf(c_3420,plain,
    ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_491,c_1050])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3857,plain,
    ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3420,c_18,c_21])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_504,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_503,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2058,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_504,c_503])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_500,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2351,plain,
    ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_2058,c_500])).

cnf(c_3863,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_3857,c_2351])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_499,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2339,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_491,c_499])).

cnf(c_2687,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2339,c_18,c_21])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_493,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1246,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_493,c_500])).

cnf(c_2702,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_2687,c_1246])).

cnf(c_2726,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,sK0))) ),
    inference(superposition,[status(thm)],[c_2702,c_2687])).

cnf(c_2728,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,sK0))) ),
    inference(demodulation,[status(thm)],[c_2726,c_2687])).

cnf(c_10711,plain,
    ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,sK0)))),k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_2728,c_3857])).

cnf(c_16941,plain,
    ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),sK0)))),k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))))) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),k1_setfam_1(k2_tarski(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_3863,c_10711])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_494,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_498,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1858,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_500])).

cnf(c_7008,plain,
    ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_1858])).

cnf(c_656,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1143,plain,
    ( ~ r1_tarski(sK0,X0)
    | k1_setfam_1(k2_tarski(sK0,X0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1459,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0 ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_7843,plain,
    ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7008,c_16,c_13,c_656,c_1459])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6803,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_3863,c_0])).

cnf(c_7858,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_7843,c_6803])).

cnf(c_16990,plain,
    ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK0)))),sK0) = k1_setfam_1(k2_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1)))) ),
    inference(light_normalisation,[status(thm)],[c_16941,c_2702,c_7858])).

cnf(c_1048,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_504,c_502])).

cnf(c_1242,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_504,c_500])).

cnf(c_6,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_501,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1243,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_501,c_500])).

cnf(c_5638,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1243,c_0])).

cnf(c_16991,plain,
    ( k1_setfam_1(k2_tarski(sK0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_16990,c_1048,c_1242,c_5638,c_7858])).

cnf(c_909,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_501])).

cnf(c_17711,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_16991,c_909])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17711,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:37:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.09/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/0.99  
% 4.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.09/0.99  
% 4.09/0.99  ------  iProver source info
% 4.09/0.99  
% 4.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.09/0.99  git: non_committed_changes: false
% 4.09/0.99  git: last_make_outside_of_git: false
% 4.09/0.99  
% 4.09/0.99  ------ 
% 4.09/0.99  ------ Parsing...
% 4.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.09/0.99  
% 4.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.09/0.99  
% 4.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.09/0.99  
% 4.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.09/0.99  ------ Proving...
% 4.09/0.99  ------ Problem Properties 
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  clauses                                 16
% 4.09/0.99  conjectures                             6
% 4.09/0.99  EPR                                     6
% 4.09/0.99  Horn                                    16
% 4.09/0.99  unary                                   9
% 4.09/0.99  binary                                  3
% 4.09/0.99  lits                                    29
% 4.09/0.99  lits eq                                 5
% 4.09/0.99  fd_pure                                 0
% 4.09/0.99  fd_pseudo                               0
% 4.09/0.99  fd_cond                                 0
% 4.09/0.99  fd_pseudo_cond                          1
% 4.09/0.99  AC symbols                              0
% 4.09/0.99  
% 4.09/0.99  ------ Input Options Time Limit: Unbounded
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  ------ 
% 4.09/0.99  Current options:
% 4.09/0.99  ------ 
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  ------ Proving...
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  % SZS status Theorem for theBenchmark.p
% 4.09/0.99  
% 4.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.09/0.99  
% 4.09/0.99  fof(f11,conjecture,(
% 4.09/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f12,negated_conjecture,(
% 4.09/0.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.09/0.99    inference(negated_conjecture,[],[f11])).
% 4.09/0.99  
% 4.09/0.99  fof(f22,plain,(
% 4.09/0.99    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.09/0.99    inference(ennf_transformation,[],[f12])).
% 4.09/0.99  
% 4.09/0.99  fof(f23,plain,(
% 4.09/0.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.09/0.99    inference(flattening,[],[f22])).
% 4.09/0.99  
% 4.09/0.99  fof(f26,plain,(
% 4.09/0.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 4.09/0.99    introduced(choice_axiom,[])).
% 4.09/0.99  
% 4.09/0.99  fof(f27,plain,(
% 4.09/0.99    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 4.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).
% 4.09/0.99  
% 4.09/0.99  fof(f40,plain,(
% 4.09/0.99    v1_relat_1(sK2)),
% 4.09/0.99    inference(cnf_transformation,[],[f27])).
% 4.09/0.99  
% 4.09/0.99  fof(f10,axiom,(
% 4.09/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f20,plain,(
% 4.09/0.99    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.09/0.99    inference(ennf_transformation,[],[f10])).
% 4.09/0.99  
% 4.09/0.99  fof(f21,plain,(
% 4.09/0.99    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.09/0.99    inference(flattening,[],[f20])).
% 4.09/0.99  
% 4.09/0.99  fof(f39,plain,(
% 4.09/0.99    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f21])).
% 4.09/0.99  
% 4.09/0.99  fof(f4,axiom,(
% 4.09/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f14,plain,(
% 4.09/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.09/0.99    inference(ennf_transformation,[],[f4])).
% 4.09/0.99  
% 4.09/0.99  fof(f33,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f14])).
% 4.09/0.99  
% 4.09/0.99  fof(f41,plain,(
% 4.09/0.99    v1_funct_1(sK2)),
% 4.09/0.99    inference(cnf_transformation,[],[f27])).
% 4.09/0.99  
% 4.09/0.99  fof(f44,plain,(
% 4.09/0.99    v2_funct_1(sK2)),
% 4.09/0.99    inference(cnf_transformation,[],[f27])).
% 4.09/0.99  
% 4.09/0.99  fof(f2,axiom,(
% 4.09/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f24,plain,(
% 4.09/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.09/0.99    inference(nnf_transformation,[],[f2])).
% 4.09/0.99  
% 4.09/0.99  fof(f25,plain,(
% 4.09/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.09/0.99    inference(flattening,[],[f24])).
% 4.09/0.99  
% 4.09/0.99  fof(f29,plain,(
% 4.09/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.09/0.99    inference(cnf_transformation,[],[f25])).
% 4.09/0.99  
% 4.09/0.99  fof(f51,plain,(
% 4.09/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.09/0.99    inference(equality_resolution,[],[f29])).
% 4.09/0.99  
% 4.09/0.99  fof(f3,axiom,(
% 4.09/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f13,plain,(
% 4.09/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.09/0.99    inference(ennf_transformation,[],[f3])).
% 4.09/0.99  
% 4.09/0.99  fof(f32,plain,(
% 4.09/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f13])).
% 4.09/0.99  
% 4.09/0.99  fof(f6,axiom,(
% 4.09/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f15,plain,(
% 4.09/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.09/0.99    inference(ennf_transformation,[],[f6])).
% 4.09/0.99  
% 4.09/0.99  fof(f35,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f15])).
% 4.09/0.99  
% 4.09/0.99  fof(f7,axiom,(
% 4.09/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f36,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.09/0.99    inference(cnf_transformation,[],[f7])).
% 4.09/0.99  
% 4.09/0.99  fof(f48,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 4.09/0.99    inference(definition_unfolding,[],[f35,f36])).
% 4.09/0.99  
% 4.09/0.99  fof(f8,axiom,(
% 4.09/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f16,plain,(
% 4.09/0.99    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.09/0.99    inference(ennf_transformation,[],[f8])).
% 4.09/0.99  
% 4.09/0.99  fof(f17,plain,(
% 4.09/0.99    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.09/0.99    inference(flattening,[],[f16])).
% 4.09/0.99  
% 4.09/0.99  fof(f37,plain,(
% 4.09/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f17])).
% 4.09/0.99  
% 4.09/0.99  fof(f49,plain,(
% 4.09/0.99    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.09/0.99    inference(definition_unfolding,[],[f37,f36,f36])).
% 4.09/0.99  
% 4.09/0.99  fof(f42,plain,(
% 4.09/0.99    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 4.09/0.99    inference(cnf_transformation,[],[f27])).
% 4.09/0.99  
% 4.09/0.99  fof(f43,plain,(
% 4.09/0.99    r1_tarski(sK0,k1_relat_1(sK2))),
% 4.09/0.99    inference(cnf_transformation,[],[f27])).
% 4.09/0.99  
% 4.09/0.99  fof(f9,axiom,(
% 4.09/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f18,plain,(
% 4.09/0.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.09/0.99    inference(ennf_transformation,[],[f9])).
% 4.09/0.99  
% 4.09/0.99  fof(f19,plain,(
% 4.09/0.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.09/0.99    inference(flattening,[],[f18])).
% 4.09/0.99  
% 4.09/0.99  fof(f38,plain,(
% 4.09/0.99    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f19])).
% 4.09/0.99  
% 4.09/0.99  fof(f1,axiom,(
% 4.09/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f28,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f1])).
% 4.09/0.99  
% 4.09/0.99  fof(f46,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 4.09/0.99    inference(definition_unfolding,[],[f28,f36,f36])).
% 4.09/0.99  
% 4.09/0.99  fof(f5,axiom,(
% 4.09/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f34,plain,(
% 4.09/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f5])).
% 4.09/0.99  
% 4.09/0.99  fof(f47,plain,(
% 4.09/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 4.09/0.99    inference(definition_unfolding,[],[f34,f36])).
% 4.09/0.99  
% 4.09/0.99  fof(f45,plain,(
% 4.09/0.99    ~r1_tarski(sK0,sK1)),
% 4.09/0.99    inference(cnf_transformation,[],[f27])).
% 4.09/0.99  
% 4.09/0.99  cnf(c_16,negated_conjecture,
% 4.09/0.99      ( v1_relat_1(sK2) ),
% 4.09/0.99      inference(cnf_transformation,[],[f40]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_491,plain,
% 4.09/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_10,plain,
% 4.09/0.99      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 4.09/0.99      | ~ v1_relat_1(X0)
% 4.09/0.99      | ~ v1_funct_1(X0)
% 4.09/0.99      | ~ v2_funct_1(X0) ),
% 4.09/0.99      inference(cnf_transformation,[],[f39]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_497,plain,
% 4.09/0.99      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
% 4.09/0.99      | v1_relat_1(X0) != iProver_top
% 4.09/0.99      | v1_funct_1(X0) != iProver_top
% 4.09/0.99      | v2_funct_1(X0) != iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_5,plain,
% 4.09/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 4.09/0.99      inference(cnf_transformation,[],[f33]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_502,plain,
% 4.09/0.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_1050,plain,
% 4.09/0.99      ( k2_xboole_0(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = X1
% 4.09/0.99      | v1_relat_1(X0) != iProver_top
% 4.09/0.99      | v1_funct_1(X0) != iProver_top
% 4.09/0.99      | v2_funct_1(X0) != iProver_top ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_497,c_502]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_3420,plain,
% 4.09/0.99      ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0
% 4.09/0.99      | v1_funct_1(sK2) != iProver_top
% 4.09/0.99      | v2_funct_1(sK2) != iProver_top ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_491,c_1050]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_15,negated_conjecture,
% 4.09/0.99      ( v1_funct_1(sK2) ),
% 4.09/0.99      inference(cnf_transformation,[],[f41]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_18,plain,
% 4.09/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_12,negated_conjecture,
% 4.09/0.99      ( v2_funct_1(sK2) ),
% 4.09/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_21,plain,
% 4.09/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_3857,plain,
% 4.09/0.99      ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0 ),
% 4.09/0.99      inference(global_propositional_subsumption,
% 4.09/0.99                [status(thm)],
% 4.09/0.99                [c_3420,c_18,c_21]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_3,plain,
% 4.09/0.99      ( r1_tarski(X0,X0) ),
% 4.09/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_504,plain,
% 4.09/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_4,plain,
% 4.09/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 4.09/0.99      inference(cnf_transformation,[],[f32]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_503,plain,
% 4.09/0.99      ( r1_tarski(X0,X1) = iProver_top
% 4.09/0.99      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2058,plain,
% 4.09/0.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_504,c_503]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_7,plain,
% 4.09/0.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 4.09/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_500,plain,
% 4.09/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 4.09/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2351,plain,
% 4.09/0.99      ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0 ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_2058,c_500]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_3863,plain,
% 4.09/0.99      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_3857,c_2351]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_8,plain,
% 4.09/0.99      ( ~ v1_relat_1(X0)
% 4.09/0.99      | ~ v1_funct_1(X0)
% 4.09/0.99      | ~ v2_funct_1(X0)
% 4.09/0.99      | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 4.09/0.99      inference(cnf_transformation,[],[f49]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_499,plain,
% 4.09/0.99      ( k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 4.09/0.99      | v1_relat_1(X0) != iProver_top
% 4.09/0.99      | v1_funct_1(X0) != iProver_top
% 4.09/0.99      | v2_funct_1(X0) != iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2339,plain,
% 4.09/0.99      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
% 4.09/0.99      | v1_funct_1(sK2) != iProver_top
% 4.09/0.99      | v2_funct_1(sK2) != iProver_top ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_491,c_499]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2687,plain,
% 4.09/0.99      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 4.09/0.99      inference(global_propositional_subsumption,
% 4.09/0.99                [status(thm)],
% 4.09/0.99                [c_2339,c_18,c_21]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_14,negated_conjecture,
% 4.09/0.99      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 4.09/0.99      inference(cnf_transformation,[],[f42]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_493,plain,
% 4.09/0.99      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_1246,plain,
% 4.09/0.99      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_493,c_500]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2702,plain,
% 4.09/0.99      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) = k9_relat_1(sK2,sK0) ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_2687,c_1246]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2726,plain,
% 4.09/0.99      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,sK0))) ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_2702,c_2687]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2728,plain,
% 4.09/0.99      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,sK0))) ),
% 4.09/0.99      inference(demodulation,[status(thm)],[c_2726,c_2687]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_10711,plain,
% 4.09/0.99      ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,sK0)))),k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1)))) ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_2728,c_3857]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_16941,plain,
% 4.09/0.99      ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),sK0)))),k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))))) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),k1_setfam_1(k2_tarski(sK0,sK1)))) ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_3863,c_10711]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_13,negated_conjecture,
% 4.09/0.99      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 4.09/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_494,plain,
% 4.09/0.99      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_9,plain,
% 4.09/0.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 4.09/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 4.09/0.99      | ~ v1_relat_1(X1) ),
% 4.09/0.99      inference(cnf_transformation,[],[f38]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_498,plain,
% 4.09/0.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 4.09/0.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 4.09/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.09/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_1858,plain,
% 4.09/0.99      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0
% 4.09/0.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 4.09/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.09/0.99      inference(superposition,[status(thm)],[c_498,c_500]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_7008,plain,
% 4.09/1.00      ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0
% 4.09/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_494,c_1858]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_656,plain,
% 4.09/1.00      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
% 4.09/1.00      | ~ r1_tarski(sK0,k1_relat_1(sK2))
% 4.09/1.00      | ~ v1_relat_1(sK2) ),
% 4.09/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_1143,plain,
% 4.09/1.00      ( ~ r1_tarski(sK0,X0) | k1_setfam_1(k2_tarski(sK0,X0)) = sK0 ),
% 4.09/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_1459,plain,
% 4.09/1.00      ( ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
% 4.09/1.00      | k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0 ),
% 4.09/1.00      inference(instantiation,[status(thm)],[c_1143]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_7843,plain,
% 4.09/1.00      ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0 ),
% 4.09/1.00      inference(global_propositional_subsumption,
% 4.09/1.00                [status(thm)],
% 4.09/1.00                [c_7008,c_16,c_13,c_656,c_1459]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_0,plain,
% 4.09/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 4.09/1.00      inference(cnf_transformation,[],[f46]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_6803,plain,
% 4.09/1.00      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_3863,c_0]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_7858,plain,
% 4.09/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_7843,c_6803]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_16990,plain,
% 4.09/1.00      ( k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK0)))),sK0) = k1_setfam_1(k2_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1)))) ),
% 4.09/1.00      inference(light_normalisation,
% 4.09/1.00                [status(thm)],
% 4.09/1.00                [c_16941,c_2702,c_7858]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_1048,plain,
% 4.09/1.00      ( k2_xboole_0(X0,X0) = X0 ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_504,c_502]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_1242,plain,
% 4.09/1.00      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_504,c_500]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_6,plain,
% 4.09/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 4.09/1.00      inference(cnf_transformation,[],[f47]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_501,plain,
% 4.09/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 4.09/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_1243,plain,
% 4.09/1.00      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_501,c_500]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_5638,plain,
% 4.09/1.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_1243,c_0]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_16991,plain,
% 4.09/1.00      ( k1_setfam_1(k2_tarski(sK0,sK1)) = sK0 ),
% 4.09/1.00      inference(demodulation,
% 4.09/1.00                [status(thm)],
% 4.09/1.00                [c_16990,c_1048,c_1242,c_5638,c_7858]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_909,plain,
% 4.09/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_0,c_501]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_17711,plain,
% 4.09/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 4.09/1.00      inference(superposition,[status(thm)],[c_16991,c_909]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_11,negated_conjecture,
% 4.09/1.00      ( ~ r1_tarski(sK0,sK1) ),
% 4.09/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(c_22,plain,
% 4.09/1.00      ( r1_tarski(sK0,sK1) != iProver_top ),
% 4.09/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.09/1.00  
% 4.09/1.00  cnf(contradiction,plain,
% 4.09/1.00      ( $false ),
% 4.09/1.00      inference(minisat,[status(thm)],[c_17711,c_22]) ).
% 4.09/1.00  
% 4.09/1.00  
% 4.09/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.09/1.00  
% 4.09/1.00  ------                               Statistics
% 4.09/1.00  
% 4.09/1.00  ------ Selected
% 4.09/1.00  
% 4.09/1.00  total_time:                             0.468
% 4.09/1.00  
%------------------------------------------------------------------------------
