%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:10 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 274 expanded)
%              Number of clauses        :   68 (  95 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  318 (1068 expanded)
%              Number of equality atoms :  117 ( 169 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,
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

fof(f32,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f54,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_355,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1028,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(X3))
    | X2 != X0
    | k1_relat_1(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_1152,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | r1_tarski(X2,k1_relat_1(X3))
    | X2 != X0
    | k1_relat_1(X3) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1459,plain,
    ( r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | X0 != sK0
    | k1_relat_1(X1) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_2681,plain,
    ( r1_tarski(k2_xboole_0(k6_subset_1(sK0,X0),sK0),k1_relat_1(X1))
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | k2_xboole_0(k6_subset_1(sK0,X0),sK0) != sK0
    | k1_relat_1(X1) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_18598,plain,
    ( r1_tarski(k2_xboole_0(k6_subset_1(sK0,sK1),sK0),k1_relat_1(X0))
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | k2_xboole_0(k6_subset_1(sK0,sK1),sK0) != sK0
    | k1_relat_1(X0) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2681])).

cnf(c_18600,plain,
    ( r1_tarski(k2_xboole_0(k6_subset_1(sK0,sK1),sK0),k1_relat_1(sK2))
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | k2_xboole_0(k6_subset_1(sK0,sK1),sK0) != sK0
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18598])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_796,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_800,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3397,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_800])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3833,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3397,c_21,c_22])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_794,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_809,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2048,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_794,c_809])).

cnf(c_3846,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3833,c_2048])).

cnf(c_13,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_799,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_811,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2452,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_799,c_811])).

cnf(c_15818,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k6_subset_1(sK0,sK1))) = k6_subset_1(sK0,sK1)
    | r1_tarski(k10_relat_1(sK2,k1_xboole_0),k6_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3846,c_2452])).

cnf(c_793,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_801,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_803,plain,
    ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2289,plain,
    ( k9_relat_1(k2_funct_1(X0),k1_xboole_0) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_803])).

cnf(c_12766,plain,
    ( k9_relat_1(k2_funct_1(sK2),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_2289])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_798,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1202,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_798])).

cnf(c_1822,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1202,c_21,c_22])).

cnf(c_12769,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12766,c_1822])).

cnf(c_14304,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12769,c_21])).

cnf(c_15983,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15818,c_3846,c_14304])).

cnf(c_16044,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | ~ r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15983])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_985,plain,
    ( r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k2_xboole_0(X0,X2),k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3097,plain,
    ( ~ r1_tarski(k2_xboole_0(k6_subset_1(sK0,X0),sK0),k1_relat_1(X1))
    | r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_11046,plain,
    ( ~ r1_tarski(k2_xboole_0(k6_subset_1(sK0,sK1),sK0),k1_relat_1(X0))
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3097])).

cnf(c_11052,plain,
    ( ~ r1_tarski(k2_xboole_0(k6_subset_1(sK0,sK1),sK0),k1_relat_1(sK2))
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_11046])).

cnf(c_8,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1257,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6434,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1479,plain,
    ( ~ r1_tarski(X0,sK0)
    | k2_xboole_0(X0,sK0) = sK0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1727,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,X0),sK0)
    | k2_xboole_0(k6_subset_1(sK0,X0),sK0) = sK0 ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_4405,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),sK0)
    | k2_xboole_0(k6_subset_1(sK0,sK1),sK0) = sK0 ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1163,plain,
    ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_962,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_362,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_370,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_68,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_64,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18600,c_16044,c_11052,c_6434,c_4405,c_1163,c_962,c_370,c_68,c_64,c_15,c_17,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.06/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.03  
% 4.06/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.06/1.03  
% 4.06/1.03  ------  iProver source info
% 4.06/1.03  
% 4.06/1.03  git: date: 2020-06-30 10:37:57 +0100
% 4.06/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.06/1.03  git: non_committed_changes: false
% 4.06/1.03  git: last_make_outside_of_git: false
% 4.06/1.03  
% 4.06/1.03  ------ 
% 4.06/1.03  ------ Parsing...
% 4.06/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.06/1.03  
% 4.06/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.06/1.03  
% 4.06/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.06/1.03  
% 4.06/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.06/1.03  ------ Proving...
% 4.06/1.03  ------ Problem Properties 
% 4.06/1.03  
% 4.06/1.03  
% 4.06/1.03  clauses                                 20
% 4.06/1.03  conjectures                             6
% 4.06/1.03  EPR                                     7
% 4.06/1.03  Horn                                    20
% 4.06/1.03  unary                                   9
% 4.06/1.03  binary                                  5
% 4.06/1.03  lits                                    39
% 4.06/1.03  lits eq                                 7
% 4.06/1.03  fd_pure                                 0
% 4.06/1.03  fd_pseudo                               0
% 4.06/1.03  fd_cond                                 0
% 4.06/1.03  fd_pseudo_cond                          1
% 4.06/1.03  AC symbols                              0
% 4.06/1.03  
% 4.06/1.03  ------ Input Options Time Limit: Unbounded
% 4.06/1.03  
% 4.06/1.03  
% 4.06/1.03  ------ 
% 4.06/1.03  Current options:
% 4.06/1.03  ------ 
% 4.06/1.03  
% 4.06/1.03  
% 4.06/1.03  
% 4.06/1.03  
% 4.06/1.03  ------ Proving...
% 4.06/1.03  
% 4.06/1.03  
% 4.06/1.03  % SZS status Theorem for theBenchmark.p
% 4.06/1.03  
% 4.06/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 4.06/1.03  
% 4.06/1.03  fof(f13,conjecture,(
% 4.06/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f14,negated_conjecture,(
% 4.06/1.03    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.06/1.03    inference(negated_conjecture,[],[f13])).
% 4.06/1.03  
% 4.06/1.03  fof(f26,plain,(
% 4.06/1.03    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.06/1.03    inference(ennf_transformation,[],[f14])).
% 4.06/1.03  
% 4.06/1.03  fof(f27,plain,(
% 4.06/1.03    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.06/1.03    inference(flattening,[],[f26])).
% 4.06/1.03  
% 4.06/1.03  fof(f31,plain,(
% 4.06/1.03    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 4.06/1.03    introduced(choice_axiom,[])).
% 4.06/1.03  
% 4.06/1.03  fof(f32,plain,(
% 4.06/1.03    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 4.06/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).
% 4.06/1.03  
% 4.06/1.03  fof(f53,plain,(
% 4.06/1.03    v2_funct_1(sK2)),
% 4.06/1.03    inference(cnf_transformation,[],[f32])).
% 4.06/1.03  
% 4.06/1.03  fof(f10,axiom,(
% 4.06/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f20,plain,(
% 4.06/1.03    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.06/1.03    inference(ennf_transformation,[],[f10])).
% 4.06/1.03  
% 4.06/1.03  fof(f21,plain,(
% 4.06/1.03    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.06/1.03    inference(flattening,[],[f20])).
% 4.06/1.03  
% 4.06/1.03  fof(f46,plain,(
% 4.06/1.03    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f21])).
% 4.06/1.03  
% 4.06/1.03  fof(f49,plain,(
% 4.06/1.03    v1_relat_1(sK2)),
% 4.06/1.03    inference(cnf_transformation,[],[f32])).
% 4.06/1.03  
% 4.06/1.03  fof(f50,plain,(
% 4.06/1.03    v1_funct_1(sK2)),
% 4.06/1.03    inference(cnf_transformation,[],[f32])).
% 4.06/1.03  
% 4.06/1.03  fof(f51,plain,(
% 4.06/1.03    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 4.06/1.03    inference(cnf_transformation,[],[f32])).
% 4.06/1.03  
% 4.06/1.03  fof(f2,axiom,(
% 4.06/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f30,plain,(
% 4.06/1.03    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.06/1.03    inference(nnf_transformation,[],[f2])).
% 4.06/1.03  
% 4.06/1.03  fof(f37,plain,(
% 4.06/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f30])).
% 4.06/1.03  
% 4.06/1.03  fof(f7,axiom,(
% 4.06/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f42,plain,(
% 4.06/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f7])).
% 4.06/1.03  
% 4.06/1.03  fof(f55,plain,(
% 4.06/1.03    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.06/1.03    inference(definition_unfolding,[],[f37,f42])).
% 4.06/1.03  
% 4.06/1.03  fof(f11,axiom,(
% 4.06/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f22,plain,(
% 4.06/1.03    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.06/1.03    inference(ennf_transformation,[],[f11])).
% 4.06/1.03  
% 4.06/1.03  fof(f23,plain,(
% 4.06/1.03    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.06/1.03    inference(flattening,[],[f22])).
% 4.06/1.03  
% 4.06/1.03  fof(f47,plain,(
% 4.06/1.03    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f23])).
% 4.06/1.03  
% 4.06/1.03  fof(f1,axiom,(
% 4.06/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f28,plain,(
% 4.06/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.06/1.03    inference(nnf_transformation,[],[f1])).
% 4.06/1.03  
% 4.06/1.03  fof(f29,plain,(
% 4.06/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.06/1.03    inference(flattening,[],[f28])).
% 4.06/1.03  
% 4.06/1.03  fof(f35,plain,(
% 4.06/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f29])).
% 4.06/1.03  
% 4.06/1.03  fof(f9,axiom,(
% 4.06/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f18,plain,(
% 4.06/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.06/1.03    inference(ennf_transformation,[],[f9])).
% 4.06/1.03  
% 4.06/1.03  fof(f19,plain,(
% 4.06/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.06/1.03    inference(flattening,[],[f18])).
% 4.06/1.03  
% 4.06/1.03  fof(f44,plain,(
% 4.06/1.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f19])).
% 4.06/1.03  
% 4.06/1.03  fof(f8,axiom,(
% 4.06/1.03    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f17,plain,(
% 4.06/1.03    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 4.06/1.03    inference(ennf_transformation,[],[f8])).
% 4.06/1.03  
% 4.06/1.03  fof(f43,plain,(
% 4.06/1.03    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f17])).
% 4.06/1.03  
% 4.06/1.03  fof(f12,axiom,(
% 4.06/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f24,plain,(
% 4.06/1.03    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.06/1.03    inference(ennf_transformation,[],[f12])).
% 4.06/1.03  
% 4.06/1.03  fof(f25,plain,(
% 4.06/1.03    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.06/1.03    inference(flattening,[],[f24])).
% 4.06/1.03  
% 4.06/1.03  fof(f48,plain,(
% 4.06/1.03    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f25])).
% 4.06/1.03  
% 4.06/1.03  fof(f3,axiom,(
% 4.06/1.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f15,plain,(
% 4.06/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.06/1.03    inference(ennf_transformation,[],[f3])).
% 4.06/1.03  
% 4.06/1.03  fof(f38,plain,(
% 4.06/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f15])).
% 4.06/1.03  
% 4.06/1.03  fof(f6,axiom,(
% 4.06/1.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f41,plain,(
% 4.06/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f6])).
% 4.06/1.03  
% 4.06/1.03  fof(f57,plain,(
% 4.06/1.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 4.06/1.03    inference(definition_unfolding,[],[f41,f42])).
% 4.06/1.03  
% 4.06/1.03  fof(f4,axiom,(
% 4.06/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f16,plain,(
% 4.06/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.06/1.03    inference(ennf_transformation,[],[f4])).
% 4.06/1.03  
% 4.06/1.03  fof(f39,plain,(
% 4.06/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f16])).
% 4.06/1.03  
% 4.06/1.03  fof(f5,axiom,(
% 4.06/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/1.03  
% 4.06/1.03  fof(f40,plain,(
% 4.06/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.06/1.03    inference(cnf_transformation,[],[f5])).
% 4.06/1.03  
% 4.06/1.03  fof(f36,plain,(
% 4.06/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.06/1.03    inference(cnf_transformation,[],[f30])).
% 4.06/1.03  
% 4.06/1.03  fof(f56,plain,(
% 4.06/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 4.06/1.03    inference(definition_unfolding,[],[f36,f42])).
% 4.06/1.03  
% 4.06/1.03  fof(f33,plain,(
% 4.06/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.06/1.03    inference(cnf_transformation,[],[f29])).
% 4.06/1.03  
% 4.06/1.03  fof(f59,plain,(
% 4.06/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.06/1.03    inference(equality_resolution,[],[f33])).
% 4.06/1.03  
% 4.06/1.03  fof(f54,plain,(
% 4.06/1.03    ~r1_tarski(sK0,sK1)),
% 4.06/1.03    inference(cnf_transformation,[],[f32])).
% 4.06/1.03  
% 4.06/1.03  fof(f52,plain,(
% 4.06/1.03    r1_tarski(sK0,k1_relat_1(sK2))),
% 4.06/1.03    inference(cnf_transformation,[],[f32])).
% 4.06/1.03  
% 4.06/1.03  cnf(c_355,plain,
% 4.06/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.06/1.03      theory(equality) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1028,plain,
% 4.06/1.03      ( ~ r1_tarski(X0,X1)
% 4.06/1.03      | r1_tarski(X2,k1_relat_1(X3))
% 4.06/1.03      | X2 != X0
% 4.06/1.03      | k1_relat_1(X3) != X1 ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_355]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1152,plain,
% 4.06/1.03      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 4.06/1.03      | r1_tarski(X2,k1_relat_1(X3))
% 4.06/1.03      | X2 != X0
% 4.06/1.03      | k1_relat_1(X3) != k1_relat_1(X1) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_1028]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1459,plain,
% 4.06/1.03      ( r1_tarski(X0,k1_relat_1(X1))
% 4.06/1.03      | ~ r1_tarski(sK0,k1_relat_1(sK2))
% 4.06/1.03      | X0 != sK0
% 4.06/1.03      | k1_relat_1(X1) != k1_relat_1(sK2) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_1152]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_2681,plain,
% 4.06/1.03      ( r1_tarski(k2_xboole_0(k6_subset_1(sK0,X0),sK0),k1_relat_1(X1))
% 4.06/1.03      | ~ r1_tarski(sK0,k1_relat_1(sK2))
% 4.06/1.03      | k2_xboole_0(k6_subset_1(sK0,X0),sK0) != sK0
% 4.06/1.03      | k1_relat_1(X1) != k1_relat_1(sK2) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_1459]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_18598,plain,
% 4.06/1.03      ( r1_tarski(k2_xboole_0(k6_subset_1(sK0,sK1),sK0),k1_relat_1(X0))
% 4.06/1.03      | ~ r1_tarski(sK0,k1_relat_1(sK2))
% 4.06/1.03      | k2_xboole_0(k6_subset_1(sK0,sK1),sK0) != sK0
% 4.06/1.03      | k1_relat_1(X0) != k1_relat_1(sK2) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_2681]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_18600,plain,
% 4.06/1.03      ( r1_tarski(k2_xboole_0(k6_subset_1(sK0,sK1),sK0),k1_relat_1(sK2))
% 4.06/1.03      | ~ r1_tarski(sK0,k1_relat_1(sK2))
% 4.06/1.03      | k2_xboole_0(k6_subset_1(sK0,sK1),sK0) != sK0
% 4.06/1.03      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_18598]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_16,negated_conjecture,
% 4.06/1.03      ( v2_funct_1(sK2) ),
% 4.06/1.03      inference(cnf_transformation,[],[f53]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_796,plain,
% 4.06/1.03      ( v2_funct_1(sK2) = iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_12,plain,
% 4.06/1.03      ( ~ v2_funct_1(X0)
% 4.06/1.03      | ~ v1_funct_1(X0)
% 4.06/1.03      | ~ v1_relat_1(X0)
% 4.06/1.03      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 4.06/1.03      inference(cnf_transformation,[],[f46]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_800,plain,
% 4.06/1.03      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 4.06/1.03      | v2_funct_1(X0) != iProver_top
% 4.06/1.03      | v1_funct_1(X0) != iProver_top
% 4.06/1.03      | v1_relat_1(X0) != iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_3397,plain,
% 4.06/1.03      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
% 4.06/1.03      | v1_funct_1(sK2) != iProver_top
% 4.06/1.03      | v1_relat_1(sK2) != iProver_top ),
% 4.06/1.03      inference(superposition,[status(thm)],[c_796,c_800]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_20,negated_conjecture,
% 4.06/1.03      ( v1_relat_1(sK2) ),
% 4.06/1.03      inference(cnf_transformation,[],[f49]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_21,plain,
% 4.06/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_19,negated_conjecture,
% 4.06/1.03      ( v1_funct_1(sK2) ),
% 4.06/1.03      inference(cnf_transformation,[],[f50]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_22,plain,
% 4.06/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_3833,plain,
% 4.06/1.03      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 4.06/1.03      inference(global_propositional_subsumption,
% 4.06/1.03                [status(thm)],
% 4.06/1.03                [c_3397,c_21,c_22]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_18,negated_conjecture,
% 4.06/1.03      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 4.06/1.03      inference(cnf_transformation,[],[f51]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_794,plain,
% 4.06/1.03      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_3,plain,
% 4.06/1.03      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 4.06/1.03      inference(cnf_transformation,[],[f55]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_809,plain,
% 4.06/1.03      ( k6_subset_1(X0,X1) = k1_xboole_0
% 4.06/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_2048,plain,
% 4.06/1.03      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 4.06/1.03      inference(superposition,[status(thm)],[c_794,c_809]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_3846,plain,
% 4.06/1.03      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 4.06/1.03      inference(superposition,[status(thm)],[c_3833,c_2048]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_13,plain,
% 4.06/1.03      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 4.06/1.03      | ~ r1_tarski(X0,k1_relat_1(X1))
% 4.06/1.03      | ~ v1_relat_1(X1) ),
% 4.06/1.03      inference(cnf_transformation,[],[f47]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_799,plain,
% 4.06/1.03      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 4.06/1.03      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 4.06/1.03      | v1_relat_1(X1) != iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_0,plain,
% 4.06/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.06/1.03      inference(cnf_transformation,[],[f35]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_811,plain,
% 4.06/1.03      ( X0 = X1
% 4.06/1.03      | r1_tarski(X0,X1) != iProver_top
% 4.06/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_2452,plain,
% 4.06/1.03      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 4.06/1.03      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 4.06/1.03      | r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) != iProver_top
% 4.06/1.03      | v1_relat_1(X0) != iProver_top ),
% 4.06/1.03      inference(superposition,[status(thm)],[c_799,c_811]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_15818,plain,
% 4.06/1.03      ( k10_relat_1(sK2,k9_relat_1(sK2,k6_subset_1(sK0,sK1))) = k6_subset_1(sK0,sK1)
% 4.06/1.03      | r1_tarski(k10_relat_1(sK2,k1_xboole_0),k6_subset_1(sK0,sK1)) != iProver_top
% 4.06/1.03      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 4.06/1.03      | v1_relat_1(sK2) != iProver_top ),
% 4.06/1.03      inference(superposition,[status(thm)],[c_3846,c_2452]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_793,plain,
% 4.06/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_11,plain,
% 4.06/1.03      ( ~ v1_funct_1(X0)
% 4.06/1.03      | ~ v1_relat_1(X0)
% 4.06/1.03      | v1_relat_1(k2_funct_1(X0)) ),
% 4.06/1.03      inference(cnf_transformation,[],[f44]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_801,plain,
% 4.06/1.03      ( v1_funct_1(X0) != iProver_top
% 4.06/1.03      | v1_relat_1(X0) != iProver_top
% 4.06/1.03      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_9,plain,
% 4.06/1.03      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.06/1.03      inference(cnf_transformation,[],[f43]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_803,plain,
% 4.06/1.03      ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 4.06/1.03      | v1_relat_1(X0) != iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_2289,plain,
% 4.06/1.03      ( k9_relat_1(k2_funct_1(X0),k1_xboole_0) = k1_xboole_0
% 4.06/1.03      | v1_funct_1(X0) != iProver_top
% 4.06/1.03      | v1_relat_1(X0) != iProver_top ),
% 4.06/1.03      inference(superposition,[status(thm)],[c_801,c_803]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_12766,plain,
% 4.06/1.03      ( k9_relat_1(k2_funct_1(sK2),k1_xboole_0) = k1_xboole_0
% 4.06/1.03      | v1_relat_1(sK2) != iProver_top ),
% 4.06/1.03      inference(superposition,[status(thm)],[c_793,c_2289]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_14,plain,
% 4.06/1.03      ( ~ v2_funct_1(X0)
% 4.06/1.03      | ~ v1_funct_1(X0)
% 4.06/1.03      | ~ v1_relat_1(X0)
% 4.06/1.03      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 4.06/1.03      inference(cnf_transformation,[],[f48]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_798,plain,
% 4.06/1.03      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 4.06/1.03      | v2_funct_1(X0) != iProver_top
% 4.06/1.03      | v1_funct_1(X0) != iProver_top
% 4.06/1.03      | v1_relat_1(X0) != iProver_top ),
% 4.06/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1202,plain,
% 4.06/1.03      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 4.06/1.03      | v1_funct_1(sK2) != iProver_top
% 4.06/1.03      | v1_relat_1(sK2) != iProver_top ),
% 4.06/1.03      inference(superposition,[status(thm)],[c_796,c_798]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1822,plain,
% 4.06/1.03      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 4.06/1.03      inference(global_propositional_subsumption,
% 4.06/1.03                [status(thm)],
% 4.06/1.03                [c_1202,c_21,c_22]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_12769,plain,
% 4.06/1.03      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0
% 4.06/1.03      | v1_relat_1(sK2) != iProver_top ),
% 4.06/1.03      inference(demodulation,[status(thm)],[c_12766,c_1822]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_14304,plain,
% 4.06/1.03      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 4.06/1.03      inference(global_propositional_subsumption,
% 4.06/1.03                [status(thm)],
% 4.06/1.03                [c_12769,c_21]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_15983,plain,
% 4.06/1.03      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 4.06/1.03      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 4.06/1.03      | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) != iProver_top
% 4.06/1.03      | v1_relat_1(sK2) != iProver_top ),
% 4.06/1.03      inference(light_normalisation,
% 4.06/1.03                [status(thm)],
% 4.06/1.03                [c_15818,c_3846,c_14304]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_16044,plain,
% 4.06/1.03      ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
% 4.06/1.03      | ~ r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
% 4.06/1.03      | ~ v1_relat_1(sK2)
% 4.06/1.03      | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 4.06/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_15983]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_5,plain,
% 4.06/1.03      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 4.06/1.03      inference(cnf_transformation,[],[f38]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_985,plain,
% 4.06/1.03      ( r1_tarski(X0,k1_relat_1(X1))
% 4.06/1.03      | ~ r1_tarski(k2_xboole_0(X0,X2),k1_relat_1(X1)) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_3097,plain,
% 4.06/1.03      ( ~ r1_tarski(k2_xboole_0(k6_subset_1(sK0,X0),sK0),k1_relat_1(X1))
% 4.06/1.03      | r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(X1)) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_985]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_11046,plain,
% 4.06/1.03      ( ~ r1_tarski(k2_xboole_0(k6_subset_1(sK0,sK1),sK0),k1_relat_1(X0))
% 4.06/1.03      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(X0)) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_3097]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_11052,plain,
% 4.06/1.03      ( ~ r1_tarski(k2_xboole_0(k6_subset_1(sK0,sK1),sK0),k1_relat_1(sK2))
% 4.06/1.03      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_11046]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_8,plain,
% 4.06/1.03      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 4.06/1.03      inference(cnf_transformation,[],[f57]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1257,plain,
% 4.06/1.03      ( r1_tarski(k6_subset_1(sK0,X0),sK0) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_6434,plain,
% 4.06/1.03      ( r1_tarski(k6_subset_1(sK0,sK1),sK0) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_1257]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_6,plain,
% 4.06/1.03      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 4.06/1.03      inference(cnf_transformation,[],[f39]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1479,plain,
% 4.06/1.03      ( ~ r1_tarski(X0,sK0) | k2_xboole_0(X0,sK0) = sK0 ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1727,plain,
% 4.06/1.03      ( ~ r1_tarski(k6_subset_1(sK0,X0),sK0)
% 4.06/1.03      | k2_xboole_0(k6_subset_1(sK0,X0),sK0) = sK0 ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_1479]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_4405,plain,
% 4.06/1.03      ( ~ r1_tarski(k6_subset_1(sK0,sK1),sK0)
% 4.06/1.03      | k2_xboole_0(k6_subset_1(sK0,sK1),sK0) = sK0 ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_1727]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_7,plain,
% 4.06/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 4.06/1.03      inference(cnf_transformation,[],[f40]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_1163,plain,
% 4.06/1.03      ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_4,plain,
% 4.06/1.03      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 4.06/1.03      inference(cnf_transformation,[],[f56]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_962,plain,
% 4.06/1.03      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_362,plain,
% 4.06/1.03      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 4.06/1.03      theory(equality) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_370,plain,
% 4.06/1.03      ( k1_relat_1(sK2) = k1_relat_1(sK2) | sK2 != sK2 ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_362]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_68,plain,
% 4.06/1.03      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_2,plain,
% 4.06/1.03      ( r1_tarski(X0,X0) ),
% 4.06/1.03      inference(cnf_transformation,[],[f59]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_64,plain,
% 4.06/1.03      ( r1_tarski(sK2,sK2) ),
% 4.06/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_15,negated_conjecture,
% 4.06/1.03      ( ~ r1_tarski(sK0,sK1) ),
% 4.06/1.03      inference(cnf_transformation,[],[f54]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(c_17,negated_conjecture,
% 4.06/1.03      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 4.06/1.03      inference(cnf_transformation,[],[f52]) ).
% 4.06/1.03  
% 4.06/1.03  cnf(contradiction,plain,
% 4.06/1.03      ( $false ),
% 4.06/1.03      inference(minisat,
% 4.06/1.03                [status(thm)],
% 4.06/1.03                [c_18600,c_16044,c_11052,c_6434,c_4405,c_1163,c_962,
% 4.06/1.03                 c_370,c_68,c_64,c_15,c_17,c_20]) ).
% 4.06/1.03  
% 4.06/1.03  
% 4.06/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 4.06/1.03  
% 4.06/1.03  ------                               Statistics
% 4.06/1.03  
% 4.06/1.03  ------ Selected
% 4.06/1.03  
% 4.06/1.03  total_time:                             0.43
% 4.06/1.03  
%------------------------------------------------------------------------------
