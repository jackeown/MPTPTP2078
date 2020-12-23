%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:39 EST 2020

% Result     : Theorem 11.58s
% Output     : CNFRefutation 11.58s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 274 expanded)
%              Number of clauses        :   52 (  79 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  273 (1002 expanded)
%              Number of equality atoms :   67 ( 226 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f36,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).

fof(f65,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

cnf(c_453,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_451,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5753,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_453,c_451])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_291,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_292,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_296,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK1))
    | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_24])).

cnf(c_17191,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_relat_1(sK1))
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) ),
    inference(resolution,[status(thm)],[c_5753,c_296])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_309,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_310,plain,
    ( ~ v1_relat_1(sK1)
    | k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_314,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_24])).

cnf(c_4,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_785,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2414,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_314,c_785])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_784,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7440,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_784])).

cnf(c_7492,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7440])).

cnf(c_18803,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17191,c_7492])).

cnf(c_18,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_242,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_243,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_245,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_24,c_23])).

cnf(c_19589,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK1,X1))
    | r1_tarski(k10_relat_1(sK1,X0),X1)
    | ~ r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_18803,c_245])).

cnf(c_774,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_8284,plain,
    ( r1_tarski(X0,k9_relat_1(sK1,X1)) != iProver_top
    | r1_tarski(k10_relat_1(sK1,X0),X1) = iProver_top
    | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7440,c_774])).

cnf(c_25,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1672,plain,
    ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1677,plain,
    ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1672])).

cnf(c_17036,plain,
    ( r1_tarski(k10_relat_1(sK1,X0),X1) = iProver_top
    | r1_tarski(X0,k9_relat_1(sK1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8284,c_25,c_1677])).

cnf(c_17037,plain,
    ( r1_tarski(X0,k9_relat_1(sK1,X1)) != iProver_top
    | r1_tarski(k10_relat_1(sK1,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_17036])).

cnf(c_17038,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK1,X1))
    | r1_tarski(k10_relat_1(sK1,X0),X1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17037])).

cnf(c_20684,plain,
    ( r1_tarski(k10_relat_1(sK1,X0),X1)
    | ~ r1_tarski(X0,k9_relat_1(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19589,c_17038])).

cnf(c_20685,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK1,X1))
    | r1_tarski(k10_relat_1(sK1,X0),X1) ),
    inference(renaming,[status(thm)],[c_20684])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3960,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(resolution,[status(thm)],[c_0,c_20])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_984,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1033,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4407,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3960,c_24,c_22,c_20,c_984,c_1033])).

cnf(c_20706,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(resolution,[status(thm)],[c_20685,c_4407])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_924,plain,
    ( r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_12842,plain,
    ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20706,c_12842])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.58/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.58/2.00  
% 11.58/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.58/2.00  
% 11.58/2.00  ------  iProver source info
% 11.58/2.00  
% 11.58/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.58/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.58/2.00  git: non_committed_changes: false
% 11.58/2.00  git: last_make_outside_of_git: false
% 11.58/2.00  
% 11.58/2.00  ------ 
% 11.58/2.00  ------ Parsing...
% 11.58/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.58/2.00  
% 11.58/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.58/2.00  
% 11.58/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.58/2.00  
% 11.58/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.58/2.00  ------ Proving...
% 11.58/2.00  ------ Problem Properties 
% 11.58/2.00  
% 11.58/2.00  
% 11.58/2.00  clauses                                 23
% 11.58/2.00  conjectures                             3
% 11.58/2.00  EPR                                     5
% 11.58/2.00  Horn                                    23
% 11.58/2.00  unary                                   12
% 11.58/2.00  binary                                  6
% 11.58/2.00  lits                                    39
% 11.58/2.00  lits eq                                 13
% 11.58/2.00  fd_pure                                 0
% 11.58/2.00  fd_pseudo                               0
% 11.58/2.00  fd_cond                                 0
% 11.58/2.00  fd_pseudo_cond                          1
% 11.58/2.00  AC symbols                              0
% 11.58/2.00  
% 11.58/2.00  ------ Input Options Time Limit: Unbounded
% 11.58/2.00  
% 11.58/2.00  
% 11.58/2.00  ------ 
% 11.58/2.00  Current options:
% 11.58/2.00  ------ 
% 11.58/2.00  
% 11.58/2.00  
% 11.58/2.00  
% 11.58/2.00  
% 11.58/2.00  ------ Proving...
% 11.58/2.00  
% 11.58/2.00  
% 11.58/2.00  % SZS status Theorem for theBenchmark.p
% 11.58/2.00  
% 11.58/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.58/2.00  
% 11.58/2.00  fof(f15,axiom,(
% 11.58/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f30,plain,(
% 11.58/2.00    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.58/2.00    inference(ennf_transformation,[],[f15])).
% 11.58/2.00  
% 11.58/2.00  fof(f31,plain,(
% 11.58/2.00    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.58/2.00    inference(flattening,[],[f30])).
% 11.58/2.00  
% 11.58/2.00  fof(f60,plain,(
% 11.58/2.00    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f31])).
% 11.58/2.00  
% 11.58/2.00  fof(f19,conjecture,(
% 11.58/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f20,negated_conjecture,(
% 11.58/2.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 11.58/2.00    inference(negated_conjecture,[],[f19])).
% 11.58/2.00  
% 11.58/2.00  fof(f36,plain,(
% 11.58/2.00    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 11.58/2.00    inference(ennf_transformation,[],[f20])).
% 11.58/2.00  
% 11.58/2.00  fof(f37,plain,(
% 11.58/2.00    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 11.58/2.00    inference(flattening,[],[f36])).
% 11.58/2.00  
% 11.58/2.00  fof(f40,plain,(
% 11.58/2.00    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 11.58/2.00    introduced(choice_axiom,[])).
% 11.58/2.00  
% 11.58/2.00  fof(f41,plain,(
% 11.58/2.00    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 11.58/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).
% 11.58/2.00  
% 11.58/2.00  fof(f65,plain,(
% 11.58/2.00    v1_funct_1(sK1)),
% 11.58/2.00    inference(cnf_transformation,[],[f41])).
% 11.58/2.00  
% 11.58/2.00  fof(f64,plain,(
% 11.58/2.00    v1_relat_1(sK1)),
% 11.58/2.00    inference(cnf_transformation,[],[f41])).
% 11.58/2.00  
% 11.58/2.00  fof(f16,axiom,(
% 11.58/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f32,plain,(
% 11.58/2.00    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.58/2.00    inference(ennf_transformation,[],[f16])).
% 11.58/2.00  
% 11.58/2.00  fof(f33,plain,(
% 11.58/2.00    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.58/2.00    inference(flattening,[],[f32])).
% 11.58/2.00  
% 11.58/2.00  fof(f61,plain,(
% 11.58/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f33])).
% 11.58/2.00  
% 11.58/2.00  fof(f7,axiom,(
% 11.58/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f50,plain,(
% 11.58/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.58/2.00    inference(cnf_transformation,[],[f7])).
% 11.58/2.00  
% 11.58/2.00  fof(f6,axiom,(
% 11.58/2.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f49,plain,(
% 11.58/2.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f6])).
% 11.58/2.00  
% 11.58/2.00  fof(f69,plain,(
% 11.58/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 11.58/2.00    inference(definition_unfolding,[],[f50,f49])).
% 11.58/2.00  
% 11.58/2.00  fof(f71,plain,(
% 11.58/2.00    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.58/2.00    inference(definition_unfolding,[],[f61,f69])).
% 11.58/2.00  
% 11.58/2.00  fof(f3,axiom,(
% 11.58/2.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f46,plain,(
% 11.58/2.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f3])).
% 11.58/2.00  
% 11.58/2.00  fof(f70,plain,(
% 11.58/2.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 11.58/2.00    inference(definition_unfolding,[],[f46,f69])).
% 11.58/2.00  
% 11.58/2.00  fof(f4,axiom,(
% 11.58/2.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f22,plain,(
% 11.58/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.58/2.00    inference(ennf_transformation,[],[f4])).
% 11.58/2.00  
% 11.58/2.00  fof(f23,plain,(
% 11.58/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.58/2.00    inference(flattening,[],[f22])).
% 11.58/2.00  
% 11.58/2.00  fof(f47,plain,(
% 11.58/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f23])).
% 11.58/2.00  
% 11.58/2.00  fof(f17,axiom,(
% 11.58/2.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f34,plain,(
% 11.58/2.00    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.58/2.00    inference(ennf_transformation,[],[f17])).
% 11.58/2.00  
% 11.58/2.00  fof(f35,plain,(
% 11.58/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.58/2.00    inference(flattening,[],[f34])).
% 11.58/2.00  
% 11.58/2.00  fof(f62,plain,(
% 11.58/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f35])).
% 11.58/2.00  
% 11.58/2.00  fof(f67,plain,(
% 11.58/2.00    v2_funct_1(sK1)),
% 11.58/2.00    inference(cnf_transformation,[],[f41])).
% 11.58/2.00  
% 11.58/2.00  fof(f9,axiom,(
% 11.58/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f25,plain,(
% 11.58/2.00    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.58/2.00    inference(ennf_transformation,[],[f9])).
% 11.58/2.00  
% 11.58/2.00  fof(f52,plain,(
% 11.58/2.00    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f25])).
% 11.58/2.00  
% 11.58/2.00  fof(f1,axiom,(
% 11.58/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f38,plain,(
% 11.58/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.58/2.00    inference(nnf_transformation,[],[f1])).
% 11.58/2.00  
% 11.58/2.00  fof(f39,plain,(
% 11.58/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.58/2.00    inference(flattening,[],[f38])).
% 11.58/2.00  
% 11.58/2.00  fof(f44,plain,(
% 11.58/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f39])).
% 11.58/2.00  
% 11.58/2.00  fof(f68,plain,(
% 11.58/2.00    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 11.58/2.00    inference(cnf_transformation,[],[f41])).
% 11.58/2.00  
% 11.58/2.00  fof(f66,plain,(
% 11.58/2.00    r1_tarski(sK0,k1_relat_1(sK1))),
% 11.58/2.00    inference(cnf_transformation,[],[f41])).
% 11.58/2.00  
% 11.58/2.00  fof(f14,axiom,(
% 11.58/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 11.58/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.58/2.00  
% 11.58/2.00  fof(f28,plain,(
% 11.58/2.00    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.58/2.00    inference(ennf_transformation,[],[f14])).
% 11.58/2.00  
% 11.58/2.00  fof(f29,plain,(
% 11.58/2.00    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.58/2.00    inference(flattening,[],[f28])).
% 11.58/2.00  
% 11.58/2.00  fof(f59,plain,(
% 11.58/2.00    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.58/2.00    inference(cnf_transformation,[],[f29])).
% 11.58/2.00  
% 11.58/2.00  fof(f42,plain,(
% 11.58/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.58/2.00    inference(cnf_transformation,[],[f39])).
% 11.58/2.00  
% 11.58/2.00  fof(f74,plain,(
% 11.58/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.58/2.00    inference(equality_resolution,[],[f42])).
% 11.58/2.00  
% 11.58/2.00  cnf(c_453,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.58/2.00      theory(equality) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_451,plain,( X0 = X0 ),theory(equality) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_5753,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.58/2.00      inference(resolution,[status(thm)],[c_453,c_451]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_16,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 11.58/2.00      | ~ v1_funct_1(X1)
% 11.58/2.00      | ~ v1_relat_1(X1)
% 11.58/2.00      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 11.58/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_23,negated_conjecture,
% 11.58/2.00      ( v1_funct_1(sK1) ),
% 11.58/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_291,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 11.58/2.00      | ~ v1_relat_1(X1)
% 11.58/2.00      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 11.58/2.00      | sK1 != X1 ),
% 11.58/2.00      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_292,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,k2_relat_1(sK1))
% 11.58/2.00      | ~ v1_relat_1(sK1)
% 11.58/2.00      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ),
% 11.58/2.00      inference(unflattening,[status(thm)],[c_291]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_24,negated_conjecture,
% 11.58/2.00      ( v1_relat_1(sK1) ),
% 11.58/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_296,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,k2_relat_1(sK1))
% 11.58/2.00      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ),
% 11.58/2.00      inference(global_propositional_subsumption,
% 11.58/2.00                [status(thm)],
% 11.58/2.00                [c_292,c_24]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_17191,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,X1)
% 11.58/2.00      | ~ r1_tarski(X0,k2_relat_1(sK1))
% 11.58/2.00      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) ),
% 11.58/2.00      inference(resolution,[status(thm)],[c_5753,c_296]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_17,plain,
% 11.58/2.00      ( ~ v1_funct_1(X0)
% 11.58/2.00      | ~ v1_relat_1(X0)
% 11.58/2.00      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 11.58/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_309,plain,
% 11.58/2.00      ( ~ v1_relat_1(X0)
% 11.58/2.00      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 11.58/2.00      | sK1 != X0 ),
% 11.58/2.00      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_310,plain,
% 11.58/2.00      ( ~ v1_relat_1(sK1)
% 11.58/2.00      | k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
% 11.58/2.00      inference(unflattening,[status(thm)],[c_309]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_314,plain,
% 11.58/2.00      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
% 11.58/2.00      inference(global_propositional_subsumption,
% 11.58/2.00                [status(thm)],
% 11.58/2.00                [c_310,c_24]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_4,plain,
% 11.58/2.00      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 11.58/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_785,plain,
% 11.58/2.00      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 11.58/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_2414,plain,
% 11.58/2.00      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = iProver_top ),
% 11.58/2.00      inference(superposition,[status(thm)],[c_314,c_785]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_5,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.58/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_784,plain,
% 11.58/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.58/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.58/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 11.58/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_7440,plain,
% 11.58/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.58/2.00      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) = iProver_top ),
% 11.58/2.00      inference(superposition,[status(thm)],[c_2414,c_784]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_7492,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,X1)
% 11.58/2.00      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) ),
% 11.58/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_7440]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_18803,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,X1)
% 11.58/2.00      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) ),
% 11.58/2.00      inference(global_propositional_subsumption,
% 11.58/2.00                [status(thm)],
% 11.58/2.00                [c_17191,c_7492]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_18,plain,
% 11.58/2.00      ( r1_tarski(X0,X1)
% 11.58/2.00      | ~ r1_tarski(X0,k1_relat_1(X2))
% 11.58/2.00      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 11.58/2.00      | ~ v2_funct_1(X2)
% 11.58/2.00      | ~ v1_funct_1(X2)
% 11.58/2.00      | ~ v1_relat_1(X2) ),
% 11.58/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_21,negated_conjecture,
% 11.58/2.00      ( v2_funct_1(sK1) ),
% 11.58/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_242,plain,
% 11.58/2.00      ( r1_tarski(X0,X1)
% 11.58/2.00      | ~ r1_tarski(X0,k1_relat_1(X2))
% 11.58/2.00      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 11.58/2.00      | ~ v1_funct_1(X2)
% 11.58/2.00      | ~ v1_relat_1(X2)
% 11.58/2.00      | sK1 != X2 ),
% 11.58/2.00      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_243,plain,
% 11.58/2.00      ( r1_tarski(X0,X1)
% 11.58/2.00      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 11.58/2.00      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
% 11.58/2.00      | ~ v1_funct_1(sK1)
% 11.58/2.00      | ~ v1_relat_1(sK1) ),
% 11.58/2.00      inference(unflattening,[status(thm)],[c_242]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_245,plain,
% 11.58/2.00      ( r1_tarski(X0,X1)
% 11.58/2.00      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 11.58/2.00      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
% 11.58/2.00      inference(global_propositional_subsumption,
% 11.58/2.00                [status(thm)],
% 11.58/2.00                [c_243,c_24,c_23]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_19589,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,k9_relat_1(sK1,X1))
% 11.58/2.00      | r1_tarski(k10_relat_1(sK1,X0),X1)
% 11.58/2.00      | ~ r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
% 11.58/2.00      inference(resolution,[status(thm)],[c_18803,c_245]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_774,plain,
% 11.58/2.00      ( r1_tarski(X0,X1) = iProver_top
% 11.58/2.00      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
% 11.58/2.00      | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) != iProver_top ),
% 11.58/2.00      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_8284,plain,
% 11.58/2.00      ( r1_tarski(X0,k9_relat_1(sK1,X1)) != iProver_top
% 11.58/2.00      | r1_tarski(k10_relat_1(sK1,X0),X1) = iProver_top
% 11.58/2.00      | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) != iProver_top ),
% 11.58/2.00      inference(superposition,[status(thm)],[c_7440,c_774]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_25,plain,
% 11.58/2.00      ( v1_relat_1(sK1) = iProver_top ),
% 11.58/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_8,plain,
% 11.58/2.00      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 11.58/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_1672,plain,
% 11.58/2.00      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
% 11.58/2.00      | ~ v1_relat_1(sK1) ),
% 11.58/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_1677,plain,
% 11.58/2.00      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = iProver_top
% 11.58/2.00      | v1_relat_1(sK1) != iProver_top ),
% 11.58/2.00      inference(predicate_to_equality,[status(thm)],[c_1672]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_17036,plain,
% 11.58/2.00      ( r1_tarski(k10_relat_1(sK1,X0),X1) = iProver_top
% 11.58/2.00      | r1_tarski(X0,k9_relat_1(sK1,X1)) != iProver_top ),
% 11.58/2.00      inference(global_propositional_subsumption,
% 11.58/2.00                [status(thm)],
% 11.58/2.00                [c_8284,c_25,c_1677]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_17037,plain,
% 11.58/2.00      ( r1_tarski(X0,k9_relat_1(sK1,X1)) != iProver_top
% 11.58/2.00      | r1_tarski(k10_relat_1(sK1,X0),X1) = iProver_top ),
% 11.58/2.00      inference(renaming,[status(thm)],[c_17036]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_17038,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,k9_relat_1(sK1,X1))
% 11.58/2.00      | r1_tarski(k10_relat_1(sK1,X0),X1) ),
% 11.58/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_17037]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_20684,plain,
% 11.58/2.00      ( r1_tarski(k10_relat_1(sK1,X0),X1)
% 11.58/2.00      | ~ r1_tarski(X0,k9_relat_1(sK1,X1)) ),
% 11.58/2.00      inference(global_propositional_subsumption,
% 11.58/2.00                [status(thm)],
% 11.58/2.00                [c_19589,c_17038]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_20685,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,k9_relat_1(sK1,X1))
% 11.58/2.00      | r1_tarski(k10_relat_1(sK1,X0),X1) ),
% 11.58/2.00      inference(renaming,[status(thm)],[c_20684]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_0,plain,
% 11.58/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.58/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_20,negated_conjecture,
% 11.58/2.00      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 11.58/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_3960,plain,
% 11.58/2.00      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 11.58/2.00      | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 11.58/2.00      inference(resolution,[status(thm)],[c_0,c_20]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_22,negated_conjecture,
% 11.58/2.00      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 11.58/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_984,plain,
% 11.58/2.00      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 11.58/2.00      | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 11.58/2.00      | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 11.58/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_15,plain,
% 11.58/2.00      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 11.58/2.00      | ~ r1_tarski(X0,k1_relat_1(X1))
% 11.58/2.00      | ~ v1_relat_1(X1) ),
% 11.58/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_1033,plain,
% 11.58/2.00      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 11.58/2.00      | ~ r1_tarski(sK0,k1_relat_1(sK1))
% 11.58/2.00      | ~ v1_relat_1(sK1) ),
% 11.58/2.00      inference(instantiation,[status(thm)],[c_15]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_4407,plain,
% 11.58/2.00      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
% 11.58/2.00      inference(global_propositional_subsumption,
% 11.58/2.00                [status(thm)],
% 11.58/2.00                [c_3960,c_24,c_22,c_20,c_984,c_1033]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_20706,plain,
% 11.58/2.00      ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
% 11.58/2.00      inference(resolution,[status(thm)],[c_20685,c_4407]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_2,plain,
% 11.58/2.00      ( r1_tarski(X0,X0) ),
% 11.58/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_924,plain,
% 11.58/2.00      ( r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X0)) ),
% 11.58/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(c_12842,plain,
% 11.58/2.00      ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
% 11.58/2.00      inference(instantiation,[status(thm)],[c_924]) ).
% 11.58/2.00  
% 11.58/2.00  cnf(contradiction,plain,
% 11.58/2.00      ( $false ),
% 11.58/2.00      inference(minisat,[status(thm)],[c_20706,c_12842]) ).
% 11.58/2.00  
% 11.58/2.00  
% 11.58/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.58/2.00  
% 11.58/2.00  ------                               Statistics
% 11.58/2.00  
% 11.58/2.00  ------ Selected
% 11.58/2.00  
% 11.58/2.00  total_time:                             1.119
% 11.58/2.00  
%------------------------------------------------------------------------------
