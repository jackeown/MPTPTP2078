%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:08 EST 2020

% Result     : Theorem 11.52s
% Output     : CNFRefutation 11.52s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 548 expanded)
%              Number of clauses        :   62 ( 139 expanded)
%              Number of leaves         :   15 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          :  309 (1990 expanded)
%              Number of equality atoms :  130 ( 351 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f43,plain,
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

fof(f44,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43])).

fof(f70,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f59,f73,f73])).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f74,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f45,f73,f73])).

fof(f68,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f69,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f73])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f73])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_677,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_685,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3889,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_685])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4392,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3889,c_24,c_25])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4407,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_4392,c_0])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_675,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_689,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1488,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_675,c_689])).

cnf(c_5350,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_4407,c_1488])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_676,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_692,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2158,plain,
    ( k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_689])).

cnf(c_7383,plain,
    ( k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_relat_1(sK2))) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)) ),
    inference(superposition,[status(thm)],[c_676,c_2158])).

cnf(c_5,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_691,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1193,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_691])).

cnf(c_7791,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7383,c_1193])).

cnf(c_8107,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,sK0)),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_7791])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_680,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2174,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_680])).

cnf(c_34,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2802,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_23,c_22,c_19,c_34])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_683,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3825,plain,
    ( k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2802,c_683])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_51,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_53,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_54,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_56,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_31366,plain,
    ( k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3825,c_24,c_25,c_53,c_56])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_682,plain,
    ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3649,plain,
    ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_682])).

cnf(c_4382,plain,
    ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3649,c_24,c_25])).

cnf(c_31372,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31366,c_4382])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_681,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3640,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_681])).

cnf(c_4091,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3640,c_24,c_25])).

cnf(c_31373,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31372,c_4091])).

cnf(c_31385,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,sK0)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK0)) ),
    inference(superposition,[status(thm)],[c_8107,c_31373])).

cnf(c_33778,plain,
    ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_5350,c_31385])).

cnf(c_31382,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_676,c_31373])).

cnf(c_33798,plain,
    ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_33778,c_31382])).

cnf(c_35503,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_33798,c_691])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35503,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:55:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 11.52/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.52/2.01  
% 11.52/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.52/2.01  
% 11.52/2.01  ------  iProver source info
% 11.52/2.01  
% 11.52/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.52/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.52/2.01  git: non_committed_changes: false
% 11.52/2.01  git: last_make_outside_of_git: false
% 11.52/2.01  
% 11.52/2.01  ------ 
% 11.52/2.01  ------ Parsing...
% 11.52/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.52/2.01  ------ Proving...
% 11.52/2.01  ------ Problem Properties 
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  clauses                                 23
% 11.52/2.01  conjectures                             6
% 11.52/2.01  EPR                                     7
% 11.52/2.01  Horn                                    23
% 11.52/2.01  unary                                   9
% 11.52/2.01  binary                                  3
% 11.52/2.01  lits                                    54
% 11.52/2.01  lits eq                                 10
% 11.52/2.01  fd_pure                                 0
% 11.52/2.01  fd_pseudo                               0
% 11.52/2.01  fd_cond                                 0
% 11.52/2.01  fd_pseudo_cond                          1
% 11.52/2.01  AC symbols                              0
% 11.52/2.01  
% 11.52/2.01  ------ Input Options Time Limit: Unbounded
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  ------ 
% 11.52/2.01  Current options:
% 11.52/2.01  ------ 
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  ------ Proving...
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  % SZS status Theorem for theBenchmark.p
% 11.52/2.01  
% 11.52/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.52/2.01  
% 11.52/2.01  fof(f18,conjecture,(
% 11.52/2.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f19,negated_conjecture,(
% 11.52/2.01    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.52/2.01    inference(negated_conjecture,[],[f18])).
% 11.52/2.01  
% 11.52/2.01  fof(f39,plain,(
% 11.52/2.01    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 11.52/2.01    inference(ennf_transformation,[],[f19])).
% 11.52/2.01  
% 11.52/2.01  fof(f40,plain,(
% 11.52/2.01    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.52/2.01    inference(flattening,[],[f39])).
% 11.52/2.01  
% 11.52/2.01  fof(f43,plain,(
% 11.52/2.01    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 11.52/2.01    introduced(choice_axiom,[])).
% 11.52/2.01  
% 11.52/2.01  fof(f44,plain,(
% 11.52/2.01    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 11.52/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43])).
% 11.52/2.01  
% 11.52/2.01  fof(f70,plain,(
% 11.52/2.01    v2_funct_1(sK2)),
% 11.52/2.01    inference(cnf_transformation,[],[f44])).
% 11.52/2.01  
% 11.52/2.01  fof(f12,axiom,(
% 11.52/2.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f27,plain,(
% 11.52/2.01    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.52/2.01    inference(ennf_transformation,[],[f12])).
% 11.52/2.01  
% 11.52/2.01  fof(f28,plain,(
% 11.52/2.01    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.52/2.01    inference(flattening,[],[f27])).
% 11.52/2.01  
% 11.52/2.01  fof(f59,plain,(
% 11.52/2.01    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f28])).
% 11.52/2.01  
% 11.52/2.01  fof(f9,axiom,(
% 11.52/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f55,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.52/2.01    inference(cnf_transformation,[],[f9])).
% 11.52/2.01  
% 11.52/2.01  fof(f7,axiom,(
% 11.52/2.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f53,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f7])).
% 11.52/2.01  
% 11.52/2.01  fof(f8,axiom,(
% 11.52/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f54,plain,(
% 11.52/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f8])).
% 11.52/2.01  
% 11.52/2.01  fof(f72,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.52/2.01    inference(definition_unfolding,[],[f53,f54])).
% 11.52/2.01  
% 11.52/2.01  fof(f73,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 11.52/2.01    inference(definition_unfolding,[],[f55,f72])).
% 11.52/2.01  
% 11.52/2.01  fof(f78,plain,(
% 11.52/2.01    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.52/2.01    inference(definition_unfolding,[],[f59,f73,f73])).
% 11.52/2.01  
% 11.52/2.01  fof(f66,plain,(
% 11.52/2.01    v1_relat_1(sK2)),
% 11.52/2.01    inference(cnf_transformation,[],[f44])).
% 11.52/2.01  
% 11.52/2.01  fof(f67,plain,(
% 11.52/2.01    v1_funct_1(sK2)),
% 11.52/2.01    inference(cnf_transformation,[],[f44])).
% 11.52/2.01  
% 11.52/2.01  fof(f1,axiom,(
% 11.52/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f45,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f1])).
% 11.52/2.01  
% 11.52/2.01  fof(f74,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 11.52/2.01    inference(definition_unfolding,[],[f45,f73,f73])).
% 11.52/2.01  
% 11.52/2.01  fof(f68,plain,(
% 11.52/2.01    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 11.52/2.01    inference(cnf_transformation,[],[f44])).
% 11.52/2.01  
% 11.52/2.01  fof(f6,axiom,(
% 11.52/2.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f23,plain,(
% 11.52/2.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.52/2.01    inference(ennf_transformation,[],[f6])).
% 11.52/2.01  
% 11.52/2.01  fof(f52,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f23])).
% 11.52/2.01  
% 11.52/2.01  fof(f77,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.52/2.01    inference(definition_unfolding,[],[f52,f73])).
% 11.52/2.01  
% 11.52/2.01  fof(f69,plain,(
% 11.52/2.01    r1_tarski(sK0,k1_relat_1(sK2))),
% 11.52/2.01    inference(cnf_transformation,[],[f44])).
% 11.52/2.01  
% 11.52/2.01  fof(f3,axiom,(
% 11.52/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f20,plain,(
% 11.52/2.01    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 11.52/2.01    inference(ennf_transformation,[],[f3])).
% 11.52/2.01  
% 11.52/2.01  fof(f49,plain,(
% 11.52/2.01    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f20])).
% 11.52/2.01  
% 11.52/2.01  fof(f75,plain,(
% 11.52/2.01    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 11.52/2.01    inference(definition_unfolding,[],[f49,f73])).
% 11.52/2.01  
% 11.52/2.01  fof(f4,axiom,(
% 11.52/2.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f50,plain,(
% 11.52/2.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f4])).
% 11.52/2.01  
% 11.52/2.01  fof(f76,plain,(
% 11.52/2.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 11.52/2.01    inference(definition_unfolding,[],[f50,f73])).
% 11.52/2.01  
% 11.52/2.01  fof(f17,axiom,(
% 11.52/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f37,plain,(
% 11.52/2.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.52/2.01    inference(ennf_transformation,[],[f17])).
% 11.52/2.01  
% 11.52/2.01  fof(f38,plain,(
% 11.52/2.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.52/2.01    inference(flattening,[],[f37])).
% 11.52/2.01  
% 11.52/2.01  fof(f65,plain,(
% 11.52/2.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f38])).
% 11.52/2.01  
% 11.52/2.01  fof(f14,axiom,(
% 11.52/2.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f31,plain,(
% 11.52/2.01    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.52/2.01    inference(ennf_transformation,[],[f14])).
% 11.52/2.01  
% 11.52/2.01  fof(f32,plain,(
% 11.52/2.01    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.52/2.01    inference(flattening,[],[f31])).
% 11.52/2.01  
% 11.52/2.01  fof(f61,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f32])).
% 11.52/2.01  
% 11.52/2.01  fof(f11,axiom,(
% 11.52/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f25,plain,(
% 11.52/2.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.52/2.01    inference(ennf_transformation,[],[f11])).
% 11.52/2.01  
% 11.52/2.01  fof(f26,plain,(
% 11.52/2.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.52/2.01    inference(flattening,[],[f25])).
% 11.52/2.01  
% 11.52/2.01  fof(f57,plain,(
% 11.52/2.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f26])).
% 11.52/2.01  
% 11.52/2.01  fof(f58,plain,(
% 11.52/2.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f26])).
% 11.52/2.01  
% 11.52/2.01  fof(f15,axiom,(
% 11.52/2.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f33,plain,(
% 11.52/2.01    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.52/2.01    inference(ennf_transformation,[],[f15])).
% 11.52/2.01  
% 11.52/2.01  fof(f34,plain,(
% 11.52/2.01    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.52/2.01    inference(flattening,[],[f33])).
% 11.52/2.01  
% 11.52/2.01  fof(f62,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f34])).
% 11.52/2.01  
% 11.52/2.01  fof(f16,axiom,(
% 11.52/2.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f35,plain,(
% 11.52/2.01    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.52/2.01    inference(ennf_transformation,[],[f16])).
% 11.52/2.01  
% 11.52/2.01  fof(f36,plain,(
% 11.52/2.01    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.52/2.01    inference(flattening,[],[f35])).
% 11.52/2.01  
% 11.52/2.01  fof(f63,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f36])).
% 11.52/2.01  
% 11.52/2.01  fof(f71,plain,(
% 11.52/2.01    ~r1_tarski(sK0,sK1)),
% 11.52/2.01    inference(cnf_transformation,[],[f44])).
% 11.52/2.01  
% 11.52/2.01  cnf(c_19,negated_conjecture,
% 11.52/2.01      ( v2_funct_1(sK2) ),
% 11.52/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_677,plain,
% 11.52/2.01      ( v2_funct_1(sK2) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_11,plain,
% 11.52/2.01      ( ~ v2_funct_1(X0)
% 11.52/2.01      | ~ v1_funct_1(X0)
% 11.52/2.01      | ~ v1_relat_1(X0)
% 11.52/2.01      | k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 11.52/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_685,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
% 11.52/2.01      | v2_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_3889,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
% 11.52/2.01      | v1_funct_1(sK2) != iProver_top
% 11.52/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_677,c_685]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_23,negated_conjecture,
% 11.52/2.01      ( v1_relat_1(sK2) ),
% 11.52/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_24,plain,
% 11.52/2.01      ( v1_relat_1(sK2) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_22,negated_conjecture,
% 11.52/2.01      ( v1_funct_1(sK2) ),
% 11.52/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_25,plain,
% 11.52/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_4392,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 11.52/2.01      inference(global_propositional_subsumption,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_3889,c_24,c_25]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_0,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 11.52/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_4407,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_4392,c_0]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_21,negated_conjecture,
% 11.52/2.01      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 11.52/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_675,plain,
% 11.52/2.01      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_7,plain,
% 11.52/2.01      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
% 11.52/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_689,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
% 11.52/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1488,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_675,c_689]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_5350,plain,
% 11.52/2.01      ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) = k9_relat_1(sK2,sK0) ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_4407,c_1488]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_20,negated_conjecture,
% 11.52/2.01      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 11.52/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_676,plain,
% 11.52/2.01      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_4,plain,
% 11.52/2.01      ( ~ r1_tarski(X0,X1)
% 11.52/2.01      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X2)),X1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_692,plain,
% 11.52/2.01      ( r1_tarski(X0,X1) != iProver_top
% 11.52/2.01      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X2)),X1) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2158,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
% 11.52/2.01      | r1_tarski(X0,X2) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_692,c_689]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_7383,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_relat_1(sK2))) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)) ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_676,c_2158]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_5,plain,
% 11.52/2.01      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 11.52/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_691,plain,
% 11.52/2.01      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1193,plain,
% 11.52/2.01      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_0,c_691]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_7791,plain,
% 11.52/2.01      ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_relat_1(sK2)) = iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_7383,c_1193]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_8107,plain,
% 11.52/2.01      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,sK0)),k1_relat_1(sK2)) = iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_0,c_7791]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_16,plain,
% 11.52/2.01      ( ~ v2_funct_1(X0)
% 11.52/2.01      | ~ v1_funct_1(X0)
% 11.52/2.01      | ~ v1_relat_1(X0)
% 11.52/2.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.52/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_680,plain,
% 11.52/2.01      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.52/2.01      | v2_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2174,plain,
% 11.52/2.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.52/2.01      | v1_funct_1(sK2) != iProver_top
% 11.52/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_677,c_680]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_34,plain,
% 11.52/2.01      ( ~ v2_funct_1(sK2)
% 11.52/2.01      | ~ v1_funct_1(sK2)
% 11.52/2.01      | ~ v1_relat_1(sK2)
% 11.52/2.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_16]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2802,plain,
% 11.52/2.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.52/2.01      inference(global_propositional_subsumption,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_2174,c_23,c_22,c_19,c_34]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_13,plain,
% 11.52/2.01      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 11.52/2.01      | ~ v1_funct_1(X1)
% 11.52/2.01      | ~ v1_relat_1(X1)
% 11.52/2.01      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 11.52/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_683,plain,
% 11.52/2.01      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 11.52/2.01      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 11.52/2.01      | v1_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_3825,plain,
% 11.52/2.01      ( k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X0)) = X0
% 11.52/2.01      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 11.52/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.52/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_2802,c_683]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_10,plain,
% 11.52/2.01      ( ~ v1_funct_1(X0)
% 11.52/2.01      | ~ v1_relat_1(X0)
% 11.52/2.01      | v1_relat_1(k2_funct_1(X0)) ),
% 11.52/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_51,plain,
% 11.52/2.01      ( v1_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_relat_1(X0) != iProver_top
% 11.52/2.01      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_53,plain,
% 11.52/2.01      ( v1_funct_1(sK2) != iProver_top
% 11.52/2.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.52/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_51]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_9,plain,
% 11.52/2.01      ( ~ v1_funct_1(X0)
% 11.52/2.01      | v1_funct_1(k2_funct_1(X0))
% 11.52/2.01      | ~ v1_relat_1(X0) ),
% 11.52/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_54,plain,
% 11.52/2.01      ( v1_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 11.52/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_56,plain,
% 11.52/2.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.52/2.01      | v1_funct_1(sK2) != iProver_top
% 11.52/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_54]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_31366,plain,
% 11.52/2.01      ( k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X0)) = X0
% 11.52/2.01      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 11.52/2.01      inference(global_propositional_subsumption,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_3825,c_24,c_25,c_53,c_56]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_14,plain,
% 11.52/2.01      ( ~ v2_funct_1(X0)
% 11.52/2.01      | ~ v1_funct_1(X0)
% 11.52/2.01      | ~ v1_relat_1(X0)
% 11.52/2.01      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_682,plain,
% 11.52/2.01      ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 11.52/2.01      | v2_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_3649,plain,
% 11.52/2.01      ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0)
% 11.52/2.01      | v1_funct_1(sK2) != iProver_top
% 11.52/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_677,c_682]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_4382,plain,
% 11.52/2.01      ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
% 11.52/2.01      inference(global_propositional_subsumption,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_3649,c_24,c_25]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_31372,plain,
% 11.52/2.01      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
% 11.52/2.01      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 11.52/2.01      inference(light_normalisation,[status(thm)],[c_31366,c_4382]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_15,plain,
% 11.52/2.01      ( ~ v2_funct_1(X0)
% 11.52/2.01      | ~ v1_funct_1(X0)
% 11.52/2.01      | ~ v1_relat_1(X0)
% 11.52/2.01      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_681,plain,
% 11.52/2.01      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 11.52/2.01      | v2_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_funct_1(X0) != iProver_top
% 11.52/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_3640,plain,
% 11.52/2.01      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 11.52/2.01      | v1_funct_1(sK2) != iProver_top
% 11.52/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_677,c_681]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_4091,plain,
% 11.52/2.01      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 11.52/2.01      inference(global_propositional_subsumption,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_3640,c_24,c_25]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_31373,plain,
% 11.52/2.01      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 11.52/2.01      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 11.52/2.01      inference(demodulation,[status(thm)],[c_31372,c_4091]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_31385,plain,
% 11.52/2.01      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,sK0)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK0)) ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_8107,c_31373]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_33778,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_5350,c_31385]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_31382,plain,
% 11.52/2.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_676,c_31373]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_33798,plain,
% 11.52/2.01      ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)) = sK0 ),
% 11.52/2.01      inference(light_normalisation,[status(thm)],[c_33778,c_31382]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_35503,plain,
% 11.52/2.01      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_33798,c_691]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_18,negated_conjecture,
% 11.52/2.01      ( ~ r1_tarski(sK0,sK1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_29,plain,
% 11.52/2.01      ( r1_tarski(sK0,sK1) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(contradiction,plain,
% 11.52/2.01      ( $false ),
% 11.52/2.01      inference(minisat,[status(thm)],[c_35503,c_29]) ).
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.52/2.01  
% 11.52/2.01  ------                               Statistics
% 11.52/2.01  
% 11.52/2.01  ------ Selected
% 11.52/2.01  
% 11.52/2.01  total_time:                             1.248
% 11.52/2.01  
%------------------------------------------------------------------------------
