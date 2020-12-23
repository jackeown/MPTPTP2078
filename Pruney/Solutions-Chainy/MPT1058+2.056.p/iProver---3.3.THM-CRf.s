%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:21 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 935 expanded)
%              Number of clauses        :   58 ( 289 expanded)
%              Number of leaves         :   21 ( 233 expanded)
%              Depth                    :   21
%              Number of atoms          :  218 (1489 expanded)
%              Number of equality atoms :  136 ( 947 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40])).

fof(f70,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

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
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f64,f77])).

fof(f21,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f68,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1051,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1057,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3821,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1057])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3932,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3821,c_35])).

cnf(c_3933,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3932])).

cnf(c_3940,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1051,c_3933])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1064,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3938,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_1064,c_3933])).

cnf(c_1055,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1060,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2424,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1055,c_1060])).

cnf(c_9943,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_3938,c_2424])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9948,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9943,c_8])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1054,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1510,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_17,c_8])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1058,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2280,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_1055,c_1058])).

cnf(c_3015,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1054,c_1510,c_2280,c_2424])).

cnf(c_3019,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(superposition,[status(thm)],[c_1055,c_3015])).

cnf(c_12,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1056,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1053,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2119,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(X0,k1_relat_1(X0))),k6_relat_1(X1))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1053,c_1510])).

cnf(c_2123,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_2119])).

cnf(c_2129,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X0)),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2123,c_9])).

cnf(c_3962,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X0)),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2129,c_35])).

cnf(c_3965,plain,
    ( k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_3962,c_2280,c_2424,c_3019,c_3938])).

cnf(c_9962,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_9948,c_3965])).

cnf(c_15621,plain,
    ( k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_3019,c_9962])).

cnf(c_15625,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_9948,c_15621])).

cnf(c_21017,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_3940,c_15625])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1049,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3020,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_1049,c_3015])).

cnf(c_10000,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = k10_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_9948,c_3020])).

cnf(c_3969,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X1)),X1)) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_3020,c_3965])).

cnf(c_10002,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0)) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) ),
    inference(superposition,[status(thm)],[c_9948,c_3969])).

cnf(c_10003,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,X0)) = k10_relat_1(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_10000,c_10002])).

cnf(c_21042,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_21017,c_3020,c_10003])).

cnf(c_749,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1175,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_750,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1089,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
    | k10_relat_1(sK0,sK2) != X0
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_1118,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_18,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21042,c_1175,c_1118,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.80/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.49  
% 7.80/1.49  ------  iProver source info
% 7.80/1.49  
% 7.80/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.49  git: non_committed_changes: false
% 7.80/1.49  git: last_make_outside_of_git: false
% 7.80/1.49  
% 7.80/1.49  ------ 
% 7.80/1.49  
% 7.80/1.49  ------ Input Options
% 7.80/1.49  
% 7.80/1.49  --out_options                           all
% 7.80/1.49  --tptp_safe_out                         true
% 7.80/1.49  --problem_path                          ""
% 7.80/1.49  --include_path                          ""
% 7.80/1.49  --clausifier                            res/vclausify_rel
% 7.80/1.49  --clausifier_options                    ""
% 7.80/1.49  --stdin                                 false
% 7.80/1.49  --stats_out                             all
% 7.80/1.49  
% 7.80/1.49  ------ General Options
% 7.80/1.49  
% 7.80/1.49  --fof                                   false
% 7.80/1.49  --time_out_real                         305.
% 7.80/1.49  --time_out_virtual                      -1.
% 7.80/1.49  --symbol_type_check                     false
% 7.80/1.49  --clausify_out                          false
% 7.80/1.49  --sig_cnt_out                           false
% 7.80/1.49  --trig_cnt_out                          false
% 7.80/1.49  --trig_cnt_out_tolerance                1.
% 7.80/1.49  --trig_cnt_out_sk_spl                   false
% 7.80/1.49  --abstr_cl_out                          false
% 7.80/1.49  
% 7.80/1.49  ------ Global Options
% 7.80/1.49  
% 7.80/1.49  --schedule                              default
% 7.80/1.49  --add_important_lit                     false
% 7.80/1.49  --prop_solver_per_cl                    1000
% 7.80/1.49  --min_unsat_core                        false
% 7.80/1.49  --soft_assumptions                      false
% 7.80/1.49  --soft_lemma_size                       3
% 7.80/1.49  --prop_impl_unit_size                   0
% 7.80/1.49  --prop_impl_unit                        []
% 7.80/1.49  --share_sel_clauses                     true
% 7.80/1.49  --reset_solvers                         false
% 7.80/1.49  --bc_imp_inh                            [conj_cone]
% 7.80/1.49  --conj_cone_tolerance                   3.
% 7.80/1.49  --extra_neg_conj                        none
% 7.80/1.49  --large_theory_mode                     true
% 7.80/1.49  --prolific_symb_bound                   200
% 7.80/1.49  --lt_threshold                          2000
% 7.80/1.49  --clause_weak_htbl                      true
% 7.80/1.49  --gc_record_bc_elim                     false
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing Options
% 7.80/1.49  
% 7.80/1.49  --preprocessing_flag                    true
% 7.80/1.49  --time_out_prep_mult                    0.1
% 7.80/1.49  --splitting_mode                        input
% 7.80/1.49  --splitting_grd                         true
% 7.80/1.49  --splitting_cvd                         false
% 7.80/1.49  --splitting_cvd_svl                     false
% 7.80/1.49  --splitting_nvd                         32
% 7.80/1.49  --sub_typing                            true
% 7.80/1.49  --prep_gs_sim                           true
% 7.80/1.49  --prep_unflatten                        true
% 7.80/1.49  --prep_res_sim                          true
% 7.80/1.49  --prep_upred                            true
% 7.80/1.49  --prep_sem_filter                       exhaustive
% 7.80/1.49  --prep_sem_filter_out                   false
% 7.80/1.49  --pred_elim                             true
% 7.80/1.49  --res_sim_input                         true
% 7.80/1.49  --eq_ax_congr_red                       true
% 7.80/1.49  --pure_diseq_elim                       true
% 7.80/1.49  --brand_transform                       false
% 7.80/1.49  --non_eq_to_eq                          false
% 7.80/1.49  --prep_def_merge                        true
% 7.80/1.49  --prep_def_merge_prop_impl              false
% 7.80/1.49  --prep_def_merge_mbd                    true
% 7.80/1.49  --prep_def_merge_tr_red                 false
% 7.80/1.49  --prep_def_merge_tr_cl                  false
% 7.80/1.49  --smt_preprocessing                     true
% 7.80/1.49  --smt_ac_axioms                         fast
% 7.80/1.49  --preprocessed_out                      false
% 7.80/1.49  --preprocessed_stats                    false
% 7.80/1.49  
% 7.80/1.49  ------ Abstraction refinement Options
% 7.80/1.49  
% 7.80/1.49  --abstr_ref                             []
% 7.80/1.49  --abstr_ref_prep                        false
% 7.80/1.49  --abstr_ref_until_sat                   false
% 7.80/1.49  --abstr_ref_sig_restrict                funpre
% 7.80/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.49  --abstr_ref_under                       []
% 7.80/1.49  
% 7.80/1.49  ------ SAT Options
% 7.80/1.49  
% 7.80/1.49  --sat_mode                              false
% 7.80/1.49  --sat_fm_restart_options                ""
% 7.80/1.49  --sat_gr_def                            false
% 7.80/1.49  --sat_epr_types                         true
% 7.80/1.49  --sat_non_cyclic_types                  false
% 7.80/1.49  --sat_finite_models                     false
% 7.80/1.49  --sat_fm_lemmas                         false
% 7.80/1.49  --sat_fm_prep                           false
% 7.80/1.49  --sat_fm_uc_incr                        true
% 7.80/1.49  --sat_out_model                         small
% 7.80/1.49  --sat_out_clauses                       false
% 7.80/1.49  
% 7.80/1.49  ------ QBF Options
% 7.80/1.49  
% 7.80/1.49  --qbf_mode                              false
% 7.80/1.49  --qbf_elim_univ                         false
% 7.80/1.49  --qbf_dom_inst                          none
% 7.80/1.49  --qbf_dom_pre_inst                      false
% 7.80/1.49  --qbf_sk_in                             false
% 7.80/1.49  --qbf_pred_elim                         true
% 7.80/1.49  --qbf_split                             512
% 7.80/1.49  
% 7.80/1.49  ------ BMC1 Options
% 7.80/1.49  
% 7.80/1.49  --bmc1_incremental                      false
% 7.80/1.49  --bmc1_axioms                           reachable_all
% 7.80/1.49  --bmc1_min_bound                        0
% 7.80/1.49  --bmc1_max_bound                        -1
% 7.80/1.49  --bmc1_max_bound_default                -1
% 7.80/1.49  --bmc1_symbol_reachability              true
% 7.80/1.49  --bmc1_property_lemmas                  false
% 7.80/1.49  --bmc1_k_induction                      false
% 7.80/1.49  --bmc1_non_equiv_states                 false
% 7.80/1.49  --bmc1_deadlock                         false
% 7.80/1.49  --bmc1_ucm                              false
% 7.80/1.49  --bmc1_add_unsat_core                   none
% 7.80/1.49  --bmc1_unsat_core_children              false
% 7.80/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.49  --bmc1_out_stat                         full
% 7.80/1.49  --bmc1_ground_init                      false
% 7.80/1.49  --bmc1_pre_inst_next_state              false
% 7.80/1.49  --bmc1_pre_inst_state                   false
% 7.80/1.49  --bmc1_pre_inst_reach_state             false
% 7.80/1.49  --bmc1_out_unsat_core                   false
% 7.80/1.49  --bmc1_aig_witness_out                  false
% 7.80/1.49  --bmc1_verbose                          false
% 7.80/1.49  --bmc1_dump_clauses_tptp                false
% 7.80/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.49  --bmc1_dump_file                        -
% 7.80/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.49  --bmc1_ucm_extend_mode                  1
% 7.80/1.49  --bmc1_ucm_init_mode                    2
% 7.80/1.49  --bmc1_ucm_cone_mode                    none
% 7.80/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.49  --bmc1_ucm_relax_model                  4
% 7.80/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.49  --bmc1_ucm_layered_model                none
% 7.80/1.49  --bmc1_ucm_max_lemma_size               10
% 7.80/1.49  
% 7.80/1.49  ------ AIG Options
% 7.80/1.49  
% 7.80/1.49  --aig_mode                              false
% 7.80/1.49  
% 7.80/1.49  ------ Instantiation Options
% 7.80/1.49  
% 7.80/1.49  --instantiation_flag                    true
% 7.80/1.49  --inst_sos_flag                         true
% 7.80/1.49  --inst_sos_phase                        true
% 7.80/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.49  --inst_lit_sel_side                     num_symb
% 7.80/1.49  --inst_solver_per_active                1400
% 7.80/1.49  --inst_solver_calls_frac                1.
% 7.80/1.49  --inst_passive_queue_type               priority_queues
% 7.80/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.49  --inst_passive_queues_freq              [25;2]
% 7.80/1.49  --inst_dismatching                      true
% 7.80/1.49  --inst_eager_unprocessed_to_passive     true
% 7.80/1.49  --inst_prop_sim_given                   true
% 7.80/1.49  --inst_prop_sim_new                     false
% 7.80/1.49  --inst_subs_new                         false
% 7.80/1.49  --inst_eq_res_simp                      false
% 7.80/1.49  --inst_subs_given                       false
% 7.80/1.49  --inst_orphan_elimination               true
% 7.80/1.49  --inst_learning_loop_flag               true
% 7.80/1.49  --inst_learning_start                   3000
% 7.80/1.49  --inst_learning_factor                  2
% 7.80/1.49  --inst_start_prop_sim_after_learn       3
% 7.80/1.49  --inst_sel_renew                        solver
% 7.80/1.49  --inst_lit_activity_flag                true
% 7.80/1.49  --inst_restr_to_given                   false
% 7.80/1.49  --inst_activity_threshold               500
% 7.80/1.49  --inst_out_proof                        true
% 7.80/1.49  
% 7.80/1.49  ------ Resolution Options
% 7.80/1.49  
% 7.80/1.49  --resolution_flag                       true
% 7.80/1.49  --res_lit_sel                           adaptive
% 7.80/1.49  --res_lit_sel_side                      none
% 7.80/1.49  --res_ordering                          kbo
% 7.80/1.49  --res_to_prop_solver                    active
% 7.80/1.49  --res_prop_simpl_new                    false
% 7.80/1.49  --res_prop_simpl_given                  true
% 7.80/1.49  --res_passive_queue_type                priority_queues
% 7.80/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.49  --res_passive_queues_freq               [15;5]
% 7.80/1.49  --res_forward_subs                      full
% 7.80/1.49  --res_backward_subs                     full
% 7.80/1.49  --res_forward_subs_resolution           true
% 7.80/1.49  --res_backward_subs_resolution          true
% 7.80/1.49  --res_orphan_elimination                true
% 7.80/1.49  --res_time_limit                        2.
% 7.80/1.49  --res_out_proof                         true
% 7.80/1.49  
% 7.80/1.49  ------ Superposition Options
% 7.80/1.49  
% 7.80/1.49  --superposition_flag                    true
% 7.80/1.49  --sup_passive_queue_type                priority_queues
% 7.80/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.49  --demod_completeness_check              fast
% 7.80/1.49  --demod_use_ground                      true
% 7.80/1.49  --sup_to_prop_solver                    passive
% 7.80/1.49  --sup_prop_simpl_new                    true
% 7.80/1.49  --sup_prop_simpl_given                  true
% 7.80/1.49  --sup_fun_splitting                     true
% 7.80/1.49  --sup_smt_interval                      50000
% 7.80/1.49  
% 7.80/1.49  ------ Superposition Simplification Setup
% 7.80/1.49  
% 7.80/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.80/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.80/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.80/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.80/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.80/1.49  --sup_immed_triv                        [TrivRules]
% 7.80/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_immed_bw_main                     []
% 7.80/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.80/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_input_bw                          []
% 7.80/1.49  
% 7.80/1.49  ------ Combination Options
% 7.80/1.49  
% 7.80/1.49  --comb_res_mult                         3
% 7.80/1.49  --comb_sup_mult                         2
% 7.80/1.49  --comb_inst_mult                        10
% 7.80/1.49  
% 7.80/1.49  ------ Debug Options
% 7.80/1.49  
% 7.80/1.49  --dbg_backtrace                         false
% 7.80/1.49  --dbg_dump_prop_clauses                 false
% 7.80/1.49  --dbg_dump_prop_clauses_file            -
% 7.80/1.49  --dbg_out_stat                          false
% 7.80/1.49  ------ Parsing...
% 7.80/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  ------ Proving...
% 7.80/1.49  ------ Problem Properties 
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  clauses                                 21
% 7.80/1.49  conjectures                             4
% 7.80/1.49  EPR                                     4
% 7.80/1.49  Horn                                    21
% 7.80/1.49  unary                                   11
% 7.80/1.49  binary                                  6
% 7.80/1.49  lits                                    37
% 7.80/1.49  lits eq                                 11
% 7.80/1.49  fd_pure                                 0
% 7.80/1.49  fd_pseudo                               0
% 7.80/1.49  fd_cond                                 0
% 7.80/1.49  fd_pseudo_cond                          1
% 7.80/1.49  AC symbols                              0
% 7.80/1.49  
% 7.80/1.49  ------ Schedule dynamic 5 is on 
% 7.80/1.49  
% 7.80/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ 
% 7.80/1.49  Current options:
% 7.80/1.49  ------ 
% 7.80/1.49  
% 7.80/1.49  ------ Input Options
% 7.80/1.49  
% 7.80/1.49  --out_options                           all
% 7.80/1.49  --tptp_safe_out                         true
% 7.80/1.49  --problem_path                          ""
% 7.80/1.49  --include_path                          ""
% 7.80/1.49  --clausifier                            res/vclausify_rel
% 7.80/1.49  --clausifier_options                    ""
% 7.80/1.49  --stdin                                 false
% 7.80/1.49  --stats_out                             all
% 7.80/1.49  
% 7.80/1.49  ------ General Options
% 7.80/1.49  
% 7.80/1.49  --fof                                   false
% 7.80/1.49  --time_out_real                         305.
% 7.80/1.49  --time_out_virtual                      -1.
% 7.80/1.49  --symbol_type_check                     false
% 7.80/1.49  --clausify_out                          false
% 7.80/1.49  --sig_cnt_out                           false
% 7.80/1.49  --trig_cnt_out                          false
% 7.80/1.49  --trig_cnt_out_tolerance                1.
% 7.80/1.49  --trig_cnt_out_sk_spl                   false
% 7.80/1.49  --abstr_cl_out                          false
% 7.80/1.49  
% 7.80/1.49  ------ Global Options
% 7.80/1.49  
% 7.80/1.49  --schedule                              default
% 7.80/1.49  --add_important_lit                     false
% 7.80/1.49  --prop_solver_per_cl                    1000
% 7.80/1.49  --min_unsat_core                        false
% 7.80/1.49  --soft_assumptions                      false
% 7.80/1.49  --soft_lemma_size                       3
% 7.80/1.49  --prop_impl_unit_size                   0
% 7.80/1.49  --prop_impl_unit                        []
% 7.80/1.49  --share_sel_clauses                     true
% 7.80/1.49  --reset_solvers                         false
% 7.80/1.49  --bc_imp_inh                            [conj_cone]
% 7.80/1.49  --conj_cone_tolerance                   3.
% 7.80/1.49  --extra_neg_conj                        none
% 7.80/1.49  --large_theory_mode                     true
% 7.80/1.49  --prolific_symb_bound                   200
% 7.80/1.50  --lt_threshold                          2000
% 7.80/1.50  --clause_weak_htbl                      true
% 7.80/1.50  --gc_record_bc_elim                     false
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing Options
% 7.80/1.50  
% 7.80/1.50  --preprocessing_flag                    true
% 7.80/1.50  --time_out_prep_mult                    0.1
% 7.80/1.50  --splitting_mode                        input
% 7.80/1.50  --splitting_grd                         true
% 7.80/1.50  --splitting_cvd                         false
% 7.80/1.50  --splitting_cvd_svl                     false
% 7.80/1.50  --splitting_nvd                         32
% 7.80/1.50  --sub_typing                            true
% 7.80/1.50  --prep_gs_sim                           true
% 7.80/1.50  --prep_unflatten                        true
% 7.80/1.50  --prep_res_sim                          true
% 7.80/1.50  --prep_upred                            true
% 7.80/1.50  --prep_sem_filter                       exhaustive
% 7.80/1.50  --prep_sem_filter_out                   false
% 7.80/1.50  --pred_elim                             true
% 7.80/1.50  --res_sim_input                         true
% 7.80/1.50  --eq_ax_congr_red                       true
% 7.80/1.50  --pure_diseq_elim                       true
% 7.80/1.50  --brand_transform                       false
% 7.80/1.50  --non_eq_to_eq                          false
% 7.80/1.50  --prep_def_merge                        true
% 7.80/1.50  --prep_def_merge_prop_impl              false
% 7.80/1.50  --prep_def_merge_mbd                    true
% 7.80/1.50  --prep_def_merge_tr_red                 false
% 7.80/1.50  --prep_def_merge_tr_cl                  false
% 7.80/1.50  --smt_preprocessing                     true
% 7.80/1.50  --smt_ac_axioms                         fast
% 7.80/1.50  --preprocessed_out                      false
% 7.80/1.50  --preprocessed_stats                    false
% 7.80/1.50  
% 7.80/1.50  ------ Abstraction refinement Options
% 7.80/1.50  
% 7.80/1.50  --abstr_ref                             []
% 7.80/1.50  --abstr_ref_prep                        false
% 7.80/1.50  --abstr_ref_until_sat                   false
% 7.80/1.50  --abstr_ref_sig_restrict                funpre
% 7.80/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.50  --abstr_ref_under                       []
% 7.80/1.50  
% 7.80/1.50  ------ SAT Options
% 7.80/1.50  
% 7.80/1.50  --sat_mode                              false
% 7.80/1.50  --sat_fm_restart_options                ""
% 7.80/1.50  --sat_gr_def                            false
% 7.80/1.50  --sat_epr_types                         true
% 7.80/1.50  --sat_non_cyclic_types                  false
% 7.80/1.50  --sat_finite_models                     false
% 7.80/1.50  --sat_fm_lemmas                         false
% 7.80/1.50  --sat_fm_prep                           false
% 7.80/1.50  --sat_fm_uc_incr                        true
% 7.80/1.50  --sat_out_model                         small
% 7.80/1.50  --sat_out_clauses                       false
% 7.80/1.50  
% 7.80/1.50  ------ QBF Options
% 7.80/1.50  
% 7.80/1.50  --qbf_mode                              false
% 7.80/1.50  --qbf_elim_univ                         false
% 7.80/1.50  --qbf_dom_inst                          none
% 7.80/1.50  --qbf_dom_pre_inst                      false
% 7.80/1.50  --qbf_sk_in                             false
% 7.80/1.50  --qbf_pred_elim                         true
% 7.80/1.50  --qbf_split                             512
% 7.80/1.50  
% 7.80/1.50  ------ BMC1 Options
% 7.80/1.50  
% 7.80/1.50  --bmc1_incremental                      false
% 7.80/1.50  --bmc1_axioms                           reachable_all
% 7.80/1.50  --bmc1_min_bound                        0
% 7.80/1.50  --bmc1_max_bound                        -1
% 7.80/1.50  --bmc1_max_bound_default                -1
% 7.80/1.50  --bmc1_symbol_reachability              true
% 7.80/1.50  --bmc1_property_lemmas                  false
% 7.80/1.50  --bmc1_k_induction                      false
% 7.80/1.50  --bmc1_non_equiv_states                 false
% 7.80/1.50  --bmc1_deadlock                         false
% 7.80/1.50  --bmc1_ucm                              false
% 7.80/1.50  --bmc1_add_unsat_core                   none
% 7.80/1.50  --bmc1_unsat_core_children              false
% 7.80/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.50  --bmc1_out_stat                         full
% 7.80/1.50  --bmc1_ground_init                      false
% 7.80/1.50  --bmc1_pre_inst_next_state              false
% 7.80/1.50  --bmc1_pre_inst_state                   false
% 7.80/1.50  --bmc1_pre_inst_reach_state             false
% 7.80/1.50  --bmc1_out_unsat_core                   false
% 7.80/1.50  --bmc1_aig_witness_out                  false
% 7.80/1.50  --bmc1_verbose                          false
% 7.80/1.50  --bmc1_dump_clauses_tptp                false
% 7.80/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.50  --bmc1_dump_file                        -
% 7.80/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.50  --bmc1_ucm_extend_mode                  1
% 7.80/1.50  --bmc1_ucm_init_mode                    2
% 7.80/1.50  --bmc1_ucm_cone_mode                    none
% 7.80/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.50  --bmc1_ucm_relax_model                  4
% 7.80/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.50  --bmc1_ucm_layered_model                none
% 7.80/1.50  --bmc1_ucm_max_lemma_size               10
% 7.80/1.50  
% 7.80/1.50  ------ AIG Options
% 7.80/1.50  
% 7.80/1.50  --aig_mode                              false
% 7.80/1.50  
% 7.80/1.50  ------ Instantiation Options
% 7.80/1.50  
% 7.80/1.50  --instantiation_flag                    true
% 7.80/1.50  --inst_sos_flag                         true
% 7.80/1.50  --inst_sos_phase                        true
% 7.80/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.50  --inst_lit_sel_side                     none
% 7.80/1.50  --inst_solver_per_active                1400
% 7.80/1.50  --inst_solver_calls_frac                1.
% 7.80/1.50  --inst_passive_queue_type               priority_queues
% 7.80/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.50  --inst_passive_queues_freq              [25;2]
% 7.80/1.50  --inst_dismatching                      true
% 7.80/1.50  --inst_eager_unprocessed_to_passive     true
% 7.80/1.50  --inst_prop_sim_given                   true
% 7.80/1.50  --inst_prop_sim_new                     false
% 7.80/1.50  --inst_subs_new                         false
% 7.80/1.50  --inst_eq_res_simp                      false
% 7.80/1.50  --inst_subs_given                       false
% 7.80/1.50  --inst_orphan_elimination               true
% 7.80/1.50  --inst_learning_loop_flag               true
% 7.80/1.50  --inst_learning_start                   3000
% 7.80/1.50  --inst_learning_factor                  2
% 7.80/1.50  --inst_start_prop_sim_after_learn       3
% 7.80/1.50  --inst_sel_renew                        solver
% 7.80/1.50  --inst_lit_activity_flag                true
% 7.80/1.50  --inst_restr_to_given                   false
% 7.80/1.50  --inst_activity_threshold               500
% 7.80/1.50  --inst_out_proof                        true
% 7.80/1.50  
% 7.80/1.50  ------ Resolution Options
% 7.80/1.50  
% 7.80/1.50  --resolution_flag                       false
% 7.80/1.50  --res_lit_sel                           adaptive
% 7.80/1.50  --res_lit_sel_side                      none
% 7.80/1.50  --res_ordering                          kbo
% 7.80/1.50  --res_to_prop_solver                    active
% 7.80/1.50  --res_prop_simpl_new                    false
% 7.80/1.50  --res_prop_simpl_given                  true
% 7.80/1.50  --res_passive_queue_type                priority_queues
% 7.80/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.50  --res_passive_queues_freq               [15;5]
% 7.80/1.50  --res_forward_subs                      full
% 7.80/1.50  --res_backward_subs                     full
% 7.80/1.50  --res_forward_subs_resolution           true
% 7.80/1.50  --res_backward_subs_resolution          true
% 7.80/1.50  --res_orphan_elimination                true
% 7.80/1.50  --res_time_limit                        2.
% 7.80/1.50  --res_out_proof                         true
% 7.80/1.50  
% 7.80/1.50  ------ Superposition Options
% 7.80/1.50  
% 7.80/1.50  --superposition_flag                    true
% 7.80/1.50  --sup_passive_queue_type                priority_queues
% 7.80/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.50  --demod_completeness_check              fast
% 7.80/1.50  --demod_use_ground                      true
% 7.80/1.50  --sup_to_prop_solver                    passive
% 7.80/1.50  --sup_prop_simpl_new                    true
% 7.80/1.50  --sup_prop_simpl_given                  true
% 7.80/1.50  --sup_fun_splitting                     true
% 7.80/1.50  --sup_smt_interval                      50000
% 7.80/1.50  
% 7.80/1.50  ------ Superposition Simplification Setup
% 7.80/1.50  
% 7.80/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.80/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.80/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.80/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.80/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.80/1.50  --sup_immed_triv                        [TrivRules]
% 7.80/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.50  --sup_immed_bw_main                     []
% 7.80/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.80/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.50  --sup_input_bw                          []
% 7.80/1.50  
% 7.80/1.50  ------ Combination Options
% 7.80/1.50  
% 7.80/1.50  --comb_res_mult                         3
% 7.80/1.50  --comb_sup_mult                         2
% 7.80/1.50  --comb_inst_mult                        10
% 7.80/1.50  
% 7.80/1.50  ------ Debug Options
% 7.80/1.50  
% 7.80/1.50  --dbg_backtrace                         false
% 7.80/1.50  --dbg_dump_prop_clauses                 false
% 7.80/1.50  --dbg_dump_prop_clauses_file            -
% 7.80/1.50  --dbg_out_stat                          false
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  % SZS status Theorem for theBenchmark.p
% 7.80/1.50  
% 7.80/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.50  
% 7.80/1.50  fof(f22,conjecture,(
% 7.80/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f23,negated_conjecture,(
% 7.80/1.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.80/1.50    inference(negated_conjecture,[],[f22])).
% 7.80/1.50  
% 7.80/1.50  fof(f36,plain,(
% 7.80/1.50    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.80/1.50    inference(ennf_transformation,[],[f23])).
% 7.80/1.50  
% 7.80/1.50  fof(f37,plain,(
% 7.80/1.50    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.80/1.50    inference(flattening,[],[f36])).
% 7.80/1.50  
% 7.80/1.50  fof(f41,plain,(
% 7.80/1.50    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 7.80/1.50    introduced(choice_axiom,[])).
% 7.80/1.50  
% 7.80/1.50  fof(f40,plain,(
% 7.80/1.50    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 7.80/1.50    introduced(choice_axiom,[])).
% 7.80/1.50  
% 7.80/1.50  fof(f42,plain,(
% 7.80/1.50    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 7.80/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40])).
% 7.80/1.50  
% 7.80/1.50  fof(f70,plain,(
% 7.80/1.50    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 7.80/1.50    inference(cnf_transformation,[],[f42])).
% 7.80/1.50  
% 7.80/1.50  fof(f14,axiom,(
% 7.80/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f58,plain,(
% 7.80/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.80/1.50    inference(cnf_transformation,[],[f14])).
% 7.80/1.50  
% 7.80/1.50  fof(f16,axiom,(
% 7.80/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f29,plain,(
% 7.80/1.50    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.80/1.50    inference(ennf_transformation,[],[f16])).
% 7.80/1.50  
% 7.80/1.50  fof(f30,plain,(
% 7.80/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.80/1.50    inference(flattening,[],[f29])).
% 7.80/1.50  
% 7.80/1.50  fof(f61,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f30])).
% 7.80/1.50  
% 7.80/1.50  fof(f17,axiom,(
% 7.80/1.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f62,plain,(
% 7.80/1.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.80/1.50    inference(cnf_transformation,[],[f17])).
% 7.80/1.50  
% 7.80/1.50  fof(f1,axiom,(
% 7.80/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f38,plain,(
% 7.80/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.50    inference(nnf_transformation,[],[f1])).
% 7.80/1.50  
% 7.80/1.50  fof(f39,plain,(
% 7.80/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.50    inference(flattening,[],[f38])).
% 7.80/1.50  
% 7.80/1.50  fof(f44,plain,(
% 7.80/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.80/1.50    inference(cnf_transformation,[],[f39])).
% 7.80/1.50  
% 7.80/1.50  fof(f82,plain,(
% 7.80/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.80/1.50    inference(equality_resolution,[],[f44])).
% 7.80/1.50  
% 7.80/1.50  fof(f12,axiom,(
% 7.80/1.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f26,plain,(
% 7.80/1.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.80/1.50    inference(ennf_transformation,[],[f12])).
% 7.80/1.50  
% 7.80/1.50  fof(f56,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f26])).
% 7.80/1.50  
% 7.80/1.50  fof(f59,plain,(
% 7.80/1.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.80/1.50    inference(cnf_transformation,[],[f14])).
% 7.80/1.50  
% 7.80/1.50  fof(f18,axiom,(
% 7.80/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f31,plain,(
% 7.80/1.50    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.80/1.50    inference(ennf_transformation,[],[f18])).
% 7.80/1.50  
% 7.80/1.50  fof(f64,plain,(
% 7.80/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f31])).
% 7.80/1.50  
% 7.80/1.50  fof(f11,axiom,(
% 7.80/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f55,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.80/1.50    inference(cnf_transformation,[],[f11])).
% 7.80/1.50  
% 7.80/1.50  fof(f5,axiom,(
% 7.80/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f49,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f5])).
% 7.80/1.50  
% 7.80/1.50  fof(f6,axiom,(
% 7.80/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f50,plain,(
% 7.80/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f6])).
% 7.80/1.50  
% 7.80/1.50  fof(f7,axiom,(
% 7.80/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f51,plain,(
% 7.80/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f7])).
% 7.80/1.50  
% 7.80/1.50  fof(f8,axiom,(
% 7.80/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f52,plain,(
% 7.80/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f8])).
% 7.80/1.50  
% 7.80/1.50  fof(f9,axiom,(
% 7.80/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f53,plain,(
% 7.80/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f9])).
% 7.80/1.50  
% 7.80/1.50  fof(f10,axiom,(
% 7.80/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f54,plain,(
% 7.80/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f10])).
% 7.80/1.50  
% 7.80/1.50  fof(f72,plain,(
% 7.80/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.80/1.50    inference(definition_unfolding,[],[f53,f54])).
% 7.80/1.50  
% 7.80/1.50  fof(f73,plain,(
% 7.80/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.80/1.50    inference(definition_unfolding,[],[f52,f72])).
% 7.80/1.50  
% 7.80/1.50  fof(f74,plain,(
% 7.80/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.80/1.50    inference(definition_unfolding,[],[f51,f73])).
% 7.80/1.50  
% 7.80/1.50  fof(f75,plain,(
% 7.80/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.80/1.50    inference(definition_unfolding,[],[f50,f74])).
% 7.80/1.50  
% 7.80/1.50  fof(f76,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.80/1.50    inference(definition_unfolding,[],[f49,f75])).
% 7.80/1.50  
% 7.80/1.50  fof(f77,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.80/1.50    inference(definition_unfolding,[],[f55,f76])).
% 7.80/1.50  
% 7.80/1.50  fof(f79,plain,(
% 7.80/1.50    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.80/1.50    inference(definition_unfolding,[],[f64,f77])).
% 7.80/1.50  
% 7.80/1.50  fof(f21,axiom,(
% 7.80/1.50    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f67,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 7.80/1.50    inference(cnf_transformation,[],[f21])).
% 7.80/1.50  
% 7.80/1.50  fof(f81,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 7.80/1.50    inference(definition_unfolding,[],[f67,f77])).
% 7.80/1.50  
% 7.80/1.50  fof(f15,axiom,(
% 7.80/1.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f28,plain,(
% 7.80/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 7.80/1.50    inference(ennf_transformation,[],[f15])).
% 7.80/1.50  
% 7.80/1.50  fof(f60,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f28])).
% 7.80/1.50  
% 7.80/1.50  fof(f63,plain,(
% 7.80/1.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.80/1.50    inference(cnf_transformation,[],[f17])).
% 7.80/1.50  
% 7.80/1.50  fof(f19,axiom,(
% 7.80/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f32,plain,(
% 7.80/1.50    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.80/1.50    inference(ennf_transformation,[],[f19])).
% 7.80/1.50  
% 7.80/1.50  fof(f33,plain,(
% 7.80/1.50    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.80/1.50    inference(flattening,[],[f32])).
% 7.80/1.50  
% 7.80/1.50  fof(f65,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f33])).
% 7.80/1.50  
% 7.80/1.50  fof(f80,plain,(
% 7.80/1.50    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.80/1.50    inference(definition_unfolding,[],[f65,f77])).
% 7.80/1.50  
% 7.80/1.50  fof(f68,plain,(
% 7.80/1.50    v1_relat_1(sK0)),
% 7.80/1.50    inference(cnf_transformation,[],[f42])).
% 7.80/1.50  
% 7.80/1.50  fof(f71,plain,(
% 7.80/1.50    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 7.80/1.50    inference(cnf_transformation,[],[f42])).
% 7.80/1.50  
% 7.80/1.50  cnf(c_19,negated_conjecture,
% 7.80/1.50      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 7.80/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1051,plain,
% 7.80/1.50      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_9,plain,
% 7.80/1.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.80/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_11,plain,
% 7.80/1.50      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.80/1.50      | ~ v1_relat_1(X0)
% 7.80/1.50      | k7_relat_1(X0,X1) = X0 ),
% 7.80/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1057,plain,
% 7.80/1.50      ( k7_relat_1(X0,X1) = X0
% 7.80/1.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.80/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3821,plain,
% 7.80/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.80/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.80/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_9,c_1057]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_13,plain,
% 7.80/1.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.80/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_35,plain,
% 7.80/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3932,plain,
% 7.80/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.80/1.50      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 7.80/1.50      inference(global_propositional_subsumption,
% 7.80/1.50                [status(thm)],
% 7.80/1.50                [c_3821,c_35]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3933,plain,
% 7.80/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.80/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.80/1.50      inference(renaming,[status(thm)],[c_3932]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3940,plain,
% 7.80/1.50      ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_1051,c_3933]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1,plain,
% 7.80/1.50      ( r1_tarski(X0,X0) ),
% 7.80/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1064,plain,
% 7.80/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3938,plain,
% 7.80/1.50      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_1064,c_3933]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1055,plain,
% 7.80/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_6,plain,
% 7.80/1.50      ( ~ v1_relat_1(X0)
% 7.80/1.50      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.80/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1060,plain,
% 7.80/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.80/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_2424,plain,
% 7.80/1.50      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_1055,c_1060]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_9943,plain,
% 7.80/1.50      ( k9_relat_1(k6_relat_1(X0),X0) = k2_relat_1(k6_relat_1(X0)) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_3938,c_2424]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_8,plain,
% 7.80/1.50      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.80/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_9948,plain,
% 7.80/1.50      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 7.80/1.50      inference(light_normalisation,[status(thm)],[c_9943,c_8]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_14,plain,
% 7.80/1.50      ( ~ v1_relat_1(X0)
% 7.80/1.50      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.80/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1054,plain,
% 7.80/1.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.80/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_17,plain,
% 7.80/1.50      ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 7.80/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1510,plain,
% 7.80/1.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_17,c_8]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_10,plain,
% 7.80/1.50      ( ~ v1_relat_1(X0)
% 7.80/1.50      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.80/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1058,plain,
% 7.80/1.50      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.80/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_2280,plain,
% 7.80/1.50      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_1055,c_1058]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3015,plain,
% 7.80/1.50      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.80/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.80/1.50      inference(demodulation,[status(thm)],[c_1054,c_1510,c_2280,c_2424]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3019,plain,
% 7.80/1.50      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_1055,c_3015]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_12,plain,
% 7.80/1.50      ( v1_funct_1(k6_relat_1(X0)) ),
% 7.80/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1056,plain,
% 7.80/1.50      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_15,plain,
% 7.80/1.50      ( ~ v1_funct_1(X0)
% 7.80/1.50      | ~ v1_relat_1(X0)
% 7.80/1.50      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 7.80/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1053,plain,
% 7.80/1.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
% 7.80/1.50      | v1_funct_1(X1) != iProver_top
% 7.80/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_2119,plain,
% 7.80/1.50      ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(X0,k1_relat_1(X0))),k6_relat_1(X1))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 7.80/1.50      | v1_funct_1(X0) != iProver_top
% 7.80/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.80/1.50      inference(demodulation,[status(thm)],[c_1053,c_1510]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_2123,plain,
% 7.80/1.50      ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))
% 7.80/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_1056,c_2119]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_2129,plain,
% 7.80/1.50      ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X0)),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))
% 7.80/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.80/1.50      inference(light_normalisation,[status(thm)],[c_2123,c_9]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3962,plain,
% 7.80/1.50      ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X0)),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 7.80/1.50      inference(global_propositional_subsumption,
% 7.80/1.50                [status(thm)],
% 7.80/1.50                [c_2129,c_35]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3965,plain,
% 7.80/1.50      ( k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
% 7.80/1.50      inference(demodulation,
% 7.80/1.50                [status(thm)],
% 7.80/1.50                [c_3962,c_2280,c_2424,c_3019,c_3938]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_9962,plain,
% 7.80/1.50      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
% 7.80/1.50      inference(demodulation,[status(thm)],[c_9948,c_3965]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_15621,plain,
% 7.80/1.50      ( k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 7.80/1.50      inference(demodulation,[status(thm)],[c_3019,c_9962]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_15625,plain,
% 7.80/1.50      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k9_relat_1(k6_relat_1(X1),X0) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_9948,c_15621]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_21017,plain,
% 7.80/1.50      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_3940,c_15625]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_21,negated_conjecture,
% 7.80/1.50      ( v1_relat_1(sK0) ),
% 7.80/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1049,plain,
% 7.80/1.50      ( v1_relat_1(sK0) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3020,plain,
% 7.80/1.50      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_1049,c_3015]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_10000,plain,
% 7.80/1.50      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = k10_relat_1(sK0,X0) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_9948,c_3020]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3969,plain,
% 7.80/1.50      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X1)),X1)) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_3020,c_3965]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_10002,plain,
% 7.80/1.50      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0)) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_9948,c_3969]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_10003,plain,
% 7.80/1.50      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,X0)) = k10_relat_1(sK0,X0) ),
% 7.80/1.50      inference(demodulation,[status(thm)],[c_10000,c_10002]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_21042,plain,
% 7.80/1.50      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 7.80/1.50      inference(demodulation,[status(thm)],[c_21017,c_3020,c_10003]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_749,plain,( X0 = X0 ),theory(equality) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1175,plain,
% 7.80/1.50      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 7.80/1.50      inference(instantiation,[status(thm)],[c_749]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_750,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1089,plain,
% 7.80/1.50      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
% 7.80/1.50      | k10_relat_1(sK0,sK2) != X0
% 7.80/1.50      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.80/1.50      inference(instantiation,[status(thm)],[c_750]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1118,plain,
% 7.80/1.50      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
% 7.80/1.50      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 7.80/1.50      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 7.80/1.50      inference(instantiation,[status(thm)],[c_1089]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_18,negated_conjecture,
% 7.80/1.50      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.80/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(contradiction,plain,
% 7.80/1.50      ( $false ),
% 7.80/1.50      inference(minisat,[status(thm)],[c_21042,c_1175,c_1118,c_18]) ).
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.50  
% 7.80/1.50  ------                               Statistics
% 7.80/1.50  
% 7.80/1.50  ------ General
% 7.80/1.50  
% 7.80/1.50  abstr_ref_over_cycles:                  0
% 7.80/1.50  abstr_ref_under_cycles:                 0
% 7.80/1.50  gc_basic_clause_elim:                   0
% 7.80/1.50  forced_gc_time:                         0
% 7.80/1.50  parsing_time:                           0.012
% 7.80/1.50  unif_index_cands_time:                  0.
% 7.80/1.50  unif_index_add_time:                    0.
% 7.80/1.50  orderings_time:                         0.
% 7.80/1.50  out_proof_time:                         0.009
% 7.80/1.50  total_time:                             0.747
% 7.80/1.50  num_of_symbols:                         47
% 7.80/1.50  num_of_terms:                           31588
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing
% 7.80/1.50  
% 7.80/1.50  num_of_splits:                          0
% 7.80/1.50  num_of_split_atoms:                     0
% 7.80/1.50  num_of_reused_defs:                     0
% 7.80/1.50  num_eq_ax_congr_red:                    30
% 7.80/1.50  num_of_sem_filtered_clauses:            1
% 7.80/1.50  num_of_subtypes:                        0
% 7.80/1.50  monotx_restored_types:                  0
% 7.80/1.50  sat_num_of_epr_types:                   0
% 7.80/1.50  sat_num_of_non_cyclic_types:            0
% 7.80/1.50  sat_guarded_non_collapsed_types:        0
% 7.80/1.50  num_pure_diseq_elim:                    0
% 7.80/1.50  simp_replaced_by:                       0
% 7.80/1.50  res_preprocessed:                       113
% 7.80/1.50  prep_upred:                             0
% 7.80/1.50  prep_unflattend:                        36
% 7.80/1.50  smt_new_axioms:                         0
% 7.80/1.50  pred_elim_cands:                        3
% 7.80/1.50  pred_elim:                              0
% 7.80/1.50  pred_elim_cl:                           0
% 7.80/1.50  pred_elim_cycles:                       4
% 7.80/1.50  merged_defs:                            0
% 7.80/1.50  merged_defs_ncl:                        0
% 7.80/1.50  bin_hyper_res:                          0
% 7.80/1.50  prep_cycles:                            4
% 7.80/1.50  pred_elim_time:                         0.01
% 7.80/1.50  splitting_time:                         0.
% 7.80/1.50  sem_filter_time:                        0.
% 7.80/1.50  monotx_time:                            0.
% 7.80/1.50  subtype_inf_time:                       0.
% 7.80/1.50  
% 7.80/1.50  ------ Problem properties
% 7.80/1.50  
% 7.80/1.50  clauses:                                21
% 7.80/1.50  conjectures:                            4
% 7.80/1.50  epr:                                    4
% 7.80/1.50  horn:                                   21
% 7.80/1.50  ground:                                 4
% 7.80/1.50  unary:                                  11
% 7.80/1.50  binary:                                 6
% 7.80/1.50  lits:                                   37
% 7.80/1.50  lits_eq:                                11
% 7.80/1.50  fd_pure:                                0
% 7.80/1.50  fd_pseudo:                              0
% 7.80/1.50  fd_cond:                                0
% 7.80/1.50  fd_pseudo_cond:                         1
% 7.80/1.50  ac_symbols:                             0
% 7.80/1.50  
% 7.80/1.50  ------ Propositional Solver
% 7.80/1.50  
% 7.80/1.50  prop_solver_calls:                      32
% 7.80/1.50  prop_fast_solver_calls:                 1002
% 7.80/1.50  smt_solver_calls:                       0
% 7.80/1.50  smt_fast_solver_calls:                  0
% 7.80/1.50  prop_num_of_clauses:                    10262
% 7.80/1.50  prop_preprocess_simplified:             19269
% 7.80/1.50  prop_fo_subsumed:                       47
% 7.80/1.50  prop_solver_time:                       0.
% 7.80/1.50  smt_solver_time:                        0.
% 7.80/1.50  smt_fast_solver_time:                   0.
% 7.80/1.50  prop_fast_solver_time:                  0.
% 7.80/1.50  prop_unsat_core_time:                   0.001
% 7.80/1.50  
% 7.80/1.50  ------ QBF
% 7.80/1.50  
% 7.80/1.50  qbf_q_res:                              0
% 7.80/1.50  qbf_num_tautologies:                    0
% 7.80/1.50  qbf_prep_cycles:                        0
% 7.80/1.50  
% 7.80/1.50  ------ BMC1
% 7.80/1.50  
% 7.80/1.50  bmc1_current_bound:                     -1
% 7.80/1.50  bmc1_last_solved_bound:                 -1
% 7.80/1.50  bmc1_unsat_core_size:                   -1
% 7.80/1.50  bmc1_unsat_core_parents_size:           -1
% 7.80/1.50  bmc1_merge_next_fun:                    0
% 7.80/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.80/1.50  
% 7.80/1.50  ------ Instantiation
% 7.80/1.50  
% 7.80/1.50  inst_num_of_clauses:                    2829
% 7.80/1.50  inst_num_in_passive:                    921
% 7.80/1.50  inst_num_in_active:                     921
% 7.80/1.50  inst_num_in_unprocessed:                987
% 7.80/1.50  inst_num_of_loops:                      980
% 7.80/1.50  inst_num_of_learning_restarts:          0
% 7.80/1.50  inst_num_moves_active_passive:          56
% 7.80/1.50  inst_lit_activity:                      0
% 7.80/1.50  inst_lit_activity_moves:                0
% 7.80/1.50  inst_num_tautologies:                   0
% 7.80/1.50  inst_num_prop_implied:                  0
% 7.80/1.50  inst_num_existing_simplified:           0
% 7.80/1.50  inst_num_eq_res_simplified:             0
% 7.80/1.50  inst_num_child_elim:                    0
% 7.80/1.50  inst_num_of_dismatching_blockings:      1558
% 7.80/1.50  inst_num_of_non_proper_insts:           3544
% 7.80/1.50  inst_num_of_duplicates:                 0
% 7.80/1.50  inst_inst_num_from_inst_to_res:         0
% 7.80/1.50  inst_dismatching_checking_time:         0.
% 7.80/1.50  
% 7.80/1.50  ------ Resolution
% 7.80/1.50  
% 7.80/1.50  res_num_of_clauses:                     0
% 7.80/1.50  res_num_in_passive:                     0
% 7.80/1.50  res_num_in_active:                      0
% 7.80/1.50  res_num_of_loops:                       117
% 7.80/1.50  res_forward_subset_subsumed:            505
% 7.80/1.50  res_backward_subset_subsumed:           0
% 7.80/1.50  res_forward_subsumed:                   0
% 7.80/1.50  res_backward_subsumed:                  0
% 7.80/1.50  res_forward_subsumption_resolution:     1
% 7.80/1.50  res_backward_subsumption_resolution:    0
% 7.80/1.50  res_clause_to_clause_subsumption:       3854
% 7.80/1.50  res_orphan_elimination:                 0
% 7.80/1.50  res_tautology_del:                      239
% 7.80/1.50  res_num_eq_res_simplified:              0
% 7.80/1.50  res_num_sel_changes:                    0
% 7.80/1.50  res_moves_from_active_to_pass:          0
% 7.80/1.50  
% 7.80/1.50  ------ Superposition
% 7.80/1.50  
% 7.80/1.50  sup_time_total:                         0.
% 7.80/1.50  sup_time_generating:                    0.
% 7.80/1.50  sup_time_sim_full:                      0.
% 7.80/1.50  sup_time_sim_immed:                     0.
% 7.80/1.50  
% 7.80/1.50  sup_num_of_clauses:                     931
% 7.80/1.50  sup_num_in_active:                      135
% 7.80/1.50  sup_num_in_passive:                     796
% 7.80/1.50  sup_num_of_loops:                       195
% 7.80/1.50  sup_fw_superposition:                   744
% 7.80/1.50  sup_bw_superposition:                   731
% 7.80/1.50  sup_immediate_simplified:               638
% 7.80/1.50  sup_given_eliminated:                   1
% 7.80/1.50  comparisons_done:                       0
% 7.80/1.50  comparisons_avoided:                    0
% 7.80/1.50  
% 7.80/1.50  ------ Simplifications
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  sim_fw_subset_subsumed:                 11
% 7.80/1.50  sim_bw_subset_subsumed:                 1
% 7.80/1.50  sim_fw_subsumed:                        117
% 7.80/1.50  sim_bw_subsumed:                        9
% 7.80/1.50  sim_fw_subsumption_res:                 0
% 7.80/1.50  sim_bw_subsumption_res:                 0
% 7.80/1.50  sim_tautology_del:                      44
% 7.80/1.50  sim_eq_tautology_del:                   55
% 7.80/1.50  sim_eq_res_simp:                        0
% 7.80/1.50  sim_fw_demodulated:                     484
% 7.80/1.50  sim_bw_demodulated:                     72
% 7.80/1.50  sim_light_normalised:                   287
% 7.80/1.50  sim_joinable_taut:                      0
% 7.80/1.50  sim_joinable_simp:                      0
% 7.80/1.50  sim_ac_normalised:                      0
% 7.80/1.50  sim_smt_subsumption:                    0
% 7.80/1.50  
%------------------------------------------------------------------------------
