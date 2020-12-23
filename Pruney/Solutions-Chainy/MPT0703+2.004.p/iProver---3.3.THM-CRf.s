%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:15 EST 2020

% Result     : Theorem 23.64s
% Output     : CNFRefutation 23.64s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 274 expanded)
%              Number of clauses        :   57 (  95 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  228 ( 772 expanded)
%              Number of equality atoms :   99 ( 183 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK3,sK4)
      & r1_tarski(sK3,k2_relat_1(sK5))
      & r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4))
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ~ r1_tarski(sK3,sK4)
    & r1_tarski(sK3,k2_relat_1(sK5))
    & r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4))
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f54])).

fof(f93,plain,(
    r1_tarski(sK3,k2_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f85,f83,f84])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f89,f83])).

fof(f90,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1269,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1268,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3388,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_1268])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(sK3,k2_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1257,plain,
    ( r1_tarski(sK3,k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1267,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2404,plain,
    ( k2_xboole_0(sK3,k2_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1257,c_1267])).

cnf(c_3392,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2404,c_1268])).

cnf(c_20144,plain,
    ( r1_tarski(sK3,k2_xboole_0(k2_relat_1(sK5),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3388,c_3392])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1264,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24016,plain,
    ( r1_tarski(k4_xboole_0(sK3,k2_relat_1(sK5)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20144,c_1264])).

cnf(c_27,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1265,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2389,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1265])).

cnf(c_90382,plain,
    ( k4_xboole_0(sK3,k2_relat_1(sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24016,c_2389])).

cnf(c_93183,plain,
    ( k1_setfam_1(k1_enumset1(sK3,sK3,k2_relat_1(sK5))) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_90382,c_27])).

cnf(c_24,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1255,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1259,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1422,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1259,c_27])).

cnf(c_24816,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK5,k1_relat_1(sK5)))) = k9_relat_1(sK5,k10_relat_1(sK5,X0))
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_1422])).

cnf(c_36,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1254,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_28,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1262,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3119,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1254,c_1262])).

cnf(c_24817,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK5))) = k9_relat_1(sK5,k10_relat_1(sK5,X0))
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24816,c_3119])).

cnf(c_37,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_25061,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK5))) = k9_relat_1(sK5,k10_relat_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24817,c_37])).

cnf(c_93204,plain,
    ( k1_setfam_1(k1_enumset1(sK3,sK3,k2_relat_1(sK5))) = sK3 ),
    inference(demodulation,[status(thm)],[c_93183,c_24,c_25061])).

cnf(c_93437,plain,
    ( k9_relat_1(sK5,k10_relat_1(sK5,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_93204,c_25061])).

cnf(c_30,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1260,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2403,plain,
    ( k2_xboole_0(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1267])).

cnf(c_13856,plain,
    ( k2_xboole_0(k9_relat_1(sK5,k10_relat_1(sK5,X0)),X0) = X0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_2403])).

cnf(c_14882,plain,
    ( k2_xboole_0(k9_relat_1(sK5,k10_relat_1(sK5,X0)),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13856,c_37])).

cnf(c_20130,plain,
    ( r1_tarski(k9_relat_1(sK5,k10_relat_1(sK5,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14882,c_3388])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1256,plain,
    ( r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1261,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2978,plain,
    ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,X2)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1267])).

cnf(c_16502,plain,
    ( k2_xboole_0(k9_relat_1(X0,k10_relat_1(sK5,sK3)),k9_relat_1(X0,k10_relat_1(sK5,sK4))) = k9_relat_1(X0,k10_relat_1(sK5,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_2978])).

cnf(c_18875,plain,
    ( k2_xboole_0(k9_relat_1(sK5,k10_relat_1(sK5,sK3)),k9_relat_1(sK5,k10_relat_1(sK5,sK4))) = k9_relat_1(sK5,k10_relat_1(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_1254,c_16502])).

cnf(c_18877,plain,
    ( r1_tarski(k9_relat_1(sK5,k10_relat_1(sK5,sK4)),X0) != iProver_top
    | r1_tarski(k9_relat_1(sK5,k10_relat_1(sK5,sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18875,c_1268])).

cnf(c_23158,plain,
    ( r1_tarski(k9_relat_1(sK5,k10_relat_1(sK5,sK3)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_20130,c_18877])).

cnf(c_93471,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_93437,c_23158])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_41,plain,
    ( r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93471,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.64/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.64/3.49  
% 23.64/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.64/3.49  
% 23.64/3.49  ------  iProver source info
% 23.64/3.49  
% 23.64/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.64/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.64/3.49  git: non_committed_changes: false
% 23.64/3.49  git: last_make_outside_of_git: false
% 23.64/3.49  
% 23.64/3.49  ------ 
% 23.64/3.49  ------ Parsing...
% 23.64/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.64/3.49  
% 23.64/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.64/3.49  
% 23.64/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.64/3.49  
% 23.64/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.64/3.49  ------ Proving...
% 23.64/3.49  ------ Problem Properties 
% 23.64/3.49  
% 23.64/3.49  
% 23.64/3.49  clauses                                 36
% 23.64/3.49  conjectures                             5
% 23.64/3.49  EPR                                     6
% 23.64/3.49  Horn                                    29
% 23.64/3.49  unary                                   11
% 23.64/3.49  binary                                  12
% 23.64/3.49  lits                                    76
% 23.64/3.49  lits eq                                 15
% 23.64/3.49  fd_pure                                 0
% 23.64/3.50  fd_pseudo                               0
% 23.64/3.50  fd_cond                                 1
% 23.64/3.50  fd_pseudo_cond                          7
% 23.64/3.50  AC symbols                              0
% 23.64/3.50  
% 23.64/3.50  ------ Input Options Time Limit: Unbounded
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  ------ 
% 23.64/3.50  Current options:
% 23.64/3.50  ------ 
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  ------ Proving...
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  % SZS status Theorem for theBenchmark.p
% 23.64/3.50  
% 23.64/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.64/3.50  
% 23.64/3.50  fof(f5,axiom,(
% 23.64/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f52,plain,(
% 23.64/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.64/3.50    inference(nnf_transformation,[],[f5])).
% 23.64/3.50  
% 23.64/3.50  fof(f53,plain,(
% 23.64/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.64/3.50    inference(flattening,[],[f52])).
% 23.64/3.50  
% 23.64/3.50  fof(f72,plain,(
% 23.64/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.64/3.50    inference(cnf_transformation,[],[f53])).
% 23.64/3.50  
% 23.64/3.50  fof(f111,plain,(
% 23.64/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.64/3.50    inference(equality_resolution,[],[f72])).
% 23.64/3.50  
% 23.64/3.50  fof(f7,axiom,(
% 23.64/3.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f24,plain,(
% 23.64/3.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 23.64/3.50    inference(ennf_transformation,[],[f7])).
% 23.64/3.50  
% 23.64/3.50  fof(f76,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f24])).
% 23.64/3.50  
% 23.64/3.50  fof(f21,conjecture,(
% 23.64/3.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f22,negated_conjecture,(
% 23.64/3.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.64/3.50    inference(negated_conjecture,[],[f21])).
% 23.64/3.50  
% 23.64/3.50  fof(f36,plain,(
% 23.64/3.50    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 23.64/3.50    inference(ennf_transformation,[],[f22])).
% 23.64/3.50  
% 23.64/3.50  fof(f37,plain,(
% 23.64/3.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 23.64/3.50    inference(flattening,[],[f36])).
% 23.64/3.50  
% 23.64/3.50  fof(f54,plain,(
% 23.64/3.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK3,sK4) & r1_tarski(sK3,k2_relat_1(sK5)) & r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 23.64/3.50    introduced(choice_axiom,[])).
% 23.64/3.50  
% 23.64/3.50  fof(f55,plain,(
% 23.64/3.50    ~r1_tarski(sK3,sK4) & r1_tarski(sK3,k2_relat_1(sK5)) & r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 23.64/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f54])).
% 23.64/3.50  
% 23.64/3.50  fof(f93,plain,(
% 23.64/3.50    r1_tarski(sK3,k2_relat_1(sK5))),
% 23.64/3.50    inference(cnf_transformation,[],[f55])).
% 23.64/3.50  
% 23.64/3.50  fof(f8,axiom,(
% 23.64/3.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f25,plain,(
% 23.64/3.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 23.64/3.50    inference(ennf_transformation,[],[f8])).
% 23.64/3.50  
% 23.64/3.50  fof(f77,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f25])).
% 23.64/3.50  
% 23.64/3.50  fof(f12,axiom,(
% 23.64/3.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f27,plain,(
% 23.64/3.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.64/3.50    inference(ennf_transformation,[],[f12])).
% 23.64/3.50  
% 23.64/3.50  fof(f81,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f27])).
% 23.64/3.50  
% 23.64/3.50  fof(f16,axiom,(
% 23.64/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f85,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f16])).
% 23.64/3.50  
% 23.64/3.50  fof(f14,axiom,(
% 23.64/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f83,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f14])).
% 23.64/3.50  
% 23.64/3.50  fof(f15,axiom,(
% 23.64/3.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f84,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f15])).
% 23.64/3.50  
% 23.64/3.50  fof(f102,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 23.64/3.50    inference(definition_unfolding,[],[f85,f83,f84])).
% 23.64/3.50  
% 23.64/3.50  fof(f10,axiom,(
% 23.64/3.50    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f26,plain,(
% 23.64/3.50    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f10])).
% 23.64/3.50  
% 23.64/3.50  fof(f79,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f26])).
% 23.64/3.50  
% 23.64/3.50  fof(f11,axiom,(
% 23.64/3.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f80,plain,(
% 23.64/3.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.64/3.50    inference(cnf_transformation,[],[f11])).
% 23.64/3.50  
% 23.64/3.50  fof(f91,plain,(
% 23.64/3.50    v1_funct_1(sK5)),
% 23.64/3.50    inference(cnf_transformation,[],[f55])).
% 23.64/3.50  
% 23.64/3.50  fof(f20,axiom,(
% 23.64/3.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f34,plain,(
% 23.64/3.50    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.64/3.50    inference(ennf_transformation,[],[f20])).
% 23.64/3.50  
% 23.64/3.50  fof(f35,plain,(
% 23.64/3.50    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.64/3.50    inference(flattening,[],[f34])).
% 23.64/3.50  
% 23.64/3.50  fof(f89,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f35])).
% 23.64/3.50  
% 23.64/3.50  fof(f103,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.64/3.50    inference(definition_unfolding,[],[f89,f83])).
% 23.64/3.50  
% 23.64/3.50  fof(f90,plain,(
% 23.64/3.50    v1_relat_1(sK5)),
% 23.64/3.50    inference(cnf_transformation,[],[f55])).
% 23.64/3.50  
% 23.64/3.50  fof(f17,axiom,(
% 23.64/3.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f29,plain,(
% 23.64/3.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 23.64/3.50    inference(ennf_transformation,[],[f17])).
% 23.64/3.50  
% 23.64/3.50  fof(f86,plain,(
% 23.64/3.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f29])).
% 23.64/3.50  
% 23.64/3.50  fof(f19,axiom,(
% 23.64/3.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f32,plain,(
% 23.64/3.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.64/3.50    inference(ennf_transformation,[],[f19])).
% 23.64/3.50  
% 23.64/3.50  fof(f33,plain,(
% 23.64/3.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.64/3.50    inference(flattening,[],[f32])).
% 23.64/3.50  
% 23.64/3.50  fof(f88,plain,(
% 23.64/3.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f33])).
% 23.64/3.50  
% 23.64/3.50  fof(f92,plain,(
% 23.64/3.50    r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4))),
% 23.64/3.50    inference(cnf_transformation,[],[f55])).
% 23.64/3.50  
% 23.64/3.50  fof(f18,axiom,(
% 23.64/3.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f30,plain,(
% 23.64/3.50    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 23.64/3.50    inference(ennf_transformation,[],[f18])).
% 23.64/3.50  
% 23.64/3.50  fof(f31,plain,(
% 23.64/3.50    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 23.64/3.50    inference(flattening,[],[f30])).
% 23.64/3.50  
% 23.64/3.50  fof(f87,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f31])).
% 23.64/3.50  
% 23.64/3.50  fof(f94,plain,(
% 23.64/3.50    ~r1_tarski(sK3,sK4)),
% 23.64/3.50    inference(cnf_transformation,[],[f55])).
% 23.64/3.50  
% 23.64/3.50  cnf(c_19,plain,
% 23.64/3.50      ( r1_tarski(X0,X0) ),
% 23.64/3.50      inference(cnf_transformation,[],[f111]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1269,plain,
% 23.64/3.50      ( r1_tarski(X0,X0) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_20,plain,
% 23.64/3.50      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 23.64/3.50      inference(cnf_transformation,[],[f76]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1268,plain,
% 23.64/3.50      ( r1_tarski(X0,X1) = iProver_top
% 23.64/3.50      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3388,plain,
% 23.64/3.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1269,c_1268]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_33,negated_conjecture,
% 23.64/3.50      ( r1_tarski(sK3,k2_relat_1(sK5)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f93]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1257,plain,
% 23.64/3.50      ( r1_tarski(sK3,k2_relat_1(sK5)) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_21,plain,
% 23.64/3.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 23.64/3.50      inference(cnf_transformation,[],[f77]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1267,plain,
% 23.64/3.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2404,plain,
% 23.64/3.50      ( k2_xboole_0(sK3,k2_relat_1(sK5)) = k2_relat_1(sK5) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1257,c_1267]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3392,plain,
% 23.64/3.50      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 23.64/3.50      | r1_tarski(sK3,X0) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_2404,c_1268]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_20144,plain,
% 23.64/3.50      ( r1_tarski(sK3,k2_xboole_0(k2_relat_1(sK5),X0)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3388,c_3392]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_25,plain,
% 23.64/3.50      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.64/3.50      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 23.64/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1264,plain,
% 23.64/3.50      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 23.64/3.50      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_24016,plain,
% 23.64/3.50      ( r1_tarski(k4_xboole_0(sK3,k2_relat_1(sK5)),X0) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_20144,c_1264]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_27,plain,
% 23.64/3.50      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f102]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_23,plain,
% 23.64/3.50      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1265,plain,
% 23.64/3.50      ( k1_xboole_0 = X0
% 23.64/3.50      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2389,plain,
% 23.64/3.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 23.64/3.50      | r1_tarski(k4_xboole_0(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_27,c_1265]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_90382,plain,
% 23.64/3.50      ( k4_xboole_0(sK3,k2_relat_1(sK5)) = k1_xboole_0 ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_24016,c_2389]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_93183,plain,
% 23.64/3.50      ( k1_setfam_1(k1_enumset1(sK3,sK3,k2_relat_1(sK5))) = k4_xboole_0(sK3,k1_xboole_0) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_90382,c_27]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_24,plain,
% 23.64/3.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_35,negated_conjecture,
% 23.64/3.50      ( v1_funct_1(sK5) ),
% 23.64/3.50      inference(cnf_transformation,[],[f91]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1255,plain,
% 23.64/3.50      ( v1_funct_1(sK5) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_31,plain,
% 23.64/3.50      ( ~ v1_funct_1(X0)
% 23.64/3.50      | ~ v1_relat_1(X0)
% 23.64/3.50      | k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f103]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1259,plain,
% 23.64/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
% 23.64/3.50      | v1_funct_1(X1) != iProver_top
% 23.64/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1422,plain,
% 23.64/3.50      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
% 23.64/3.50      | v1_funct_1(X1) != iProver_top
% 23.64/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_1259,c_27]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_24816,plain,
% 23.64/3.50      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK5,k1_relat_1(sK5)))) = k9_relat_1(sK5,k10_relat_1(sK5,X0))
% 23.64/3.50      | v1_relat_1(sK5) != iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1255,c_1422]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_36,negated_conjecture,
% 23.64/3.50      ( v1_relat_1(sK5) ),
% 23.64/3.50      inference(cnf_transformation,[],[f90]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1254,plain,
% 23.64/3.50      ( v1_relat_1(sK5) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_28,plain,
% 23.64/3.50      ( ~ v1_relat_1(X0)
% 23.64/3.50      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 23.64/3.50      inference(cnf_transformation,[],[f86]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1262,plain,
% 23.64/3.50      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 23.64/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3119,plain,
% 23.64/3.50      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1254,c_1262]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_24817,plain,
% 23.64/3.50      ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK5))) = k9_relat_1(sK5,k10_relat_1(sK5,X0))
% 23.64/3.50      | v1_relat_1(sK5) != iProver_top ),
% 23.64/3.50      inference(light_normalisation,[status(thm)],[c_24816,c_3119]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_37,plain,
% 23.64/3.50      ( v1_relat_1(sK5) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_25061,plain,
% 23.64/3.50      ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK5))) = k9_relat_1(sK5,k10_relat_1(sK5,X0)) ),
% 23.64/3.50      inference(global_propositional_subsumption,
% 23.64/3.50                [status(thm)],
% 23.64/3.50                [c_24817,c_37]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_93204,plain,
% 23.64/3.50      ( k1_setfam_1(k1_enumset1(sK3,sK3,k2_relat_1(sK5))) = sK3 ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_93183,c_24,c_25061]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_93437,plain,
% 23.64/3.50      ( k9_relat_1(sK5,k10_relat_1(sK5,sK3)) = sK3 ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_93204,c_25061]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_30,plain,
% 23.64/3.50      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 23.64/3.50      | ~ v1_funct_1(X0)
% 23.64/3.50      | ~ v1_relat_1(X0) ),
% 23.64/3.50      inference(cnf_transformation,[],[f88]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1260,plain,
% 23.64/3.50      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 23.64/3.50      | v1_funct_1(X0) != iProver_top
% 23.64/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2403,plain,
% 23.64/3.50      ( k2_xboole_0(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = X1
% 23.64/3.50      | v1_funct_1(X0) != iProver_top
% 23.64/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1260,c_1267]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_13856,plain,
% 23.64/3.50      ( k2_xboole_0(k9_relat_1(sK5,k10_relat_1(sK5,X0)),X0) = X0
% 23.64/3.50      | v1_relat_1(sK5) != iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1255,c_2403]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_14882,plain,
% 23.64/3.50      ( k2_xboole_0(k9_relat_1(sK5,k10_relat_1(sK5,X0)),X0) = X0 ),
% 23.64/3.50      inference(global_propositional_subsumption,
% 23.64/3.50                [status(thm)],
% 23.64/3.50                [c_13856,c_37]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_20130,plain,
% 23.64/3.50      ( r1_tarski(k9_relat_1(sK5,k10_relat_1(sK5,X0)),X0) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_14882,c_3388]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_34,negated_conjecture,
% 23.64/3.50      ( r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f92]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1256,plain,
% 23.64/3.50      ( r1_tarski(k10_relat_1(sK5,sK3),k10_relat_1(sK5,sK4)) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_29,plain,
% 23.64/3.50      ( ~ r1_tarski(X0,X1)
% 23.64/3.50      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 23.64/3.50      | ~ v1_relat_1(X2) ),
% 23.64/3.50      inference(cnf_transformation,[],[f87]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1261,plain,
% 23.64/3.50      ( r1_tarski(X0,X1) != iProver_top
% 23.64/3.50      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 23.64/3.50      | v1_relat_1(X2) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2978,plain,
% 23.64/3.50      ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,X2)
% 23.64/3.50      | r1_tarski(X1,X2) != iProver_top
% 23.64/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1261,c_1267]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_16502,plain,
% 23.64/3.50      ( k2_xboole_0(k9_relat_1(X0,k10_relat_1(sK5,sK3)),k9_relat_1(X0,k10_relat_1(sK5,sK4))) = k9_relat_1(X0,k10_relat_1(sK5,sK4))
% 23.64/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1256,c_2978]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_18875,plain,
% 23.64/3.50      ( k2_xboole_0(k9_relat_1(sK5,k10_relat_1(sK5,sK3)),k9_relat_1(sK5,k10_relat_1(sK5,sK4))) = k9_relat_1(sK5,k10_relat_1(sK5,sK4)) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1254,c_16502]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_18877,plain,
% 23.64/3.50      ( r1_tarski(k9_relat_1(sK5,k10_relat_1(sK5,sK4)),X0) != iProver_top
% 23.64/3.50      | r1_tarski(k9_relat_1(sK5,k10_relat_1(sK5,sK3)),X0) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_18875,c_1268]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_23158,plain,
% 23.64/3.50      ( r1_tarski(k9_relat_1(sK5,k10_relat_1(sK5,sK3)),sK4) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_20130,c_18877]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_93471,plain,
% 23.64/3.50      ( r1_tarski(sK3,sK4) = iProver_top ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_93437,c_23158]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_32,negated_conjecture,
% 23.64/3.50      ( ~ r1_tarski(sK3,sK4) ),
% 23.64/3.50      inference(cnf_transformation,[],[f94]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_41,plain,
% 23.64/3.50      ( r1_tarski(sK3,sK4) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(contradiction,plain,
% 23.64/3.50      ( $false ),
% 23.64/3.50      inference(minisat,[status(thm)],[c_93471,c_41]) ).
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.64/3.50  
% 23.64/3.50  ------                               Statistics
% 23.64/3.50  
% 23.64/3.50  ------ Selected
% 23.64/3.50  
% 23.64/3.50  total_time:                             2.808
% 23.64/3.50  
%------------------------------------------------------------------------------
