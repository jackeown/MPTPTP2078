%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:39 EST 2020

% Result     : Theorem 15.65s
% Output     : CNFRefutation 15.65s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 314 expanded)
%              Number of clauses        :   67 ( 122 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  282 ( 806 expanded)
%              Number of equality atoms :  127 ( 305 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,
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

fof(f34,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).

fof(f58,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f16,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f55,f41])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f41,f45])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_15,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_548,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_553,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_546,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_551,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_552,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2580,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_552])).

cnf(c_6796,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X3),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2580,c_552])).

cnf(c_49852,plain,
    ( r1_tarski(k4_xboole_0(sK0,X0),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_6796])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 != X2
    | k4_xboole_0(X3,X1) != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_213,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_544,plain,
    ( k1_xboole_0 = k4_xboole_0(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_50455,plain,
    ( k4_xboole_0(sK0,X0) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_49852,c_544])).

cnf(c_51206,plain,
    ( k4_xboole_0(sK0,k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_553,c_50455])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_550,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2379,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_550])).

cnf(c_7533,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_548,c_2379])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7538,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_7533,c_12])).

cnf(c_18,plain,
    ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_555,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_18,c_9])).

cnf(c_1746,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_555,c_12])).

cnf(c_7670,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_7538,c_1746])).

cnf(c_23872,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_7670,c_9])).

cnf(c_52740,plain,
    ( k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_51206,c_23872])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_52777,plain,
    ( k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_52740,c_5])).

cnf(c_17,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1)))
    | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_547,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_53580,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK0,k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k9_relat_1(X0,sK0))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_52777,c_547])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_53682,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK0,k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k9_relat_1(X0,sK0))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_53580,c_11])).

cnf(c_19,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_572,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_573,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_16,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_227,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_228,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_232,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_23,c_22])).

cnf(c_577,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_578,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_545,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_549,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1857,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_545,c_549])).

cnf(c_1940,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_547])).

cnf(c_1941,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1940,c_11])).

cnf(c_24,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_896,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_897,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_1946,plain,
    ( v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1941,c_24,c_897])).

cnf(c_1947,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1946])).

cnf(c_53615,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_52777,c_1947])).

cnf(c_53744,plain,
    ( v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_53682,c_19,c_573,c_578,c_53615])).

cnf(c_53748,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_548,c_53744])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:40:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.65/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.65/2.48  
% 15.65/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.65/2.48  
% 15.65/2.48  ------  iProver source info
% 15.65/2.48  
% 15.65/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.65/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.65/2.48  git: non_committed_changes: false
% 15.65/2.48  git: last_make_outside_of_git: false
% 15.65/2.48  
% 15.65/2.48  ------ 
% 15.65/2.48  
% 15.65/2.48  ------ Input Options
% 15.65/2.48  
% 15.65/2.48  --out_options                           all
% 15.65/2.48  --tptp_safe_out                         true
% 15.65/2.48  --problem_path                          ""
% 15.65/2.48  --include_path                          ""
% 15.65/2.48  --clausifier                            res/vclausify_rel
% 15.65/2.48  --clausifier_options                    ""
% 15.65/2.48  --stdin                                 false
% 15.65/2.48  --stats_out                             all
% 15.65/2.48  
% 15.65/2.48  ------ General Options
% 15.65/2.48  
% 15.65/2.48  --fof                                   false
% 15.65/2.48  --time_out_real                         305.
% 15.65/2.48  --time_out_virtual                      -1.
% 15.65/2.48  --symbol_type_check                     false
% 15.65/2.48  --clausify_out                          false
% 15.65/2.48  --sig_cnt_out                           false
% 15.65/2.48  --trig_cnt_out                          false
% 15.65/2.48  --trig_cnt_out_tolerance                1.
% 15.65/2.48  --trig_cnt_out_sk_spl                   false
% 15.65/2.48  --abstr_cl_out                          false
% 15.65/2.48  
% 15.65/2.48  ------ Global Options
% 15.65/2.48  
% 15.65/2.48  --schedule                              default
% 15.65/2.48  --add_important_lit                     false
% 15.65/2.48  --prop_solver_per_cl                    1000
% 15.65/2.48  --min_unsat_core                        false
% 15.65/2.48  --soft_assumptions                      false
% 15.65/2.48  --soft_lemma_size                       3
% 15.65/2.48  --prop_impl_unit_size                   0
% 15.65/2.48  --prop_impl_unit                        []
% 15.65/2.48  --share_sel_clauses                     true
% 15.65/2.48  --reset_solvers                         false
% 15.65/2.48  --bc_imp_inh                            [conj_cone]
% 15.65/2.48  --conj_cone_tolerance                   3.
% 15.65/2.48  --extra_neg_conj                        none
% 15.65/2.48  --large_theory_mode                     true
% 15.65/2.48  --prolific_symb_bound                   200
% 15.65/2.48  --lt_threshold                          2000
% 15.65/2.48  --clause_weak_htbl                      true
% 15.65/2.48  --gc_record_bc_elim                     false
% 15.65/2.48  
% 15.65/2.48  ------ Preprocessing Options
% 15.65/2.48  
% 15.65/2.48  --preprocessing_flag                    true
% 15.65/2.48  --time_out_prep_mult                    0.1
% 15.65/2.48  --splitting_mode                        input
% 15.65/2.48  --splitting_grd                         true
% 15.65/2.48  --splitting_cvd                         false
% 15.65/2.48  --splitting_cvd_svl                     false
% 15.65/2.48  --splitting_nvd                         32
% 15.65/2.48  --sub_typing                            true
% 15.65/2.48  --prep_gs_sim                           true
% 15.65/2.48  --prep_unflatten                        true
% 15.65/2.48  --prep_res_sim                          true
% 15.65/2.48  --prep_upred                            true
% 15.65/2.48  --prep_sem_filter                       exhaustive
% 15.65/2.48  --prep_sem_filter_out                   false
% 15.65/2.48  --pred_elim                             true
% 15.65/2.48  --res_sim_input                         true
% 15.65/2.48  --eq_ax_congr_red                       true
% 15.65/2.48  --pure_diseq_elim                       true
% 15.65/2.48  --brand_transform                       false
% 15.65/2.48  --non_eq_to_eq                          false
% 15.65/2.48  --prep_def_merge                        true
% 15.65/2.48  --prep_def_merge_prop_impl              false
% 15.65/2.48  --prep_def_merge_mbd                    true
% 15.65/2.48  --prep_def_merge_tr_red                 false
% 15.65/2.48  --prep_def_merge_tr_cl                  false
% 15.65/2.48  --smt_preprocessing                     true
% 15.65/2.48  --smt_ac_axioms                         fast
% 15.65/2.48  --preprocessed_out                      false
% 15.65/2.48  --preprocessed_stats                    false
% 15.65/2.48  
% 15.65/2.48  ------ Abstraction refinement Options
% 15.65/2.48  
% 15.65/2.48  --abstr_ref                             []
% 15.65/2.48  --abstr_ref_prep                        false
% 15.65/2.48  --abstr_ref_until_sat                   false
% 15.65/2.48  --abstr_ref_sig_restrict                funpre
% 15.65/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.65/2.48  --abstr_ref_under                       []
% 15.65/2.48  
% 15.65/2.48  ------ SAT Options
% 15.65/2.48  
% 15.65/2.48  --sat_mode                              false
% 15.65/2.48  --sat_fm_restart_options                ""
% 15.65/2.48  --sat_gr_def                            false
% 15.65/2.48  --sat_epr_types                         true
% 15.65/2.48  --sat_non_cyclic_types                  false
% 15.65/2.48  --sat_finite_models                     false
% 15.65/2.48  --sat_fm_lemmas                         false
% 15.65/2.48  --sat_fm_prep                           false
% 15.65/2.48  --sat_fm_uc_incr                        true
% 15.65/2.48  --sat_out_model                         small
% 15.65/2.48  --sat_out_clauses                       false
% 15.65/2.48  
% 15.65/2.48  ------ QBF Options
% 15.65/2.48  
% 15.65/2.48  --qbf_mode                              false
% 15.65/2.48  --qbf_elim_univ                         false
% 15.65/2.48  --qbf_dom_inst                          none
% 15.65/2.48  --qbf_dom_pre_inst                      false
% 15.65/2.48  --qbf_sk_in                             false
% 15.65/2.48  --qbf_pred_elim                         true
% 15.65/2.48  --qbf_split                             512
% 15.65/2.48  
% 15.65/2.48  ------ BMC1 Options
% 15.65/2.48  
% 15.65/2.48  --bmc1_incremental                      false
% 15.65/2.48  --bmc1_axioms                           reachable_all
% 15.65/2.48  --bmc1_min_bound                        0
% 15.65/2.48  --bmc1_max_bound                        -1
% 15.65/2.48  --bmc1_max_bound_default                -1
% 15.65/2.48  --bmc1_symbol_reachability              true
% 15.65/2.48  --bmc1_property_lemmas                  false
% 15.65/2.48  --bmc1_k_induction                      false
% 15.65/2.48  --bmc1_non_equiv_states                 false
% 15.65/2.48  --bmc1_deadlock                         false
% 15.65/2.48  --bmc1_ucm                              false
% 15.65/2.48  --bmc1_add_unsat_core                   none
% 15.65/2.48  --bmc1_unsat_core_children              false
% 15.65/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.65/2.48  --bmc1_out_stat                         full
% 15.65/2.48  --bmc1_ground_init                      false
% 15.65/2.48  --bmc1_pre_inst_next_state              false
% 15.65/2.48  --bmc1_pre_inst_state                   false
% 15.65/2.48  --bmc1_pre_inst_reach_state             false
% 15.65/2.48  --bmc1_out_unsat_core                   false
% 15.65/2.48  --bmc1_aig_witness_out                  false
% 15.65/2.48  --bmc1_verbose                          false
% 15.65/2.48  --bmc1_dump_clauses_tptp                false
% 15.65/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.65/2.48  --bmc1_dump_file                        -
% 15.65/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.65/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.65/2.48  --bmc1_ucm_extend_mode                  1
% 15.65/2.48  --bmc1_ucm_init_mode                    2
% 15.65/2.48  --bmc1_ucm_cone_mode                    none
% 15.65/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.65/2.48  --bmc1_ucm_relax_model                  4
% 15.65/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.65/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.65/2.48  --bmc1_ucm_layered_model                none
% 15.65/2.48  --bmc1_ucm_max_lemma_size               10
% 15.65/2.48  
% 15.65/2.48  ------ AIG Options
% 15.65/2.48  
% 15.65/2.48  --aig_mode                              false
% 15.65/2.48  
% 15.65/2.48  ------ Instantiation Options
% 15.65/2.48  
% 15.65/2.48  --instantiation_flag                    true
% 15.65/2.48  --inst_sos_flag                         true
% 15.65/2.48  --inst_sos_phase                        true
% 15.65/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.65/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.65/2.48  --inst_lit_sel_side                     num_symb
% 15.65/2.48  --inst_solver_per_active                1400
% 15.65/2.48  --inst_solver_calls_frac                1.
% 15.65/2.48  --inst_passive_queue_type               priority_queues
% 15.65/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.65/2.48  --inst_passive_queues_freq              [25;2]
% 15.65/2.48  --inst_dismatching                      true
% 15.65/2.48  --inst_eager_unprocessed_to_passive     true
% 15.65/2.48  --inst_prop_sim_given                   true
% 15.65/2.48  --inst_prop_sim_new                     false
% 15.65/2.48  --inst_subs_new                         false
% 15.65/2.48  --inst_eq_res_simp                      false
% 15.65/2.48  --inst_subs_given                       false
% 15.65/2.48  --inst_orphan_elimination               true
% 15.65/2.48  --inst_learning_loop_flag               true
% 15.65/2.48  --inst_learning_start                   3000
% 15.65/2.48  --inst_learning_factor                  2
% 15.65/2.48  --inst_start_prop_sim_after_learn       3
% 15.65/2.48  --inst_sel_renew                        solver
% 15.65/2.48  --inst_lit_activity_flag                true
% 15.65/2.48  --inst_restr_to_given                   false
% 15.65/2.48  --inst_activity_threshold               500
% 15.65/2.48  --inst_out_proof                        true
% 15.65/2.48  
% 15.65/2.48  ------ Resolution Options
% 15.65/2.48  
% 15.65/2.48  --resolution_flag                       true
% 15.65/2.48  --res_lit_sel                           adaptive
% 15.65/2.48  --res_lit_sel_side                      none
% 15.65/2.48  --res_ordering                          kbo
% 15.65/2.48  --res_to_prop_solver                    active
% 15.65/2.48  --res_prop_simpl_new                    false
% 15.65/2.48  --res_prop_simpl_given                  true
% 15.65/2.48  --res_passive_queue_type                priority_queues
% 15.65/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.65/2.48  --res_passive_queues_freq               [15;5]
% 15.65/2.48  --res_forward_subs                      full
% 15.65/2.48  --res_backward_subs                     full
% 15.65/2.48  --res_forward_subs_resolution           true
% 15.65/2.48  --res_backward_subs_resolution          true
% 15.65/2.48  --res_orphan_elimination                true
% 15.65/2.48  --res_time_limit                        2.
% 15.65/2.48  --res_out_proof                         true
% 15.65/2.48  
% 15.65/2.48  ------ Superposition Options
% 15.65/2.48  
% 15.65/2.48  --superposition_flag                    true
% 15.65/2.48  --sup_passive_queue_type                priority_queues
% 15.65/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.65/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.65/2.48  --demod_completeness_check              fast
% 15.65/2.48  --demod_use_ground                      true
% 15.65/2.48  --sup_to_prop_solver                    passive
% 15.65/2.48  --sup_prop_simpl_new                    true
% 15.65/2.48  --sup_prop_simpl_given                  true
% 15.65/2.48  --sup_fun_splitting                     true
% 15.65/2.48  --sup_smt_interval                      50000
% 15.65/2.48  
% 15.65/2.48  ------ Superposition Simplification Setup
% 15.65/2.48  
% 15.65/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.65/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.65/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.65/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.65/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.65/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.65/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.65/2.48  --sup_immed_triv                        [TrivRules]
% 15.65/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.65/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.65/2.48  --sup_immed_bw_main                     []
% 15.65/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.65/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.65/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.65/2.48  --sup_input_bw                          []
% 15.65/2.48  
% 15.65/2.48  ------ Combination Options
% 15.65/2.48  
% 15.65/2.48  --comb_res_mult                         3
% 15.65/2.48  --comb_sup_mult                         2
% 15.65/2.48  --comb_inst_mult                        10
% 15.65/2.48  
% 15.65/2.48  ------ Debug Options
% 15.65/2.48  
% 15.65/2.48  --dbg_backtrace                         false
% 15.65/2.48  --dbg_dump_prop_clauses                 false
% 15.65/2.48  --dbg_dump_prop_clauses_file            -
% 15.65/2.48  --dbg_out_stat                          false
% 15.65/2.48  ------ Parsing...
% 15.65/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.65/2.48  
% 15.65/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 15.65/2.48  
% 15.65/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.65/2.48  
% 15.65/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.65/2.48  ------ Proving...
% 15.65/2.48  ------ Problem Properties 
% 15.65/2.48  
% 15.65/2.48  
% 15.65/2.48  clauses                                 18
% 15.65/2.48  conjectures                             3
% 15.65/2.48  EPR                                     4
% 15.65/2.48  Horn                                    18
% 15.65/2.48  unary                                   12
% 15.65/2.48  binary                                  2
% 15.65/2.48  lits                                    29
% 15.65/2.48  lits eq                                 10
% 15.65/2.48  fd_pure                                 0
% 15.65/2.48  fd_pseudo                               0
% 15.65/2.48  fd_cond                                 0
% 15.65/2.48  fd_pseudo_cond                          1
% 15.65/2.48  AC symbols                              0
% 15.65/2.48  
% 15.65/2.48  ------ Schedule dynamic 5 is on 
% 15.65/2.48  
% 15.65/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.65/2.48  
% 15.65/2.48  
% 15.65/2.48  ------ 
% 15.65/2.48  Current options:
% 15.65/2.48  ------ 
% 15.65/2.48  
% 15.65/2.48  ------ Input Options
% 15.65/2.48  
% 15.65/2.48  --out_options                           all
% 15.65/2.48  --tptp_safe_out                         true
% 15.65/2.48  --problem_path                          ""
% 15.65/2.48  --include_path                          ""
% 15.65/2.48  --clausifier                            res/vclausify_rel
% 15.65/2.48  --clausifier_options                    ""
% 15.65/2.48  --stdin                                 false
% 15.65/2.48  --stats_out                             all
% 15.65/2.48  
% 15.65/2.48  ------ General Options
% 15.65/2.48  
% 15.65/2.48  --fof                                   false
% 15.65/2.48  --time_out_real                         305.
% 15.65/2.48  --time_out_virtual                      -1.
% 15.65/2.48  --symbol_type_check                     false
% 15.65/2.48  --clausify_out                          false
% 15.65/2.48  --sig_cnt_out                           false
% 15.65/2.48  --trig_cnt_out                          false
% 15.65/2.48  --trig_cnt_out_tolerance                1.
% 15.65/2.48  --trig_cnt_out_sk_spl                   false
% 15.65/2.48  --abstr_cl_out                          false
% 15.65/2.48  
% 15.65/2.48  ------ Global Options
% 15.65/2.48  
% 15.65/2.48  --schedule                              default
% 15.65/2.48  --add_important_lit                     false
% 15.65/2.48  --prop_solver_per_cl                    1000
% 15.65/2.48  --min_unsat_core                        false
% 15.65/2.48  --soft_assumptions                      false
% 15.65/2.48  --soft_lemma_size                       3
% 15.65/2.48  --prop_impl_unit_size                   0
% 15.65/2.48  --prop_impl_unit                        []
% 15.65/2.48  --share_sel_clauses                     true
% 15.65/2.48  --reset_solvers                         false
% 15.65/2.48  --bc_imp_inh                            [conj_cone]
% 15.65/2.48  --conj_cone_tolerance                   3.
% 15.65/2.48  --extra_neg_conj                        none
% 15.65/2.48  --large_theory_mode                     true
% 15.65/2.48  --prolific_symb_bound                   200
% 15.65/2.48  --lt_threshold                          2000
% 15.65/2.48  --clause_weak_htbl                      true
% 15.65/2.48  --gc_record_bc_elim                     false
% 15.65/2.48  
% 15.65/2.48  ------ Preprocessing Options
% 15.65/2.48  
% 15.65/2.48  --preprocessing_flag                    true
% 15.65/2.48  --time_out_prep_mult                    0.1
% 15.65/2.48  --splitting_mode                        input
% 15.65/2.48  --splitting_grd                         true
% 15.65/2.48  --splitting_cvd                         false
% 15.65/2.48  --splitting_cvd_svl                     false
% 15.65/2.48  --splitting_nvd                         32
% 15.65/2.48  --sub_typing                            true
% 15.65/2.48  --prep_gs_sim                           true
% 15.65/2.48  --prep_unflatten                        true
% 15.65/2.48  --prep_res_sim                          true
% 15.65/2.48  --prep_upred                            true
% 15.65/2.48  --prep_sem_filter                       exhaustive
% 15.65/2.48  --prep_sem_filter_out                   false
% 15.65/2.48  --pred_elim                             true
% 15.65/2.48  --res_sim_input                         true
% 15.65/2.48  --eq_ax_congr_red                       true
% 15.65/2.48  --pure_diseq_elim                       true
% 15.65/2.48  --brand_transform                       false
% 15.65/2.48  --non_eq_to_eq                          false
% 15.65/2.48  --prep_def_merge                        true
% 15.65/2.48  --prep_def_merge_prop_impl              false
% 15.65/2.48  --prep_def_merge_mbd                    true
% 15.65/2.48  --prep_def_merge_tr_red                 false
% 15.65/2.48  --prep_def_merge_tr_cl                  false
% 15.65/2.48  --smt_preprocessing                     true
% 15.65/2.48  --smt_ac_axioms                         fast
% 15.65/2.48  --preprocessed_out                      false
% 15.65/2.48  --preprocessed_stats                    false
% 15.65/2.48  
% 15.65/2.48  ------ Abstraction refinement Options
% 15.65/2.48  
% 15.65/2.48  --abstr_ref                             []
% 15.65/2.48  --abstr_ref_prep                        false
% 15.65/2.48  --abstr_ref_until_sat                   false
% 15.65/2.48  --abstr_ref_sig_restrict                funpre
% 15.65/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.65/2.48  --abstr_ref_under                       []
% 15.65/2.48  
% 15.65/2.48  ------ SAT Options
% 15.65/2.48  
% 15.65/2.48  --sat_mode                              false
% 15.65/2.48  --sat_fm_restart_options                ""
% 15.65/2.48  --sat_gr_def                            false
% 15.65/2.48  --sat_epr_types                         true
% 15.65/2.48  --sat_non_cyclic_types                  false
% 15.65/2.48  --sat_finite_models                     false
% 15.65/2.48  --sat_fm_lemmas                         false
% 15.65/2.48  --sat_fm_prep                           false
% 15.65/2.48  --sat_fm_uc_incr                        true
% 15.65/2.48  --sat_out_model                         small
% 15.65/2.48  --sat_out_clauses                       false
% 15.65/2.48  
% 15.65/2.48  ------ QBF Options
% 15.65/2.48  
% 15.65/2.48  --qbf_mode                              false
% 15.65/2.48  --qbf_elim_univ                         false
% 15.65/2.48  --qbf_dom_inst                          none
% 15.65/2.48  --qbf_dom_pre_inst                      false
% 15.65/2.48  --qbf_sk_in                             false
% 15.65/2.48  --qbf_pred_elim                         true
% 15.65/2.48  --qbf_split                             512
% 15.65/2.48  
% 15.65/2.48  ------ BMC1 Options
% 15.65/2.48  
% 15.65/2.48  --bmc1_incremental                      false
% 15.65/2.48  --bmc1_axioms                           reachable_all
% 15.65/2.48  --bmc1_min_bound                        0
% 15.65/2.48  --bmc1_max_bound                        -1
% 15.65/2.48  --bmc1_max_bound_default                -1
% 15.65/2.48  --bmc1_symbol_reachability              true
% 15.65/2.48  --bmc1_property_lemmas                  false
% 15.65/2.48  --bmc1_k_induction                      false
% 15.65/2.48  --bmc1_non_equiv_states                 false
% 15.65/2.48  --bmc1_deadlock                         false
% 15.65/2.48  --bmc1_ucm                              false
% 15.65/2.48  --bmc1_add_unsat_core                   none
% 15.65/2.48  --bmc1_unsat_core_children              false
% 15.65/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.65/2.48  --bmc1_out_stat                         full
% 15.65/2.48  --bmc1_ground_init                      false
% 15.65/2.48  --bmc1_pre_inst_next_state              false
% 15.65/2.48  --bmc1_pre_inst_state                   false
% 15.65/2.48  --bmc1_pre_inst_reach_state             false
% 15.65/2.48  --bmc1_out_unsat_core                   false
% 15.65/2.48  --bmc1_aig_witness_out                  false
% 15.65/2.48  --bmc1_verbose                          false
% 15.65/2.48  --bmc1_dump_clauses_tptp                false
% 15.65/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.65/2.48  --bmc1_dump_file                        -
% 15.65/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.65/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.65/2.48  --bmc1_ucm_extend_mode                  1
% 15.65/2.48  --bmc1_ucm_init_mode                    2
% 15.65/2.48  --bmc1_ucm_cone_mode                    none
% 15.65/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.65/2.48  --bmc1_ucm_relax_model                  4
% 15.65/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.65/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.65/2.48  --bmc1_ucm_layered_model                none
% 15.65/2.48  --bmc1_ucm_max_lemma_size               10
% 15.65/2.48  
% 15.65/2.48  ------ AIG Options
% 15.65/2.48  
% 15.65/2.48  --aig_mode                              false
% 15.65/2.48  
% 15.65/2.48  ------ Instantiation Options
% 15.65/2.48  
% 15.65/2.48  --instantiation_flag                    true
% 15.65/2.48  --inst_sos_flag                         true
% 15.65/2.48  --inst_sos_phase                        true
% 15.65/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.65/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.65/2.48  --inst_lit_sel_side                     none
% 15.65/2.48  --inst_solver_per_active                1400
% 15.65/2.48  --inst_solver_calls_frac                1.
% 15.65/2.48  --inst_passive_queue_type               priority_queues
% 15.65/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.65/2.48  --inst_passive_queues_freq              [25;2]
% 15.65/2.48  --inst_dismatching                      true
% 15.65/2.48  --inst_eager_unprocessed_to_passive     true
% 15.65/2.48  --inst_prop_sim_given                   true
% 15.65/2.48  --inst_prop_sim_new                     false
% 15.65/2.48  --inst_subs_new                         false
% 15.65/2.48  --inst_eq_res_simp                      false
% 15.65/2.48  --inst_subs_given                       false
% 15.65/2.48  --inst_orphan_elimination               true
% 15.65/2.48  --inst_learning_loop_flag               true
% 15.65/2.48  --inst_learning_start                   3000
% 15.65/2.48  --inst_learning_factor                  2
% 15.65/2.48  --inst_start_prop_sim_after_learn       3
% 15.65/2.48  --inst_sel_renew                        solver
% 15.65/2.48  --inst_lit_activity_flag                true
% 15.65/2.48  --inst_restr_to_given                   false
% 15.65/2.48  --inst_activity_threshold               500
% 15.65/2.48  --inst_out_proof                        true
% 15.65/2.48  
% 15.65/2.48  ------ Resolution Options
% 15.65/2.48  
% 15.65/2.48  --resolution_flag                       false
% 15.65/2.48  --res_lit_sel                           adaptive
% 15.65/2.48  --res_lit_sel_side                      none
% 15.65/2.48  --res_ordering                          kbo
% 15.65/2.48  --res_to_prop_solver                    active
% 15.65/2.48  --res_prop_simpl_new                    false
% 15.65/2.48  --res_prop_simpl_given                  true
% 15.65/2.48  --res_passive_queue_type                priority_queues
% 15.65/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.65/2.48  --res_passive_queues_freq               [15;5]
% 15.65/2.48  --res_forward_subs                      full
% 15.65/2.48  --res_backward_subs                     full
% 15.65/2.48  --res_forward_subs_resolution           true
% 15.65/2.48  --res_backward_subs_resolution          true
% 15.65/2.48  --res_orphan_elimination                true
% 15.65/2.48  --res_time_limit                        2.
% 15.65/2.48  --res_out_proof                         true
% 15.65/2.48  
% 15.65/2.48  ------ Superposition Options
% 15.65/2.48  
% 15.65/2.48  --superposition_flag                    true
% 15.65/2.48  --sup_passive_queue_type                priority_queues
% 15.65/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.65/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.65/2.48  --demod_completeness_check              fast
% 15.65/2.48  --demod_use_ground                      true
% 15.65/2.48  --sup_to_prop_solver                    passive
% 15.65/2.48  --sup_prop_simpl_new                    true
% 15.65/2.48  --sup_prop_simpl_given                  true
% 15.65/2.48  --sup_fun_splitting                     true
% 15.65/2.48  --sup_smt_interval                      50000
% 15.65/2.48  
% 15.65/2.48  ------ Superposition Simplification Setup
% 15.65/2.48  
% 15.65/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.65/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.65/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.65/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.65/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.65/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.65/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.65/2.48  --sup_immed_triv                        [TrivRules]
% 15.65/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.65/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.65/2.48  --sup_immed_bw_main                     []
% 15.65/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.65/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.65/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.65/2.48  --sup_input_bw                          []
% 15.65/2.48  
% 15.65/2.48  ------ Combination Options
% 15.65/2.48  
% 15.65/2.48  --comb_res_mult                         3
% 15.65/2.48  --comb_sup_mult                         2
% 15.65/2.48  --comb_inst_mult                        10
% 15.65/2.48  
% 15.65/2.48  ------ Debug Options
% 15.65/2.48  
% 15.65/2.48  --dbg_backtrace                         false
% 15.65/2.48  --dbg_dump_prop_clauses                 false
% 15.65/2.48  --dbg_dump_prop_clauses_file            -
% 15.65/2.48  --dbg_out_stat                          false
% 15.65/2.48  
% 15.65/2.48  
% 15.65/2.48  
% 15.65/2.48  
% 15.65/2.48  ------ Proving...
% 15.65/2.48  
% 15.65/2.48  
% 15.65/2.48  % SZS status Theorem for theBenchmark.p
% 15.65/2.48  
% 15.65/2.48   Resolution empty clause
% 15.65/2.48  
% 15.65/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.65/2.48  
% 15.65/2.48  fof(f13,axiom,(
% 15.65/2.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f51,plain,(
% 15.65/2.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 15.65/2.48    inference(cnf_transformation,[],[f13])).
% 15.65/2.48  
% 15.65/2.48  fof(f1,axiom,(
% 15.65/2.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f31,plain,(
% 15.65/2.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.65/2.48    inference(nnf_transformation,[],[f1])).
% 15.65/2.48  
% 15.65/2.48  fof(f32,plain,(
% 15.65/2.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.65/2.48    inference(flattening,[],[f31])).
% 15.65/2.48  
% 15.65/2.48  fof(f36,plain,(
% 15.65/2.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.65/2.48    inference(cnf_transformation,[],[f32])).
% 15.65/2.48  
% 15.65/2.48  fof(f63,plain,(
% 15.65/2.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.65/2.48    inference(equality_resolution,[],[f36])).
% 15.65/2.48  
% 15.65/2.48  fof(f17,conjecture,(
% 15.65/2.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f18,negated_conjecture,(
% 15.65/2.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 15.65/2.48    inference(negated_conjecture,[],[f17])).
% 15.65/2.48  
% 15.65/2.48  fof(f29,plain,(
% 15.65/2.48    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 15.65/2.48    inference(ennf_transformation,[],[f18])).
% 15.65/2.48  
% 15.65/2.48  fof(f30,plain,(
% 15.65/2.48    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 15.65/2.48    inference(flattening,[],[f29])).
% 15.65/2.48  
% 15.65/2.48  fof(f33,plain,(
% 15.65/2.48    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 15.65/2.48    introduced(choice_axiom,[])).
% 15.65/2.48  
% 15.65/2.48  fof(f34,plain,(
% 15.65/2.48    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 15.65/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).
% 15.65/2.48  
% 15.65/2.48  fof(f58,plain,(
% 15.65/2.48    r1_tarski(sK0,k1_relat_1(sK1))),
% 15.65/2.48    inference(cnf_transformation,[],[f34])).
% 15.65/2.48  
% 15.65/2.48  fof(f3,axiom,(
% 15.65/2.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f39,plain,(
% 15.65/2.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f3])).
% 15.65/2.48  
% 15.65/2.48  fof(f2,axiom,(
% 15.65/2.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f19,plain,(
% 15.65/2.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 15.65/2.48    inference(ennf_transformation,[],[f2])).
% 15.65/2.48  
% 15.65/2.48  fof(f20,plain,(
% 15.65/2.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 15.65/2.48    inference(flattening,[],[f19])).
% 15.65/2.48  
% 15.65/2.48  fof(f38,plain,(
% 15.65/2.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f20])).
% 15.65/2.48  
% 15.65/2.48  fof(f6,axiom,(
% 15.65/2.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f21,plain,(
% 15.65/2.48    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 15.65/2.48    inference(ennf_transformation,[],[f6])).
% 15.65/2.48  
% 15.65/2.48  fof(f43,plain,(
% 15.65/2.48    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 15.65/2.48    inference(cnf_transformation,[],[f21])).
% 15.65/2.48  
% 15.65/2.48  fof(f7,axiom,(
% 15.65/2.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f22,plain,(
% 15.65/2.48    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 15.65/2.48    inference(ennf_transformation,[],[f7])).
% 15.65/2.48  
% 15.65/2.48  fof(f44,plain,(
% 15.65/2.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f22])).
% 15.65/2.48  
% 15.65/2.48  fof(f10,axiom,(
% 15.65/2.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f23,plain,(
% 15.65/2.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.65/2.48    inference(ennf_transformation,[],[f10])).
% 15.65/2.48  
% 15.65/2.48  fof(f47,plain,(
% 15.65/2.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f23])).
% 15.65/2.48  
% 15.65/2.48  fof(f11,axiom,(
% 15.65/2.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f48,plain,(
% 15.65/2.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 15.65/2.48    inference(cnf_transformation,[],[f11])).
% 15.65/2.48  
% 15.65/2.48  fof(f16,axiom,(
% 15.65/2.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f55,plain,(
% 15.65/2.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 15.65/2.48    inference(cnf_transformation,[],[f16])).
% 15.65/2.48  
% 15.65/2.48  fof(f5,axiom,(
% 15.65/2.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f41,plain,(
% 15.65/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f5])).
% 15.65/2.48  
% 15.65/2.48  fof(f62,plain,(
% 15.65/2.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.65/2.48    inference(definition_unfolding,[],[f55,f41])).
% 15.65/2.48  
% 15.65/2.48  fof(f9,axiom,(
% 15.65/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f46,plain,(
% 15.65/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.65/2.48    inference(cnf_transformation,[],[f9])).
% 15.65/2.48  
% 15.65/2.48  fof(f8,axiom,(
% 15.65/2.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f45,plain,(
% 15.65/2.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f8])).
% 15.65/2.48  
% 15.65/2.48  fof(f61,plain,(
% 15.65/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 15.65/2.48    inference(definition_unfolding,[],[f46,f41,f45])).
% 15.65/2.48  
% 15.65/2.48  fof(f4,axiom,(
% 15.65/2.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f40,plain,(
% 15.65/2.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.65/2.48    inference(cnf_transformation,[],[f4])).
% 15.65/2.48  
% 15.65/2.48  fof(f15,axiom,(
% 15.65/2.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))))))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f27,plain,(
% 15.65/2.48    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 15.65/2.48    inference(ennf_transformation,[],[f15])).
% 15.65/2.48  
% 15.65/2.48  fof(f28,plain,(
% 15.65/2.48    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 15.65/2.48    inference(flattening,[],[f27])).
% 15.65/2.48  
% 15.65/2.48  fof(f54,plain,(
% 15.65/2.48    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f28])).
% 15.65/2.48  
% 15.65/2.48  fof(f49,plain,(
% 15.65/2.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 15.65/2.48    inference(cnf_transformation,[],[f11])).
% 15.65/2.48  
% 15.65/2.48  fof(f60,plain,(
% 15.65/2.48    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 15.65/2.48    inference(cnf_transformation,[],[f34])).
% 15.65/2.48  
% 15.65/2.48  fof(f37,plain,(
% 15.65/2.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f32])).
% 15.65/2.48  
% 15.65/2.48  fof(f14,axiom,(
% 15.65/2.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f25,plain,(
% 15.65/2.48    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.65/2.48    inference(ennf_transformation,[],[f14])).
% 15.65/2.48  
% 15.65/2.48  fof(f26,plain,(
% 15.65/2.48    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.65/2.48    inference(flattening,[],[f25])).
% 15.65/2.48  
% 15.65/2.48  fof(f53,plain,(
% 15.65/2.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f26])).
% 15.65/2.48  
% 15.65/2.48  fof(f59,plain,(
% 15.65/2.48    v2_funct_1(sK1)),
% 15.65/2.48    inference(cnf_transformation,[],[f34])).
% 15.65/2.48  
% 15.65/2.48  fof(f56,plain,(
% 15.65/2.48    v1_relat_1(sK1)),
% 15.65/2.48    inference(cnf_transformation,[],[f34])).
% 15.65/2.48  
% 15.65/2.48  fof(f57,plain,(
% 15.65/2.48    v1_funct_1(sK1)),
% 15.65/2.48    inference(cnf_transformation,[],[f34])).
% 15.65/2.48  
% 15.65/2.48  fof(f12,axiom,(
% 15.65/2.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 15.65/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.65/2.48  
% 15.65/2.48  fof(f24,plain,(
% 15.65/2.48    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 15.65/2.48    inference(ennf_transformation,[],[f12])).
% 15.65/2.48  
% 15.65/2.48  fof(f50,plain,(
% 15.65/2.48    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 15.65/2.48    inference(cnf_transformation,[],[f24])).
% 15.65/2.48  
% 15.65/2.48  cnf(c_15,plain,
% 15.65/2.48      ( v1_relat_1(k6_relat_1(X0)) ),
% 15.65/2.48      inference(cnf_transformation,[],[f51]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_548,plain,
% 15.65/2.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f63]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_553,plain,
% 15.65/2.48      ( r1_tarski(X0,X0) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_21,negated_conjecture,
% 15.65/2.48      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 15.65/2.48      inference(cnf_transformation,[],[f58]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_546,plain,
% 15.65/2.48      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_4,plain,
% 15.65/2.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.65/2.48      inference(cnf_transformation,[],[f39]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_551,plain,
% 15.65/2.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_3,plain,
% 15.65/2.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 15.65/2.48      inference(cnf_transformation,[],[f38]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_552,plain,
% 15.65/2.48      ( r1_tarski(X0,X1) != iProver_top
% 15.65/2.48      | r1_tarski(X1,X2) != iProver_top
% 15.65/2.48      | r1_tarski(X0,X2) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_2580,plain,
% 15.65/2.48      ( r1_tarski(X0,X1) != iProver_top
% 15.65/2.48      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_551,c_552]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_6796,plain,
% 15.65/2.48      ( r1_tarski(X0,X1) != iProver_top
% 15.65/2.48      | r1_tarski(X1,X2) != iProver_top
% 15.65/2.48      | r1_tarski(k4_xboole_0(X0,X3),X2) = iProver_top ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_2580,c_552]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_49852,plain,
% 15.65/2.48      ( r1_tarski(k4_xboole_0(sK0,X0),X1) = iProver_top
% 15.65/2.48      | r1_tarski(k1_relat_1(sK1),X1) != iProver_top ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_546,c_6796]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_6,plain,
% 15.65/2.48      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 15.65/2.48      inference(cnf_transformation,[],[f43]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_8,plain,
% 15.65/2.48      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 15.65/2.48      inference(cnf_transformation,[],[f44]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_212,plain,
% 15.65/2.48      ( ~ r1_tarski(X0,X1)
% 15.65/2.48      | X0 != X2
% 15.65/2.48      | k4_xboole_0(X3,X1) != X2
% 15.65/2.48      | k1_xboole_0 = X2 ),
% 15.65/2.48      inference(resolution_lifted,[status(thm)],[c_6,c_8]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_213,plain,
% 15.65/2.48      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1) | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 15.65/2.48      inference(unflattening,[status(thm)],[c_212]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_544,plain,
% 15.65/2.48      ( k1_xboole_0 = k4_xboole_0(X0,X1)
% 15.65/2.48      | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_50455,plain,
% 15.65/2.48      ( k4_xboole_0(sK0,X0) = k1_xboole_0
% 15.65/2.48      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_49852,c_544]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_51206,plain,
% 15.65/2.48      ( k4_xboole_0(sK0,k1_relat_1(sK1)) = k1_xboole_0 ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_553,c_50455]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_10,plain,
% 15.65/2.48      ( ~ v1_relat_1(X0)
% 15.65/2.48      | ~ v1_relat_1(X1)
% 15.65/2.48      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 15.65/2.48      inference(cnf_transformation,[],[f47]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_550,plain,
% 15.65/2.48      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 15.65/2.48      | v1_relat_1(X1) != iProver_top
% 15.65/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_2379,plain,
% 15.65/2.48      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 15.65/2.48      | v1_relat_1(X1) != iProver_top ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_548,c_550]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_7533,plain,
% 15.65/2.48      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_548,c_2379]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_12,plain,
% 15.65/2.48      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 15.65/2.48      inference(cnf_transformation,[],[f48]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_7538,plain,
% 15.65/2.48      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 15.65/2.48      inference(demodulation,[status(thm)],[c_7533,c_12]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_18,plain,
% 15.65/2.48      ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 15.65/2.48      inference(cnf_transformation,[],[f62]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_9,plain,
% 15.65/2.48      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 15.65/2.48      inference(cnf_transformation,[],[f61]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_555,plain,
% 15.65/2.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 15.65/2.48      inference(light_normalisation,[status(thm)],[c_18,c_9]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_1746,plain,
% 15.65/2.48      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_555,c_12]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_7670,plain,
% 15.65/2.48      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
% 15.65/2.48      inference(demodulation,[status(thm)],[c_7538,c_1746]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_23872,plain,
% 15.65/2.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
% 15.65/2.48      inference(demodulation,[status(thm)],[c_7670,c_9]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_52740,plain,
% 15.65/2.48      ( k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = k4_xboole_0(sK0,k1_xboole_0) ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_51206,c_23872]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_5,plain,
% 15.65/2.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.65/2.48      inference(cnf_transformation,[],[f40]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_52777,plain,
% 15.65/2.48      ( k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = sK0 ),
% 15.65/2.48      inference(demodulation,[status(thm)],[c_52740,c_5]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_17,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1)))
% 15.65/2.48      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X2))
% 15.65/2.48      | ~ v1_relat_1(X0)
% 15.65/2.48      | ~ v1_relat_1(X2) ),
% 15.65/2.48      inference(cnf_transformation,[],[f54]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_547,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1))) = iProver_top
% 15.65/2.48      | r1_tarski(k2_relat_1(X0),k1_relat_1(X2)) != iProver_top
% 15.65/2.48      | v1_relat_1(X0) != iProver_top
% 15.65/2.48      | v1_relat_1(X2) != iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_53580,plain,
% 15.65/2.48      ( r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X0)) != iProver_top
% 15.65/2.48      | r1_tarski(sK0,k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k9_relat_1(X0,sK0))) = iProver_top
% 15.65/2.48      | v1_relat_1(X0) != iProver_top
% 15.65/2.48      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_52777,c_547]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_11,plain,
% 15.65/2.48      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 15.65/2.48      inference(cnf_transformation,[],[f49]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_53682,plain,
% 15.65/2.48      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) != iProver_top
% 15.65/2.48      | r1_tarski(sK0,k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k9_relat_1(X0,sK0))) = iProver_top
% 15.65/2.48      | v1_relat_1(X0) != iProver_top
% 15.65/2.48      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
% 15.65/2.48      inference(demodulation,[status(thm)],[c_53580,c_11]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_19,negated_conjecture,
% 15.65/2.48      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 15.65/2.48      inference(cnf_transformation,[],[f60]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_0,plain,
% 15.65/2.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.65/2.48      inference(cnf_transformation,[],[f37]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_572,plain,
% 15.65/2.48      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 15.65/2.48      | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 15.65/2.48      | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 15.65/2.48      inference(instantiation,[status(thm)],[c_0]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_573,plain,
% 15.65/2.48      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
% 15.65/2.48      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != iProver_top
% 15.65/2.48      | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_16,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 15.65/2.48      | ~ v2_funct_1(X0)
% 15.65/2.48      | ~ v1_funct_1(X0)
% 15.65/2.48      | ~ v1_relat_1(X0) ),
% 15.65/2.48      inference(cnf_transformation,[],[f53]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_20,negated_conjecture,
% 15.65/2.48      ( v2_funct_1(sK1) ),
% 15.65/2.48      inference(cnf_transformation,[],[f59]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_227,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 15.65/2.48      | ~ v1_funct_1(X0)
% 15.65/2.48      | ~ v1_relat_1(X0)
% 15.65/2.48      | sK1 != X0 ),
% 15.65/2.48      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_228,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
% 15.65/2.48      | ~ v1_funct_1(sK1)
% 15.65/2.48      | ~ v1_relat_1(sK1) ),
% 15.65/2.48      inference(unflattening,[status(thm)],[c_227]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_23,negated_conjecture,
% 15.65/2.48      ( v1_relat_1(sK1) ),
% 15.65/2.48      inference(cnf_transformation,[],[f56]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_22,negated_conjecture,
% 15.65/2.48      ( v1_funct_1(sK1) ),
% 15.65/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_232,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
% 15.65/2.48      inference(global_propositional_subsumption,
% 15.65/2.48                [status(thm)],
% 15.65/2.48                [c_228,c_23,c_22]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_577,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
% 15.65/2.48      inference(instantiation,[status(thm)],[c_232]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_578,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_545,plain,
% 15.65/2.48      ( v1_relat_1(sK1) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_13,plain,
% 15.65/2.48      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 15.65/2.48      inference(cnf_transformation,[],[f50]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_549,plain,
% 15.65/2.48      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 15.65/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_1857,plain,
% 15.65/2.48      ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_545,c_549]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_1940,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 15.65/2.48      | r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),k1_relat_1(sK1)) != iProver_top
% 15.65/2.48      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 15.65/2.48      | v1_relat_1(sK1) != iProver_top ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_1857,c_547]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_1941,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 15.65/2.48      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 15.65/2.48      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 15.65/2.48      | v1_relat_1(sK1) != iProver_top ),
% 15.65/2.48      inference(demodulation,[status(thm)],[c_1940,c_11]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_24,plain,
% 15.65/2.48      ( v1_relat_1(sK1) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_896,plain,
% 15.65/2.48      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 15.65/2.48      inference(instantiation,[status(thm)],[c_1]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_897,plain,
% 15.65/2.48      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top ),
% 15.65/2.48      inference(predicate_to_equality,[status(thm)],[c_896]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_1946,plain,
% 15.65/2.48      ( v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 15.65/2.48      | r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 15.65/2.48      inference(global_propositional_subsumption,
% 15.65/2.48                [status(thm)],
% 15.65/2.48                [c_1941,c_24,c_897]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_1947,plain,
% 15.65/2.48      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 15.65/2.48      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
% 15.65/2.48      inference(renaming,[status(thm)],[c_1946]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_53615,plain,
% 15.65/2.48      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top
% 15.65/2.48      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_52777,c_1947]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_53744,plain,
% 15.65/2.48      ( v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
% 15.65/2.48      inference(global_propositional_subsumption,
% 15.65/2.48                [status(thm)],
% 15.65/2.48                [c_53682,c_19,c_573,c_578,c_53615]) ).
% 15.65/2.48  
% 15.65/2.48  cnf(c_53748,plain,
% 15.65/2.48      ( $false ),
% 15.65/2.48      inference(superposition,[status(thm)],[c_548,c_53744]) ).
% 15.65/2.48  
% 15.65/2.48  
% 15.65/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.65/2.48  
% 15.65/2.48  ------                               Statistics
% 15.65/2.48  
% 15.65/2.48  ------ General
% 15.65/2.48  
% 15.65/2.48  abstr_ref_over_cycles:                  0
% 15.65/2.48  abstr_ref_under_cycles:                 0
% 15.65/2.48  gc_basic_clause_elim:                   0
% 15.65/2.48  forced_gc_time:                         0
% 15.65/2.48  parsing_time:                           0.007
% 15.65/2.48  unif_index_cands_time:                  0.
% 15.65/2.48  unif_index_add_time:                    0.
% 15.65/2.48  orderings_time:                         0.
% 15.65/2.48  out_proof_time:                         0.012
% 15.65/2.48  total_time:                             1.95
% 15.65/2.48  num_of_symbols:                         48
% 15.65/2.48  num_of_terms:                           58765
% 15.65/2.48  
% 15.65/2.48  ------ Preprocessing
% 15.65/2.48  
% 15.65/2.48  num_of_splits:                          0
% 15.65/2.48  num_of_split_atoms:                     0
% 15.65/2.48  num_of_reused_defs:                     0
% 15.65/2.48  num_eq_ax_congr_red:                    12
% 15.65/2.48  num_of_sem_filtered_clauses:            1
% 15.65/2.48  num_of_subtypes:                        0
% 15.65/2.48  monotx_restored_types:                  0
% 15.65/2.48  sat_num_of_epr_types:                   0
% 15.65/2.48  sat_num_of_non_cyclic_types:            0
% 15.65/2.48  sat_guarded_non_collapsed_types:        0
% 15.65/2.48  num_pure_diseq_elim:                    0
% 15.65/2.48  simp_replaced_by:                       0
% 15.65/2.48  res_preprocessed:                       102
% 15.65/2.48  prep_upred:                             0
% 15.65/2.48  prep_unflattend:                        4
% 15.65/2.48  smt_new_axioms:                         0
% 15.65/2.48  pred_elim_cands:                        2
% 15.65/2.48  pred_elim:                              3
% 15.65/2.48  pred_elim_cl:                           5
% 15.65/2.48  pred_elim_cycles:                       5
% 15.65/2.48  merged_defs:                            0
% 15.65/2.48  merged_defs_ncl:                        0
% 15.65/2.48  bin_hyper_res:                          0
% 15.65/2.48  prep_cycles:                            4
% 15.65/2.48  pred_elim_time:                         0.001
% 15.65/2.48  splitting_time:                         0.
% 15.65/2.48  sem_filter_time:                        0.
% 15.65/2.48  monotx_time:                            0.
% 15.65/2.48  subtype_inf_time:                       0.
% 15.65/2.48  
% 15.65/2.48  ------ Problem properties
% 15.65/2.48  
% 15.65/2.48  clauses:                                18
% 15.65/2.48  conjectures:                            3
% 15.65/2.48  epr:                                    4
% 15.65/2.48  horn:                                   18
% 15.65/2.48  ground:                                 3
% 15.65/2.48  unary:                                  12
% 15.65/2.48  binary:                                 2
% 15.65/2.48  lits:                                   29
% 15.65/2.48  lits_eq:                                10
% 15.65/2.48  fd_pure:                                0
% 15.65/2.48  fd_pseudo:                              0
% 15.65/2.48  fd_cond:                                0
% 15.65/2.48  fd_pseudo_cond:                         1
% 15.65/2.48  ac_symbols:                             0
% 15.65/2.48  
% 15.65/2.48  ------ Propositional Solver
% 15.65/2.48  
% 15.65/2.48  prop_solver_calls:                      36
% 15.65/2.48  prop_fast_solver_calls:                 1954
% 15.65/2.48  smt_solver_calls:                       0
% 15.65/2.48  smt_fast_solver_calls:                  0
% 15.65/2.48  prop_num_of_clauses:                    26794
% 15.65/2.48  prop_preprocess_simplified:             32984
% 15.65/2.48  prop_fo_subsumed:                       88
% 15.65/2.48  prop_solver_time:                       0.
% 15.65/2.48  smt_solver_time:                        0.
% 15.65/2.48  smt_fast_solver_time:                   0.
% 15.65/2.48  prop_fast_solver_time:                  0.
% 15.65/2.48  prop_unsat_core_time:                   0.
% 15.65/2.48  
% 15.65/2.48  ------ QBF
% 15.65/2.48  
% 15.65/2.48  qbf_q_res:                              0
% 15.65/2.48  qbf_num_tautologies:                    0
% 15.65/2.48  qbf_prep_cycles:                        0
% 15.65/2.48  
% 15.65/2.48  ------ BMC1
% 15.65/2.48  
% 15.65/2.48  bmc1_current_bound:                     -1
% 15.65/2.48  bmc1_last_solved_bound:                 -1
% 15.65/2.48  bmc1_unsat_core_size:                   -1
% 15.65/2.48  bmc1_unsat_core_parents_size:           -1
% 15.65/2.48  bmc1_merge_next_fun:                    0
% 15.65/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.65/2.48  
% 15.65/2.48  ------ Instantiation
% 15.65/2.48  
% 15.65/2.48  inst_num_of_clauses:                    5728
% 15.65/2.48  inst_num_in_passive:                    1190
% 15.65/2.48  inst_num_in_active:                     2384
% 15.65/2.48  inst_num_in_unprocessed:                2155
% 15.65/2.48  inst_num_of_loops:                      2500
% 15.65/2.48  inst_num_of_learning_restarts:          0
% 15.65/2.48  inst_num_moves_active_passive:          111
% 15.65/2.48  inst_lit_activity:                      0
% 15.65/2.48  inst_lit_activity_moves:                0
% 15.65/2.48  inst_num_tautologies:                   0
% 15.65/2.48  inst_num_prop_implied:                  0
% 15.65/2.48  inst_num_existing_simplified:           0
% 15.65/2.48  inst_num_eq_res_simplified:             0
% 15.65/2.48  inst_num_child_elim:                    0
% 15.65/2.48  inst_num_of_dismatching_blockings:      2958
% 15.65/2.48  inst_num_of_non_proper_insts:           7623
% 15.65/2.48  inst_num_of_duplicates:                 0
% 15.65/2.48  inst_inst_num_from_inst_to_res:         0
% 15.65/2.48  inst_dismatching_checking_time:         0.
% 15.65/2.48  
% 15.65/2.48  ------ Resolution
% 15.65/2.48  
% 15.65/2.48  res_num_of_clauses:                     0
% 15.65/2.48  res_num_in_passive:                     0
% 15.65/2.48  res_num_in_active:                      0
% 15.65/2.48  res_num_of_loops:                       106
% 15.65/2.48  res_forward_subset_subsumed:            1373
% 15.65/2.48  res_backward_subset_subsumed:           2
% 15.65/2.48  res_forward_subsumed:                   0
% 15.65/2.48  res_backward_subsumed:                  0
% 15.65/2.48  res_forward_subsumption_resolution:     0
% 15.65/2.48  res_backward_subsumption_resolution:    0
% 15.65/2.48  res_clause_to_clause_subsumption:       23122
% 15.65/2.48  res_orphan_elimination:                 0
% 15.65/2.48  res_tautology_del:                      762
% 15.65/2.48  res_num_eq_res_simplified:              0
% 15.65/2.48  res_num_sel_changes:                    0
% 15.65/2.48  res_moves_from_active_to_pass:          0
% 15.65/2.48  
% 15.65/2.48  ------ Superposition
% 15.65/2.48  
% 15.65/2.48  sup_time_total:                         0.
% 15.65/2.48  sup_time_generating:                    0.
% 15.65/2.48  sup_time_sim_full:                      0.
% 15.65/2.48  sup_time_sim_immed:                     0.
% 15.65/2.48  
% 15.65/2.48  sup_num_of_clauses:                     3001
% 15.65/2.48  sup_num_in_active:                      367
% 15.65/2.48  sup_num_in_passive:                     2634
% 15.65/2.48  sup_num_of_loops:                       499
% 15.65/2.48  sup_fw_superposition:                   3931
% 15.65/2.48  sup_bw_superposition:                   2879
% 15.65/2.48  sup_immediate_simplified:               2511
% 15.65/2.48  sup_given_eliminated:                   7
% 15.65/2.48  comparisons_done:                       0
% 15.65/2.48  comparisons_avoided:                    0
% 15.65/2.48  
% 15.65/2.48  ------ Simplifications
% 15.65/2.48  
% 15.65/2.48  
% 15.65/2.48  sim_fw_subset_subsumed:                 563
% 15.65/2.48  sim_bw_subset_subsumed:                 102
% 15.65/2.48  sim_fw_subsumed:                        582
% 15.65/2.48  sim_bw_subsumed:                        141
% 15.65/2.48  sim_fw_subsumption_res:                 0
% 15.65/2.48  sim_bw_subsumption_res:                 0
% 15.65/2.48  sim_tautology_del:                      74
% 15.65/2.48  sim_eq_tautology_del:                   393
% 15.65/2.48  sim_eq_res_simp:                        0
% 15.65/2.48  sim_fw_demodulated:                     1585
% 15.65/2.48  sim_bw_demodulated:                     42
% 15.65/2.48  sim_light_normalised:                   1373
% 15.65/2.48  sim_joinable_taut:                      0
% 15.65/2.48  sim_joinable_simp:                      0
% 15.65/2.48  sim_ac_normalised:                      0
% 15.65/2.48  sim_smt_subsumption:                    0
% 15.65/2.48  
%------------------------------------------------------------------------------
