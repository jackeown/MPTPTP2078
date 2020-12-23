%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:16 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 159 expanded)
%              Number of clauses        :   56 (  72 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 ( 342 expanded)
%              Number of equality atoms :  102 ( 155 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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

fof(f30,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29,f28])).

fof(f49,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_499,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_502,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_505,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1068,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_502,c_505])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1073,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1068,c_10,c_11])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_504,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1596,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_504])).

cnf(c_29,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2793,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_29])).

cnf(c_2794,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2793])).

cnf(c_6,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_507,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1403,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_507])).

cnf(c_1415,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1403,c_29])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_511,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1929,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1415,c_511])).

cnf(c_3273,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_1929])).

cnf(c_22782,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_499,c_3273])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_506,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1613,plain,
    ( k10_relat_1(k6_relat_1(X0),k3_xboole_0(k2_relat_1(k6_relat_1(X0)),X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_502,c_506])).

cnf(c_1618,plain,
    ( k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1613,c_10])).

cnf(c_15,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_500,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1735,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),k3_xboole_0(X0,X1)) = iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_500])).

cnf(c_12,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_32,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3289,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1735,c_29,c_32])).

cnf(c_3299,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3289])).

cnf(c_24666,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22782,c_3299])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_508,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1328,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_502,c_508])).

cnf(c_1333,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1328,c_10,c_11])).

cnf(c_24755,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24666,c_1333])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_509,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_954,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_509])).

cnf(c_1928,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_511])).

cnf(c_28716,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_24755,c_1928])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_497,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_501,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1207,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_497,c_501])).

cnf(c_16,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2414,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) != k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1207,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28716,c_2414])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 8.08/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.08/1.49  
% 8.08/1.49  ------  iProver source info
% 8.08/1.49  
% 8.08/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.08/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.08/1.49  git: non_committed_changes: false
% 8.08/1.49  git: last_make_outside_of_git: false
% 8.08/1.49  
% 8.08/1.49  ------ 
% 8.08/1.49  
% 8.08/1.49  ------ Input Options
% 8.08/1.49  
% 8.08/1.49  --out_options                           all
% 8.08/1.49  --tptp_safe_out                         true
% 8.08/1.49  --problem_path                          ""
% 8.08/1.49  --include_path                          ""
% 8.08/1.49  --clausifier                            res/vclausify_rel
% 8.08/1.49  --clausifier_options                    --mode clausify
% 8.08/1.49  --stdin                                 false
% 8.08/1.49  --stats_out                             sel
% 8.08/1.49  
% 8.08/1.49  ------ General Options
% 8.08/1.49  
% 8.08/1.49  --fof                                   false
% 8.08/1.49  --time_out_real                         604.99
% 8.08/1.49  --time_out_virtual                      -1.
% 8.08/1.49  --symbol_type_check                     false
% 8.08/1.49  --clausify_out                          false
% 8.08/1.49  --sig_cnt_out                           false
% 8.08/1.49  --trig_cnt_out                          false
% 8.08/1.49  --trig_cnt_out_tolerance                1.
% 8.08/1.49  --trig_cnt_out_sk_spl                   false
% 8.08/1.49  --abstr_cl_out                          false
% 8.08/1.49  
% 8.08/1.49  ------ Global Options
% 8.08/1.49  
% 8.08/1.49  --schedule                              none
% 8.08/1.49  --add_important_lit                     false
% 8.08/1.49  --prop_solver_per_cl                    1000
% 8.08/1.49  --min_unsat_core                        false
% 8.08/1.49  --soft_assumptions                      false
% 8.08/1.49  --soft_lemma_size                       3
% 8.08/1.49  --prop_impl_unit_size                   0
% 8.08/1.49  --prop_impl_unit                        []
% 8.08/1.49  --share_sel_clauses                     true
% 8.08/1.49  --reset_solvers                         false
% 8.08/1.49  --bc_imp_inh                            [conj_cone]
% 8.08/1.49  --conj_cone_tolerance                   3.
% 8.08/1.49  --extra_neg_conj                        none
% 8.08/1.49  --large_theory_mode                     true
% 8.08/1.49  --prolific_symb_bound                   200
% 8.08/1.49  --lt_threshold                          2000
% 8.08/1.49  --clause_weak_htbl                      true
% 8.08/1.49  --gc_record_bc_elim                     false
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing Options
% 8.08/1.49  
% 8.08/1.49  --preprocessing_flag                    true
% 8.08/1.49  --time_out_prep_mult                    0.1
% 8.08/1.49  --splitting_mode                        input
% 8.08/1.49  --splitting_grd                         true
% 8.08/1.49  --splitting_cvd                         false
% 8.08/1.49  --splitting_cvd_svl                     false
% 8.08/1.49  --splitting_nvd                         32
% 8.08/1.49  --sub_typing                            true
% 8.08/1.49  --prep_gs_sim                           false
% 8.08/1.49  --prep_unflatten                        true
% 8.08/1.49  --prep_res_sim                          true
% 8.08/1.49  --prep_upred                            true
% 8.08/1.49  --prep_sem_filter                       exhaustive
% 8.08/1.49  --prep_sem_filter_out                   false
% 8.08/1.49  --pred_elim                             false
% 8.08/1.49  --res_sim_input                         true
% 8.08/1.49  --eq_ax_congr_red                       true
% 8.08/1.49  --pure_diseq_elim                       true
% 8.08/1.49  --brand_transform                       false
% 8.08/1.49  --non_eq_to_eq                          false
% 8.08/1.49  --prep_def_merge                        true
% 8.08/1.49  --prep_def_merge_prop_impl              false
% 8.08/1.49  --prep_def_merge_mbd                    true
% 8.08/1.49  --prep_def_merge_tr_red                 false
% 8.08/1.49  --prep_def_merge_tr_cl                  false
% 8.08/1.49  --smt_preprocessing                     true
% 8.08/1.49  --smt_ac_axioms                         fast
% 8.08/1.49  --preprocessed_out                      false
% 8.08/1.49  --preprocessed_stats                    false
% 8.08/1.49  
% 8.08/1.49  ------ Abstraction refinement Options
% 8.08/1.49  
% 8.08/1.49  --abstr_ref                             []
% 8.08/1.49  --abstr_ref_prep                        false
% 8.08/1.49  --abstr_ref_until_sat                   false
% 8.08/1.49  --abstr_ref_sig_restrict                funpre
% 8.08/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.08/1.49  --abstr_ref_under                       []
% 8.08/1.49  
% 8.08/1.49  ------ SAT Options
% 8.08/1.49  
% 8.08/1.49  --sat_mode                              false
% 8.08/1.49  --sat_fm_restart_options                ""
% 8.08/1.49  --sat_gr_def                            false
% 8.08/1.49  --sat_epr_types                         true
% 8.08/1.49  --sat_non_cyclic_types                  false
% 8.08/1.49  --sat_finite_models                     false
% 8.08/1.49  --sat_fm_lemmas                         false
% 8.08/1.49  --sat_fm_prep                           false
% 8.08/1.49  --sat_fm_uc_incr                        true
% 8.08/1.49  --sat_out_model                         small
% 8.08/1.49  --sat_out_clauses                       false
% 8.08/1.49  
% 8.08/1.49  ------ QBF Options
% 8.08/1.49  
% 8.08/1.49  --qbf_mode                              false
% 8.08/1.49  --qbf_elim_univ                         false
% 8.08/1.49  --qbf_dom_inst                          none
% 8.08/1.49  --qbf_dom_pre_inst                      false
% 8.08/1.49  --qbf_sk_in                             false
% 8.08/1.49  --qbf_pred_elim                         true
% 8.08/1.49  --qbf_split                             512
% 8.08/1.49  
% 8.08/1.49  ------ BMC1 Options
% 8.08/1.49  
% 8.08/1.49  --bmc1_incremental                      false
% 8.08/1.49  --bmc1_axioms                           reachable_all
% 8.08/1.49  --bmc1_min_bound                        0
% 8.08/1.49  --bmc1_max_bound                        -1
% 8.08/1.49  --bmc1_max_bound_default                -1
% 8.08/1.49  --bmc1_symbol_reachability              true
% 8.08/1.49  --bmc1_property_lemmas                  false
% 8.08/1.49  --bmc1_k_induction                      false
% 8.08/1.49  --bmc1_non_equiv_states                 false
% 8.08/1.49  --bmc1_deadlock                         false
% 8.08/1.49  --bmc1_ucm                              false
% 8.08/1.49  --bmc1_add_unsat_core                   none
% 8.08/1.49  --bmc1_unsat_core_children              false
% 8.08/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.08/1.49  --bmc1_out_stat                         full
% 8.08/1.49  --bmc1_ground_init                      false
% 8.08/1.49  --bmc1_pre_inst_next_state              false
% 8.08/1.49  --bmc1_pre_inst_state                   false
% 8.08/1.49  --bmc1_pre_inst_reach_state             false
% 8.08/1.49  --bmc1_out_unsat_core                   false
% 8.08/1.49  --bmc1_aig_witness_out                  false
% 8.08/1.49  --bmc1_verbose                          false
% 8.08/1.49  --bmc1_dump_clauses_tptp                false
% 8.08/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.08/1.49  --bmc1_dump_file                        -
% 8.08/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.08/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.08/1.49  --bmc1_ucm_extend_mode                  1
% 8.08/1.49  --bmc1_ucm_init_mode                    2
% 8.08/1.49  --bmc1_ucm_cone_mode                    none
% 8.08/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.08/1.49  --bmc1_ucm_relax_model                  4
% 8.08/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.08/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.08/1.49  --bmc1_ucm_layered_model                none
% 8.08/1.49  --bmc1_ucm_max_lemma_size               10
% 8.08/1.49  
% 8.08/1.49  ------ AIG Options
% 8.08/1.49  
% 8.08/1.49  --aig_mode                              false
% 8.08/1.49  
% 8.08/1.49  ------ Instantiation Options
% 8.08/1.49  
% 8.08/1.49  --instantiation_flag                    true
% 8.08/1.49  --inst_sos_flag                         false
% 8.08/1.49  --inst_sos_phase                        true
% 8.08/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.08/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.08/1.49  --inst_lit_sel_side                     num_symb
% 8.08/1.49  --inst_solver_per_active                1400
% 8.08/1.49  --inst_solver_calls_frac                1.
% 8.08/1.49  --inst_passive_queue_type               priority_queues
% 8.08/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.08/1.49  --inst_passive_queues_freq              [25;2]
% 8.08/1.49  --inst_dismatching                      true
% 8.08/1.49  --inst_eager_unprocessed_to_passive     true
% 8.08/1.49  --inst_prop_sim_given                   true
% 8.08/1.49  --inst_prop_sim_new                     false
% 8.08/1.49  --inst_subs_new                         false
% 8.08/1.49  --inst_eq_res_simp                      false
% 8.08/1.49  --inst_subs_given                       false
% 8.08/1.49  --inst_orphan_elimination               true
% 8.08/1.49  --inst_learning_loop_flag               true
% 8.08/1.49  --inst_learning_start                   3000
% 8.08/1.49  --inst_learning_factor                  2
% 8.08/1.49  --inst_start_prop_sim_after_learn       3
% 8.08/1.49  --inst_sel_renew                        solver
% 8.08/1.49  --inst_lit_activity_flag                true
% 8.08/1.49  --inst_restr_to_given                   false
% 8.08/1.49  --inst_activity_threshold               500
% 8.08/1.49  --inst_out_proof                        true
% 8.08/1.49  
% 8.08/1.49  ------ Resolution Options
% 8.08/1.49  
% 8.08/1.49  --resolution_flag                       true
% 8.08/1.49  --res_lit_sel                           adaptive
% 8.08/1.49  --res_lit_sel_side                      none
% 8.08/1.49  --res_ordering                          kbo
% 8.08/1.49  --res_to_prop_solver                    active
% 8.08/1.49  --res_prop_simpl_new                    false
% 8.08/1.49  --res_prop_simpl_given                  true
% 8.08/1.49  --res_passive_queue_type                priority_queues
% 8.08/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.08/1.49  --res_passive_queues_freq               [15;5]
% 8.08/1.49  --res_forward_subs                      full
% 8.08/1.49  --res_backward_subs                     full
% 8.08/1.49  --res_forward_subs_resolution           true
% 8.08/1.49  --res_backward_subs_resolution          true
% 8.08/1.49  --res_orphan_elimination                true
% 8.08/1.49  --res_time_limit                        2.
% 8.08/1.49  --res_out_proof                         true
% 8.08/1.49  
% 8.08/1.49  ------ Superposition Options
% 8.08/1.49  
% 8.08/1.49  --superposition_flag                    true
% 8.08/1.49  --sup_passive_queue_type                priority_queues
% 8.08/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.08/1.49  --sup_passive_queues_freq               [1;4]
% 8.08/1.49  --demod_completeness_check              fast
% 8.08/1.49  --demod_use_ground                      true
% 8.08/1.49  --sup_to_prop_solver                    passive
% 8.08/1.49  --sup_prop_simpl_new                    true
% 8.08/1.49  --sup_prop_simpl_given                  true
% 8.08/1.49  --sup_fun_splitting                     false
% 8.08/1.49  --sup_smt_interval                      50000
% 8.08/1.49  
% 8.08/1.49  ------ Superposition Simplification Setup
% 8.08/1.49  
% 8.08/1.49  --sup_indices_passive                   []
% 8.08/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.08/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_full_bw                           [BwDemod]
% 8.08/1.49  --sup_immed_triv                        [TrivRules]
% 8.08/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_immed_bw_main                     []
% 8.08/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.08/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.49  
% 8.08/1.49  ------ Combination Options
% 8.08/1.49  
% 8.08/1.49  --comb_res_mult                         3
% 8.08/1.49  --comb_sup_mult                         2
% 8.08/1.49  --comb_inst_mult                        10
% 8.08/1.49  
% 8.08/1.49  ------ Debug Options
% 8.08/1.49  
% 8.08/1.49  --dbg_backtrace                         false
% 8.08/1.49  --dbg_dump_prop_clauses                 false
% 8.08/1.49  --dbg_dump_prop_clauses_file            -
% 8.08/1.49  --dbg_out_stat                          false
% 8.08/1.49  ------ Parsing...
% 8.08/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  ------ Proving...
% 8.08/1.49  ------ Problem Properties 
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  clauses                                 19
% 8.08/1.49  conjectures                             4
% 8.08/1.49  EPR                                     4
% 8.08/1.49  Horn                                    19
% 8.08/1.49  unary                                   11
% 8.08/1.49  binary                                  5
% 8.08/1.49  lits                                    30
% 8.08/1.49  lits eq                                 9
% 8.08/1.49  fd_pure                                 0
% 8.08/1.49  fd_pseudo                               0
% 8.08/1.49  fd_cond                                 0
% 8.08/1.49  fd_pseudo_cond                          1
% 8.08/1.49  AC symbols                              0
% 8.08/1.49  
% 8.08/1.49  ------ Input Options Time Limit: Unbounded
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ 
% 8.08/1.49  Current options:
% 8.08/1.49  ------ 
% 8.08/1.49  
% 8.08/1.49  ------ Input Options
% 8.08/1.49  
% 8.08/1.49  --out_options                           all
% 8.08/1.49  --tptp_safe_out                         true
% 8.08/1.49  --problem_path                          ""
% 8.08/1.49  --include_path                          ""
% 8.08/1.49  --clausifier                            res/vclausify_rel
% 8.08/1.49  --clausifier_options                    --mode clausify
% 8.08/1.49  --stdin                                 false
% 8.08/1.49  --stats_out                             sel
% 8.08/1.49  
% 8.08/1.49  ------ General Options
% 8.08/1.49  
% 8.08/1.49  --fof                                   false
% 8.08/1.49  --time_out_real                         604.99
% 8.08/1.49  --time_out_virtual                      -1.
% 8.08/1.49  --symbol_type_check                     false
% 8.08/1.49  --clausify_out                          false
% 8.08/1.49  --sig_cnt_out                           false
% 8.08/1.49  --trig_cnt_out                          false
% 8.08/1.49  --trig_cnt_out_tolerance                1.
% 8.08/1.49  --trig_cnt_out_sk_spl                   false
% 8.08/1.49  --abstr_cl_out                          false
% 8.08/1.49  
% 8.08/1.49  ------ Global Options
% 8.08/1.49  
% 8.08/1.49  --schedule                              none
% 8.08/1.49  --add_important_lit                     false
% 8.08/1.49  --prop_solver_per_cl                    1000
% 8.08/1.49  --min_unsat_core                        false
% 8.08/1.49  --soft_assumptions                      false
% 8.08/1.49  --soft_lemma_size                       3
% 8.08/1.49  --prop_impl_unit_size                   0
% 8.08/1.49  --prop_impl_unit                        []
% 8.08/1.49  --share_sel_clauses                     true
% 8.08/1.49  --reset_solvers                         false
% 8.08/1.49  --bc_imp_inh                            [conj_cone]
% 8.08/1.49  --conj_cone_tolerance                   3.
% 8.08/1.49  --extra_neg_conj                        none
% 8.08/1.49  --large_theory_mode                     true
% 8.08/1.49  --prolific_symb_bound                   200
% 8.08/1.49  --lt_threshold                          2000
% 8.08/1.49  --clause_weak_htbl                      true
% 8.08/1.49  --gc_record_bc_elim                     false
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing Options
% 8.08/1.49  
% 8.08/1.49  --preprocessing_flag                    true
% 8.08/1.49  --time_out_prep_mult                    0.1
% 8.08/1.49  --splitting_mode                        input
% 8.08/1.49  --splitting_grd                         true
% 8.08/1.49  --splitting_cvd                         false
% 8.08/1.49  --splitting_cvd_svl                     false
% 8.08/1.49  --splitting_nvd                         32
% 8.08/1.49  --sub_typing                            true
% 8.08/1.49  --prep_gs_sim                           false
% 8.08/1.49  --prep_unflatten                        true
% 8.08/1.49  --prep_res_sim                          true
% 8.08/1.49  --prep_upred                            true
% 8.08/1.49  --prep_sem_filter                       exhaustive
% 8.08/1.49  --prep_sem_filter_out                   false
% 8.08/1.49  --pred_elim                             false
% 8.08/1.49  --res_sim_input                         true
% 8.08/1.49  --eq_ax_congr_red                       true
% 8.08/1.49  --pure_diseq_elim                       true
% 8.08/1.49  --brand_transform                       false
% 8.08/1.49  --non_eq_to_eq                          false
% 8.08/1.49  --prep_def_merge                        true
% 8.08/1.49  --prep_def_merge_prop_impl              false
% 8.08/1.49  --prep_def_merge_mbd                    true
% 8.08/1.49  --prep_def_merge_tr_red                 false
% 8.08/1.49  --prep_def_merge_tr_cl                  false
% 8.08/1.49  --smt_preprocessing                     true
% 8.08/1.49  --smt_ac_axioms                         fast
% 8.08/1.49  --preprocessed_out                      false
% 8.08/1.49  --preprocessed_stats                    false
% 8.08/1.49  
% 8.08/1.49  ------ Abstraction refinement Options
% 8.08/1.49  
% 8.08/1.49  --abstr_ref                             []
% 8.08/1.49  --abstr_ref_prep                        false
% 8.08/1.49  --abstr_ref_until_sat                   false
% 8.08/1.49  --abstr_ref_sig_restrict                funpre
% 8.08/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.08/1.49  --abstr_ref_under                       []
% 8.08/1.49  
% 8.08/1.49  ------ SAT Options
% 8.08/1.49  
% 8.08/1.49  --sat_mode                              false
% 8.08/1.49  --sat_fm_restart_options                ""
% 8.08/1.49  --sat_gr_def                            false
% 8.08/1.49  --sat_epr_types                         true
% 8.08/1.49  --sat_non_cyclic_types                  false
% 8.08/1.49  --sat_finite_models                     false
% 8.08/1.49  --sat_fm_lemmas                         false
% 8.08/1.49  --sat_fm_prep                           false
% 8.08/1.49  --sat_fm_uc_incr                        true
% 8.08/1.49  --sat_out_model                         small
% 8.08/1.49  --sat_out_clauses                       false
% 8.08/1.49  
% 8.08/1.49  ------ QBF Options
% 8.08/1.49  
% 8.08/1.49  --qbf_mode                              false
% 8.08/1.49  --qbf_elim_univ                         false
% 8.08/1.49  --qbf_dom_inst                          none
% 8.08/1.49  --qbf_dom_pre_inst                      false
% 8.08/1.49  --qbf_sk_in                             false
% 8.08/1.49  --qbf_pred_elim                         true
% 8.08/1.49  --qbf_split                             512
% 8.08/1.49  
% 8.08/1.49  ------ BMC1 Options
% 8.08/1.49  
% 8.08/1.49  --bmc1_incremental                      false
% 8.08/1.49  --bmc1_axioms                           reachable_all
% 8.08/1.49  --bmc1_min_bound                        0
% 8.08/1.49  --bmc1_max_bound                        -1
% 8.08/1.49  --bmc1_max_bound_default                -1
% 8.08/1.49  --bmc1_symbol_reachability              true
% 8.08/1.49  --bmc1_property_lemmas                  false
% 8.08/1.49  --bmc1_k_induction                      false
% 8.08/1.49  --bmc1_non_equiv_states                 false
% 8.08/1.49  --bmc1_deadlock                         false
% 8.08/1.49  --bmc1_ucm                              false
% 8.08/1.49  --bmc1_add_unsat_core                   none
% 8.08/1.49  --bmc1_unsat_core_children              false
% 8.08/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.08/1.49  --bmc1_out_stat                         full
% 8.08/1.49  --bmc1_ground_init                      false
% 8.08/1.49  --bmc1_pre_inst_next_state              false
% 8.08/1.49  --bmc1_pre_inst_state                   false
% 8.08/1.49  --bmc1_pre_inst_reach_state             false
% 8.08/1.49  --bmc1_out_unsat_core                   false
% 8.08/1.49  --bmc1_aig_witness_out                  false
% 8.08/1.49  --bmc1_verbose                          false
% 8.08/1.49  --bmc1_dump_clauses_tptp                false
% 8.08/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.08/1.49  --bmc1_dump_file                        -
% 8.08/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.08/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.08/1.49  --bmc1_ucm_extend_mode                  1
% 8.08/1.49  --bmc1_ucm_init_mode                    2
% 8.08/1.49  --bmc1_ucm_cone_mode                    none
% 8.08/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.08/1.49  --bmc1_ucm_relax_model                  4
% 8.08/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.08/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.08/1.49  --bmc1_ucm_layered_model                none
% 8.08/1.49  --bmc1_ucm_max_lemma_size               10
% 8.08/1.49  
% 8.08/1.49  ------ AIG Options
% 8.08/1.49  
% 8.08/1.49  --aig_mode                              false
% 8.08/1.49  
% 8.08/1.49  ------ Instantiation Options
% 8.08/1.49  
% 8.08/1.49  --instantiation_flag                    true
% 8.08/1.49  --inst_sos_flag                         false
% 8.08/1.49  --inst_sos_phase                        true
% 8.08/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.08/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.08/1.49  --inst_lit_sel_side                     num_symb
% 8.08/1.49  --inst_solver_per_active                1400
% 8.08/1.49  --inst_solver_calls_frac                1.
% 8.08/1.49  --inst_passive_queue_type               priority_queues
% 8.08/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.08/1.49  --inst_passive_queues_freq              [25;2]
% 8.08/1.49  --inst_dismatching                      true
% 8.08/1.49  --inst_eager_unprocessed_to_passive     true
% 8.08/1.49  --inst_prop_sim_given                   true
% 8.08/1.49  --inst_prop_sim_new                     false
% 8.08/1.49  --inst_subs_new                         false
% 8.08/1.49  --inst_eq_res_simp                      false
% 8.08/1.49  --inst_subs_given                       false
% 8.08/1.49  --inst_orphan_elimination               true
% 8.08/1.49  --inst_learning_loop_flag               true
% 8.08/1.49  --inst_learning_start                   3000
% 8.08/1.49  --inst_learning_factor                  2
% 8.08/1.49  --inst_start_prop_sim_after_learn       3
% 8.08/1.49  --inst_sel_renew                        solver
% 8.08/1.49  --inst_lit_activity_flag                true
% 8.08/1.49  --inst_restr_to_given                   false
% 8.08/1.49  --inst_activity_threshold               500
% 8.08/1.49  --inst_out_proof                        true
% 8.08/1.49  
% 8.08/1.49  ------ Resolution Options
% 8.08/1.49  
% 8.08/1.49  --resolution_flag                       true
% 8.08/1.49  --res_lit_sel                           adaptive
% 8.08/1.49  --res_lit_sel_side                      none
% 8.08/1.49  --res_ordering                          kbo
% 8.08/1.49  --res_to_prop_solver                    active
% 8.08/1.49  --res_prop_simpl_new                    false
% 8.08/1.49  --res_prop_simpl_given                  true
% 8.08/1.49  --res_passive_queue_type                priority_queues
% 8.08/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.08/1.49  --res_passive_queues_freq               [15;5]
% 8.08/1.49  --res_forward_subs                      full
% 8.08/1.49  --res_backward_subs                     full
% 8.08/1.49  --res_forward_subs_resolution           true
% 8.08/1.49  --res_backward_subs_resolution          true
% 8.08/1.49  --res_orphan_elimination                true
% 8.08/1.49  --res_time_limit                        2.
% 8.08/1.49  --res_out_proof                         true
% 8.08/1.49  
% 8.08/1.49  ------ Superposition Options
% 8.08/1.49  
% 8.08/1.49  --superposition_flag                    true
% 8.08/1.49  --sup_passive_queue_type                priority_queues
% 8.08/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.08/1.49  --sup_passive_queues_freq               [1;4]
% 8.08/1.49  --demod_completeness_check              fast
% 8.08/1.49  --demod_use_ground                      true
% 8.08/1.49  --sup_to_prop_solver                    passive
% 8.08/1.49  --sup_prop_simpl_new                    true
% 8.08/1.49  --sup_prop_simpl_given                  true
% 8.08/1.49  --sup_fun_splitting                     false
% 8.08/1.49  --sup_smt_interval                      50000
% 8.08/1.49  
% 8.08/1.49  ------ Superposition Simplification Setup
% 8.08/1.49  
% 8.08/1.49  --sup_indices_passive                   []
% 8.08/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.08/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_full_bw                           [BwDemod]
% 8.08/1.49  --sup_immed_triv                        [TrivRules]
% 8.08/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_immed_bw_main                     []
% 8.08/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.08/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.49  
% 8.08/1.49  ------ Combination Options
% 8.08/1.49  
% 8.08/1.49  --comb_res_mult                         3
% 8.08/1.49  --comb_sup_mult                         2
% 8.08/1.49  --comb_inst_mult                        10
% 8.08/1.49  
% 8.08/1.49  ------ Debug Options
% 8.08/1.49  
% 8.08/1.49  --dbg_backtrace                         false
% 8.08/1.49  --dbg_dump_prop_clauses                 false
% 8.08/1.49  --dbg_dump_prop_clauses_file            -
% 8.08/1.49  --dbg_out_stat                          false
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  % SZS status Theorem for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  fof(f13,conjecture,(
% 8.08/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f14,negated_conjecture,(
% 8.08/1.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 8.08/1.49    inference(negated_conjecture,[],[f13])).
% 8.08/1.49  
% 8.08/1.49  fof(f24,plain,(
% 8.08/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 8.08/1.49    inference(ennf_transformation,[],[f14])).
% 8.08/1.49  
% 8.08/1.49  fof(f25,plain,(
% 8.08/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 8.08/1.49    inference(flattening,[],[f24])).
% 8.08/1.49  
% 8.08/1.49  fof(f29,plain,(
% 8.08/1.49    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 8.08/1.49    introduced(choice_axiom,[])).
% 8.08/1.49  
% 8.08/1.49  fof(f28,plain,(
% 8.08/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 8.08/1.49    introduced(choice_axiom,[])).
% 8.08/1.49  
% 8.08/1.49  fof(f30,plain,(
% 8.08/1.49    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 8.08/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29,f28])).
% 8.08/1.49  
% 8.08/1.49  fof(f49,plain,(
% 8.08/1.49    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 8.08/1.49    inference(cnf_transformation,[],[f30])).
% 8.08/1.49  
% 8.08/1.49  fof(f10,axiom,(
% 8.08/1.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f43,plain,(
% 8.08/1.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 8.08/1.49    inference(cnf_transformation,[],[f10])).
% 8.08/1.49  
% 8.08/1.49  fof(f7,axiom,(
% 8.08/1.49    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f18,plain,(
% 8.08/1.49    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.08/1.49    inference(ennf_transformation,[],[f7])).
% 8.08/1.49  
% 8.08/1.49  fof(f39,plain,(
% 8.08/1.49    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f18])).
% 8.08/1.49  
% 8.08/1.49  fof(f9,axiom,(
% 8.08/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f42,plain,(
% 8.08/1.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 8.08/1.49    inference(cnf_transformation,[],[f9])).
% 8.08/1.49  
% 8.08/1.49  fof(f41,plain,(
% 8.08/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 8.08/1.49    inference(cnf_transformation,[],[f9])).
% 8.08/1.49  
% 8.08/1.49  fof(f8,axiom,(
% 8.08/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f19,plain,(
% 8.08/1.49    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 8.08/1.49    inference(ennf_transformation,[],[f8])).
% 8.08/1.49  
% 8.08/1.49  fof(f20,plain,(
% 8.08/1.49    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 8.08/1.49    inference(flattening,[],[f19])).
% 8.08/1.49  
% 8.08/1.49  fof(f40,plain,(
% 8.08/1.49    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f20])).
% 8.08/1.49  
% 8.08/1.49  fof(f5,axiom,(
% 8.08/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f16,plain,(
% 8.08/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 8.08/1.49    inference(ennf_transformation,[],[f5])).
% 8.08/1.49  
% 8.08/1.49  fof(f37,plain,(
% 8.08/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f16])).
% 8.08/1.49  
% 8.08/1.49  fof(f2,axiom,(
% 8.08/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f26,plain,(
% 8.08/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.08/1.49    inference(nnf_transformation,[],[f2])).
% 8.08/1.49  
% 8.08/1.49  fof(f27,plain,(
% 8.08/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.08/1.49    inference(flattening,[],[f26])).
% 8.08/1.49  
% 8.08/1.49  fof(f34,plain,(
% 8.08/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f27])).
% 8.08/1.49  
% 8.08/1.49  fof(f1,axiom,(
% 8.08/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f31,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f1])).
% 8.08/1.49  
% 8.08/1.49  fof(f6,axiom,(
% 8.08/1.49    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f17,plain,(
% 8.08/1.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.08/1.49    inference(ennf_transformation,[],[f6])).
% 8.08/1.49  
% 8.08/1.49  fof(f38,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f17])).
% 8.08/1.49  
% 8.08/1.49  fof(f12,axiom,(
% 8.08/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f22,plain,(
% 8.08/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 8.08/1.49    inference(ennf_transformation,[],[f12])).
% 8.08/1.49  
% 8.08/1.49  fof(f23,plain,(
% 8.08/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 8.08/1.49    inference(flattening,[],[f22])).
% 8.08/1.49  
% 8.08/1.49  fof(f46,plain,(
% 8.08/1.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f23])).
% 8.08/1.49  
% 8.08/1.49  fof(f44,plain,(
% 8.08/1.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 8.08/1.49    inference(cnf_transformation,[],[f10])).
% 8.08/1.49  
% 8.08/1.49  fof(f4,axiom,(
% 8.08/1.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f15,plain,(
% 8.08/1.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 8.08/1.49    inference(ennf_transformation,[],[f4])).
% 8.08/1.49  
% 8.08/1.49  fof(f36,plain,(
% 8.08/1.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f15])).
% 8.08/1.49  
% 8.08/1.49  fof(f3,axiom,(
% 8.08/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f35,plain,(
% 8.08/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f3])).
% 8.08/1.49  
% 8.08/1.49  fof(f47,plain,(
% 8.08/1.49    v1_relat_1(sK0)),
% 8.08/1.49    inference(cnf_transformation,[],[f30])).
% 8.08/1.49  
% 8.08/1.49  fof(f11,axiom,(
% 8.08/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f21,plain,(
% 8.08/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 8.08/1.49    inference(ennf_transformation,[],[f11])).
% 8.08/1.49  
% 8.08/1.49  fof(f45,plain,(
% 8.08/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f21])).
% 8.08/1.49  
% 8.08/1.49  fof(f50,plain,(
% 8.08/1.49    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 8.08/1.49    inference(cnf_transformation,[],[f30])).
% 8.08/1.49  
% 8.08/1.49  cnf(c_17,negated_conjecture,
% 8.08/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 8.08/1.49      inference(cnf_transformation,[],[f49]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_499,plain,
% 8.08/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13,plain,
% 8.08/1.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f43]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_502,plain,
% 8.08/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_8,plain,
% 8.08/1.49      ( ~ v1_relat_1(X0)
% 8.08/1.49      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f39]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_505,plain,
% 8.08/1.49      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 8.08/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1068,plain,
% 8.08/1.49      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_502,c_505]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_10,plain,
% 8.08/1.49      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 8.08/1.49      inference(cnf_transformation,[],[f42]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_11,plain,
% 8.08/1.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 8.08/1.49      inference(cnf_transformation,[],[f41]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1073,plain,
% 8.08/1.49      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 8.08/1.49      inference(light_normalisation,[status(thm)],[c_1068,c_10,c_11]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_9,plain,
% 8.08/1.49      ( ~ r1_tarski(X0,X1)
% 8.08/1.49      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
% 8.08/1.49      | ~ v1_relat_1(X2) ),
% 8.08/1.49      inference(cnf_transformation,[],[f40]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_504,plain,
% 8.08/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.08/1.49      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
% 8.08/1.49      | v1_relat_1(X2) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1596,plain,
% 8.08/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.08/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 8.08/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_1073,c_504]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_29,plain,
% 8.08/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2793,plain,
% 8.08/1.49      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 8.08/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_1596,c_29]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2794,plain,
% 8.08/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.08/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 8.08/1.49      inference(renaming,[status(thm)],[c_2793]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6,plain,
% 8.08/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f37]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_507,plain,
% 8.08/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 8.08/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1403,plain,
% 8.08/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
% 8.08/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_11,c_507]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1415,plain,
% 8.08/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_1403,c_29]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1,plain,
% 8.08/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 8.08/1.49      inference(cnf_transformation,[],[f34]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_511,plain,
% 8.08/1.49      ( X0 = X1
% 8.08/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.08/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1929,plain,
% 8.08/1.49      ( k10_relat_1(k6_relat_1(X0),X1) = X0
% 8.08/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_1415,c_511]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3273,plain,
% 8.08/1.49      ( k10_relat_1(k6_relat_1(X0),X1) = X0
% 8.08/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_2794,c_1929]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_22782,plain,
% 8.08/1.49      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_499,c_3273]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_0,plain,
% 8.08/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f31]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_7,plain,
% 8.08/1.49      ( ~ v1_relat_1(X0)
% 8.08/1.49      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 8.08/1.49      inference(cnf_transformation,[],[f38]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_506,plain,
% 8.08/1.49      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 8.08/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1613,plain,
% 8.08/1.49      ( k10_relat_1(k6_relat_1(X0),k3_xboole_0(k2_relat_1(k6_relat_1(X0)),X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_502,c_506]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1618,plain,
% 8.08/1.49      ( k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
% 8.08/1.49      inference(light_normalisation,[status(thm)],[c_1613,c_10]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_15,plain,
% 8.08/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 8.08/1.49      | ~ v1_funct_1(X0)
% 8.08/1.49      | ~ v1_relat_1(X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f46]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_500,plain,
% 8.08/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 8.08/1.49      | v1_funct_1(X0) != iProver_top
% 8.08/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1735,plain,
% 8.08/1.49      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),k3_xboole_0(X0,X1)) = iProver_top
% 8.08/1.49      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 8.08/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_1618,c_500]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_12,plain,
% 8.08/1.49      ( v1_funct_1(k6_relat_1(X0)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f44]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_32,plain,
% 8.08/1.49      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3289,plain,
% 8.08/1.49      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),k3_xboole_0(X0,X1)) = iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_1735,c_29,c_32]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3299,plain,
% 8.08/1.49      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),k3_xboole_0(X1,X0)) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_0,c_3289]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_24666,plain,
% 8.08/1.49      ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_22782,c_3299]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5,plain,
% 8.08/1.49      ( ~ v1_relat_1(X0)
% 8.08/1.49      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f36]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_508,plain,
% 8.08/1.49      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 8.08/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1328,plain,
% 8.08/1.49      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_502,c_508]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1333,plain,
% 8.08/1.49      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 8.08/1.49      inference(light_normalisation,[status(thm)],[c_1328,c_10,c_11]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_24755,plain,
% 8.08/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = iProver_top ),
% 8.08/1.49      inference(demodulation,[status(thm)],[c_24666,c_1333]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_4,plain,
% 8.08/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f35]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_509,plain,
% 8.08/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_954,plain,
% 8.08/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_0,c_509]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1928,plain,
% 8.08/1.49      ( k3_xboole_0(X0,X1) = X1
% 8.08/1.49      | r1_tarski(X1,k3_xboole_0(X0,X1)) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_954,c_511]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_28716,plain,
% 8.08/1.49      ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_24755,c_1928]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_19,negated_conjecture,
% 8.08/1.49      ( v1_relat_1(sK0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_497,plain,
% 8.08/1.49      ( v1_relat_1(sK0) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_14,plain,
% 8.08/1.49      ( ~ v1_relat_1(X0)
% 8.08/1.49      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f45]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_501,plain,
% 8.08/1.49      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 8.08/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1207,plain,
% 8.08/1.49      ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_497,c_501]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_16,negated_conjecture,
% 8.08/1.49      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 8.08/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2414,plain,
% 8.08/1.49      ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) != k10_relat_1(sK0,sK2) ),
% 8.08/1.49      inference(demodulation,[status(thm)],[c_1207,c_16]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(contradiction,plain,
% 8.08/1.49      ( $false ),
% 8.08/1.49      inference(minisat,[status(thm)],[c_28716,c_2414]) ).
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  ------                               Statistics
% 8.08/1.49  
% 8.08/1.49  ------ Selected
% 8.08/1.49  
% 8.08/1.49  total_time:                             0.845
% 8.08/1.49  
%------------------------------------------------------------------------------
