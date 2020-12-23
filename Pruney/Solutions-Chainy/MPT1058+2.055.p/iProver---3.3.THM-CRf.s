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
% DateTime   : Thu Dec  3 12:09:20 EST 2020

% Result     : Theorem 39.69s
% Output     : CNFRefutation 39.69s
% Verified   : 
% Statistics : Number of formulae       :  320 (116648 expanded)
%              Number of clauses        :  249 (39320 expanded)
%              Number of leaves         :   22 (27641 expanded)
%              Depth                    :   52
%              Number of atoms          :  546 (289158 expanded)
%              Number of equality atoms :  353 (113595 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :   13 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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

fof(f39,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37])).

fof(f63,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f17,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f61,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_632,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_246,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
    | ~ v1_relat_1(k6_relat_1(X1))
    | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_257,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
    | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_247,c_13])).

cnf(c_626,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_9,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_638,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_626,c_9])).

cnf(c_5131,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_632,c_638])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_352,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_353,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_635,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_353,c_9,c_10])).

cnf(c_5143,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5131,c_635])).

cnf(c_17,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_226,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_227,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2)
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_239,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_227,c_13])).

cnf(c_627,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_639,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_627,c_10])).

cnf(c_5788,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5143,c_639])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_68,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_140282,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5788,c_68])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_628,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_630,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2105,plain,
    ( k2_xboole_0(k10_relat_1(sK0,sK2),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_628,c_630])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_631,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3084,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2105,c_631])).

cnf(c_5217,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,sK2))) = k10_relat_1(sK0,sK2)
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3084,c_638])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_263,plain,
    ( ~ v1_relat_1(X0)
    | k6_relat_1(X1) != X0
    | k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X2)) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_264,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_268,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_13])).

cnf(c_269,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_637,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_269,c_10])).

cnf(c_5782,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(demodulation,[status(thm)],[c_5143,c_637])).

cnf(c_18,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_346,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_347,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_636,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_18,c_347])).

cnf(c_1933,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_636,c_9])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_367,plain,
    ( k6_relat_1(X0) != X1
    | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_368,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1939,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1933,c_368])).

cnf(c_5783,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_5782,c_1939])).

cnf(c_80281,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0) = k10_relat_1(sK0,sK2)
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5217,c_5783])).

cnf(c_140346,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(k6_relat_1(sK1),X0)) = k10_relat_1(sK0,sK2)
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_140282,c_80281])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_373,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_374,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_1926,plain,
    ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)) = k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_374,c_636])).

cnf(c_340,plain,
    ( k6_relat_1(X0) != X1
    | k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3))) = k10_relat_1(k7_relat_1(X1,X2),X3) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_13])).

cnf(c_341,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k6_relat_1(X1),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_8564,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(superposition,[status(thm)],[c_1939,c_341])).

cnf(c_140396,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,sK1),sK2)),X0) = k10_relat_1(sK0,sK2)
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_140346,c_1926,c_8564])).

cnf(c_142350,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,sK1),sK2)),sK1) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_632,c_140396])).

cnf(c_1925,plain,
    ( k6_relat_1(k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(superposition,[status(thm)],[c_341,c_636])).

cnf(c_7,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_358,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_359,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_623,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_634,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_623,c_10])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_295,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_296,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_300,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK0))
    | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_22])).

cnf(c_624,plain,
    ( k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0
    | r1_tarski(X0,k2_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_1454,plain,
    ( k9_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))) = k2_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_632,c_624])).

cnf(c_385,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_386,plain,
    ( k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_1455,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1454,c_386])).

cnf(c_313,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_314,plain,
    ( ~ v1_relat_1(sK0)
    | k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK0,k1_relat_1(sK0)))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_318,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK0,k1_relat_1(sK0)))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_22])).

cnf(c_1456,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_1455,c_318])).

cnf(c_5,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_629,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1913,plain,
    ( r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_629])).

cnf(c_2377,plain,
    ( k2_xboole_0(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1913,c_630])).

cnf(c_7017,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2377,c_631])).

cnf(c_274,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_275,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,X0),X1)
    | ~ v1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_279,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,X0),X1)
    | ~ r1_tarski(X0,k1_relat_1(sK0))
    | r1_tarski(X0,k10_relat_1(sK0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_22])).

cnf(c_280,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,X0),X1) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_625,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK0,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_23408,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = iProver_top
    | r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7017,c_625])).

cnf(c_390,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_391,plain,
    ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_392,plain,
    ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_25179,plain,
    ( r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23408,c_392])).

cnf(c_25180,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_25179])).

cnf(c_25193,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,X1))) = k10_relat_1(sK0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_25180,c_638])).

cnf(c_2623,plain,
    ( k2_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_1926,c_368])).

cnf(c_2626,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_2623,c_9])).

cnf(c_4651,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X1)),X1))) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_2626,c_637])).

cnf(c_4659,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0)) ),
    inference(demodulation,[status(thm)],[c_4651,c_1939])).

cnf(c_5791,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = k10_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_5143,c_2626])).

cnf(c_25197,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X1) = k10_relat_1(sK0,X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25193,c_2626,c_4659,c_5791])).

cnf(c_48436,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),X0) = k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_634,c_25197])).

cnf(c_1340,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_635,c_341])).

cnf(c_7002,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1340,c_1939])).

cnf(c_7004,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X0) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1926,c_7002])).

cnf(c_53062,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_48436,c_7004])).

cnf(c_53107,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_53062,c_635,c_2626])).

cnf(c_53694,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),k10_relat_1(sK0,X0)) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),k10_relat_1(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_53107,c_7004])).

cnf(c_53725,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),k10_relat_1(sK0,X0)) = k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_53694,c_2626,c_48436])).

cnf(c_56388,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),X2),k10_relat_1(sK0,X0)) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1)))) ),
    inference(superposition,[status(thm)],[c_53725,c_341])).

cnf(c_56411,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),X2),k10_relat_1(sK0,X0)) = k10_relat_1(k7_relat_1(sK0,X2),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_56388,c_374])).

cnf(c_56745,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(sK0,X0)) = k10_relat_1(k7_relat_1(sK0,X1),k10_relat_1(k6_relat_1(X0),X0)) ),
    inference(superposition,[status(thm)],[c_635,c_56411])).

cnf(c_56788,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(sK0,X0)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_56745,c_635])).

cnf(c_58818,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)),X2)),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X2)),X1) ),
    inference(superposition,[status(thm)],[c_1925,c_56788])).

cnf(c_58860,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X2)),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X2)),X1) ),
    inference(light_normalisation,[status(thm)],[c_58818,c_1926])).

cnf(c_143799,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(sK1),sK1)),sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_142350,c_58860])).

cnf(c_3082,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_631])).

cnf(c_5915,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_631])).

cnf(c_7144,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5915,c_631])).

cnf(c_10564,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3),X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7144,c_631])).

cnf(c_5676,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_639])).

cnf(c_36834,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),k9_relat_1(sK0,X0))))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK0,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5676,c_625])).

cnf(c_622,plain,
    ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_633,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4205,plain,
    ( k10_relat_1(sK0,X0) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k10_relat_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_633])).

cnf(c_46706,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),k9_relat_1(sK0,k1_relat_1(sK0))))) = k1_relat_1(sK0)
    | r1_tarski(k9_relat_1(sK0,k1_relat_1(sK0)),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36834,c_4205])).

cnf(c_1928,plain,
    ( k6_relat_1(k9_relat_1(sK0,k10_relat_1(sK0,X0))) = k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_1456,c_636])).

cnf(c_2605,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1928,c_9])).

cnf(c_2913,plain,
    ( k9_relat_1(k6_relat_1(X0),k2_relat_1(sK0)) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_2605,c_368])).

cnf(c_46728,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k2_relat_1(sK0),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_46706,c_1455,c_2913])).

cnf(c_754,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_755,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_47319,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46728,c_755])).

cnf(c_47339,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k9_relat_1(sK0,k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3))))) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_10564,c_47319])).

cnf(c_2103,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_632,c_630])).

cnf(c_14211,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3),X4),X5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10564,c_631])).

cnf(c_19598,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k9_relat_1(sK0,X0),X1),X2),X3),X4),X5))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14211,c_625])).

cnf(c_23072,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k9_relat_1(sK0,k1_relat_1(sK0)),X0),X1),X2),X3),X4)) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19598,c_4205])).

cnf(c_23077,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3),X4)) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23072,c_1455])).

cnf(c_24432,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3),X4)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23077,c_755])).

cnf(c_24447,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_2103,c_24432])).

cnf(c_47353,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_47339,c_1455,c_24447])).

cnf(c_57471,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_47353,c_1913])).

cnf(c_57484,plain,
    ( r1_tarski(k2_relat_1(sK0),k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_57471,c_1455])).

cnf(c_58435,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))),k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0)))))) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_57484,c_47319])).

cnf(c_58438,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))),k2_relat_1(sK0))) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_58435,c_1455,c_47353])).

cnf(c_56755,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))),X1),k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,X1),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) ),
    inference(superposition,[status(thm)],[c_386,c_56411])).

cnf(c_1837,plain,
    ( k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) = k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
    inference(superposition,[status(thm)],[c_634,c_624])).

cnf(c_5139,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1913,c_638])).

cnf(c_31236,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) = k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) ),
    inference(superposition,[status(thm)],[c_1837,c_5139])).

cnf(c_31278,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) = k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_31236,c_1837])).

cnf(c_31279,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),X0) = k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
    inference(demodulation,[status(thm)],[c_31278,c_635,c_5783,c_8564])).

cnf(c_2599,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) = k6_relat_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_386,c_1928])).

cnf(c_2611,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2599,c_1455])).

cnf(c_3410,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) = k2_relat_1(k6_relat_1(k2_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_2611,c_368])).

cnf(c_3417,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(demodulation,[status(thm)],[c_3410,c_9,c_2913])).

cnf(c_4652,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_3417,c_637])).

cnf(c_4658,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4652,c_1456])).

cnf(c_1941,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_1939,c_636])).

cnf(c_9417,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k6_relat_1(k9_relat_1(sK0,k10_relat_1(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_4658,c_1941])).

cnf(c_9490,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_9417,c_1928])).

cnf(c_31280,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0)),X0) = k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_31279,c_9490])).

cnf(c_31281,plain,
    ( k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
    inference(demodulation,[status(thm)],[c_31280,c_7002])).

cnf(c_56775,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))),X1),k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,X1),k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_56755,c_31281])).

cnf(c_47328,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k9_relat_1(sK0,k10_relat_1(sK0,k2_xboole_0(k2_relat_1(sK0),X0))))) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_3082,c_47319])).

cnf(c_5917,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,k2_xboole_0(k9_relat_1(sK0,X0),X1))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_625])).

cnf(c_6891,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k9_relat_1(sK0,k1_relat_1(sK0)),X0)) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5917,c_4205])).

cnf(c_6892,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_relat_1(sK0),X0)) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6891,c_1455])).

cnf(c_7610,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_relat_1(sK0),X0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6892,c_755])).

cnf(c_47357,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_47328,c_1455,c_7610])).

cnf(c_49075,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))),k2_relat_1(sK0)) = k6_relat_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_47357,c_1928])).

cnf(c_49083,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))),k2_relat_1(sK0)) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_49075,c_1455])).

cnf(c_50081,plain,
    ( k10_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) = k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_49083,c_7002])).

cnf(c_7622,plain,
    ( k7_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0)) = k6_relat_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_7610,c_1928])).

cnf(c_7628,plain,
    ( k7_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0)) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_7622,c_1455])).

cnf(c_50122,plain,
    ( k10_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) = k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_50081,c_7628,c_8564,c_31281])).

cnf(c_50123,plain,
    ( k10_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) = k2_relat_1(sK0) ),
    inference(demodulation,[status(thm)],[c_50122,c_386,c_1455,c_2913,c_31281])).

cnf(c_50927,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X1)),k2_relat_1(sK0))) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_50123,c_341])).

cnf(c_50949,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X1)),k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_50927,c_1456])).

cnf(c_63829,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_2103,c_50949])).

cnf(c_63852,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_63829,c_31281])).

cnf(c_63853,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k9_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_63852,c_2913])).

cnf(c_63854,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k2_relat_1(sK0)) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_63853,c_386,c_1455])).

cnf(c_63956,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0)),X1)),k2_relat_1(sK0)) = k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_1925,c_63854])).

cnf(c_68276,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k2_relat_1(sK0)) = k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) ),
    inference(superposition,[status(thm)],[c_2611,c_63956])).

cnf(c_68332,plain,
    ( k10_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k2_relat_1(sK0)) = k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_68276,c_1837,c_31281])).

cnf(c_68333,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_68332,c_1941,c_63854])).

cnf(c_82484,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),X1),k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,X1),k9_relat_1(sK0,k10_relat_1(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_56775,c_56775,c_68333])).

cnf(c_82487,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),X1)),k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X1)),k9_relat_1(sK0,k10_relat_1(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_1926,c_82484])).

cnf(c_130310,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X1),X2),X3),X4)),k2_relat_1(sK0))),k2_relat_1(sK0))))) = k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),X0)),k1_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_58438,c_82487])).

cnf(c_130404,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X1),X2),X3),X4)),k2_relat_1(sK0))),k2_relat_1(sK0))))) = k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0)),k1_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_130310,c_386,c_1455])).

cnf(c_10563,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    inference(superposition,[status(thm)],[c_7144,c_630])).

cnf(c_47331,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k9_relat_1(sK0,k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1))))) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_5915,c_47319])).

cnf(c_7146,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k9_relat_1(sK0,X0),X1),X2))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5915,c_625])).

cnf(c_8812,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k9_relat_1(sK0,k1_relat_1(sK0)),X0),X1)) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7146,c_4205])).

cnf(c_8813,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8812,c_1455])).

cnf(c_8855,plain,
    ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8813,c_755])).

cnf(c_47355,plain,
    ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_47331,c_1455,c_8855])).

cnf(c_49753,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))),k2_relat_1(sK0)) = k6_relat_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_47355,c_1928])).

cnf(c_49761,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))),k2_relat_1(sK0)) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_49753,c_1455])).

cnf(c_68281,plain,
    ( k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))),X2))) = k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X2)),k2_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_49761,c_63956])).

cnf(c_68327,plain,
    ( k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))),X2))) = k9_relat_1(sK0,k10_relat_1(sK0,X2)) ),
    inference(demodulation,[status(thm)],[c_68281,c_1941,c_31281,c_63854])).

cnf(c_85445,plain,
    ( k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))),X4))) = k9_relat_1(sK0,k10_relat_1(sK0,X4)) ),
    inference(superposition,[status(thm)],[c_10563,c_68327])).

cnf(c_2106,plain,
    ( k2_xboole_0(k10_relat_1(sK0,X0),k1_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_622,c_630])).

cnf(c_1636,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,k9_relat_1(sK0,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_625])).

cnf(c_3083,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,k9_relat_1(sK0,k2_xboole_0(X0,X1)))) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_631])).

cnf(c_44726,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k2_xboole_0(X0,X1)))),k10_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k2_xboole_0(X0,X1)))),X0)) = X0
    | r1_tarski(k2_xboole_0(X0,X1),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_638])).

cnf(c_44753,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),k9_relat_1(sK0,k2_xboole_0(X0,X1))) = X0
    | r1_tarski(k2_xboole_0(X0,X1),k1_relat_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_44726,c_2626,c_4659,c_5791])).

cnf(c_118607,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k2_xboole_0(k10_relat_1(sK0,X0),k1_relat_1(sK0)))) = k10_relat_1(sK0,X0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2106,c_44753])).

cnf(c_118769,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k2_relat_1(sK0)) = k10_relat_1(sK0,X0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_118607,c_1455,c_2106])).

cnf(c_3078,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),k2_relat_1(sK0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_386,c_2626])).

cnf(c_118770,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k1_relat_1(sK0)) = k10_relat_1(sK0,X0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_118769,c_3078])).

cnf(c_118980,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k1_relat_1(sK0)) = k10_relat_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_118770,c_755])).

cnf(c_130405,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))) = k10_relat_1(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_130404,c_7004,c_85445,c_118980])).

cnf(c_130406,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k2_relat_1(sK0)) = k10_relat_1(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_130405,c_386,c_1455])).

cnf(c_132856,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k9_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4659,c_4659,c_5791])).

cnf(c_132857,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_132856,c_2626,c_4659])).

cnf(c_1910,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_341,c_629])).

cnf(c_7345,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(superposition,[status(thm)],[c_1910,c_638])).

cnf(c_132917,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)),X2)),X1) = k10_relat_1(k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_132857,c_7345])).

cnf(c_132932,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X2)),X1) = k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X2) ),
    inference(light_normalisation,[status(thm)],[c_132917,c_1926])).

cnf(c_133933,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k2_relat_1(sK0))),X1) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k2_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_130406,c_132932])).

cnf(c_134143,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k2_relat_1(sK0)) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_133933,c_130406])).

cnf(c_1911,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_374,c_629])).

cnf(c_5138,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k10_relat_1(k7_relat_1(sK0,X0),X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_1911,c_638])).

cnf(c_135880,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1))) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k2_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_134143,c_5138])).

cnf(c_135899,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1))) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_135880,c_134143])).

cnf(c_135900,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),X1) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_135899,c_635,c_5783,c_8564])).

cnf(c_132912,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k6_relat_1(k10_relat_1(k7_relat_1(sK0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_132857,c_1941])).

cnf(c_135901,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X0) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_135900,c_132912])).

cnf(c_135902,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_135901,c_7004])).

cnf(c_143812,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,sK2)),sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_143799,c_635,c_2626,c_135902])).

cnf(c_143813,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_143812,c_5791])).

cnf(c_418,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_869,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_419,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_668,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
    | k10_relat_1(sK0,sK2) != X0
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_744,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_19,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143813,c_869,c_744,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.69/5.54  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.69/5.54  
% 39.69/5.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.69/5.54  
% 39.69/5.54  ------  iProver source info
% 39.69/5.54  
% 39.69/5.54  git: date: 2020-06-30 10:37:57 +0100
% 39.69/5.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.69/5.54  git: non_committed_changes: false
% 39.69/5.54  git: last_make_outside_of_git: false
% 39.69/5.54  
% 39.69/5.54  ------ 
% 39.69/5.54  
% 39.69/5.54  ------ Input Options
% 39.69/5.54  
% 39.69/5.54  --out_options                           all
% 39.69/5.54  --tptp_safe_out                         true
% 39.69/5.54  --problem_path                          ""
% 39.69/5.54  --include_path                          ""
% 39.69/5.54  --clausifier                            res/vclausify_rel
% 39.69/5.54  --clausifier_options                    ""
% 39.69/5.54  --stdin                                 false
% 39.69/5.54  --stats_out                             all
% 39.69/5.54  
% 39.69/5.54  ------ General Options
% 39.69/5.54  
% 39.69/5.54  --fof                                   false
% 39.69/5.54  --time_out_real                         305.
% 39.69/5.54  --time_out_virtual                      -1.
% 39.69/5.54  --symbol_type_check                     false
% 39.69/5.54  --clausify_out                          false
% 39.69/5.54  --sig_cnt_out                           false
% 39.69/5.54  --trig_cnt_out                          false
% 39.69/5.54  --trig_cnt_out_tolerance                1.
% 39.69/5.54  --trig_cnt_out_sk_spl                   false
% 39.69/5.54  --abstr_cl_out                          false
% 39.69/5.54  
% 39.69/5.54  ------ Global Options
% 39.69/5.54  
% 39.69/5.54  --schedule                              default
% 39.69/5.54  --add_important_lit                     false
% 39.69/5.54  --prop_solver_per_cl                    1000
% 39.69/5.54  --min_unsat_core                        false
% 39.69/5.54  --soft_assumptions                      false
% 39.69/5.54  --soft_lemma_size                       3
% 39.69/5.54  --prop_impl_unit_size                   0
% 39.69/5.54  --prop_impl_unit                        []
% 39.69/5.54  --share_sel_clauses                     true
% 39.69/5.54  --reset_solvers                         false
% 39.69/5.54  --bc_imp_inh                            [conj_cone]
% 39.69/5.54  --conj_cone_tolerance                   3.
% 39.69/5.54  --extra_neg_conj                        none
% 39.69/5.54  --large_theory_mode                     true
% 39.69/5.54  --prolific_symb_bound                   200
% 39.69/5.54  --lt_threshold                          2000
% 39.69/5.54  --clause_weak_htbl                      true
% 39.69/5.54  --gc_record_bc_elim                     false
% 39.69/5.54  
% 39.69/5.54  ------ Preprocessing Options
% 39.69/5.54  
% 39.69/5.54  --preprocessing_flag                    true
% 39.69/5.54  --time_out_prep_mult                    0.1
% 39.69/5.54  --splitting_mode                        input
% 39.69/5.54  --splitting_grd                         true
% 39.69/5.54  --splitting_cvd                         false
% 39.69/5.54  --splitting_cvd_svl                     false
% 39.69/5.54  --splitting_nvd                         32
% 39.69/5.54  --sub_typing                            true
% 39.69/5.54  --prep_gs_sim                           true
% 39.69/5.54  --prep_unflatten                        true
% 39.69/5.54  --prep_res_sim                          true
% 39.69/5.54  --prep_upred                            true
% 39.69/5.54  --prep_sem_filter                       exhaustive
% 39.69/5.54  --prep_sem_filter_out                   false
% 39.69/5.54  --pred_elim                             true
% 39.69/5.54  --res_sim_input                         true
% 39.69/5.54  --eq_ax_congr_red                       true
% 39.69/5.54  --pure_diseq_elim                       true
% 39.69/5.54  --brand_transform                       false
% 39.69/5.54  --non_eq_to_eq                          false
% 39.69/5.54  --prep_def_merge                        true
% 39.69/5.54  --prep_def_merge_prop_impl              false
% 39.69/5.54  --prep_def_merge_mbd                    true
% 39.69/5.54  --prep_def_merge_tr_red                 false
% 39.69/5.54  --prep_def_merge_tr_cl                  false
% 39.69/5.54  --smt_preprocessing                     true
% 39.69/5.54  --smt_ac_axioms                         fast
% 39.69/5.54  --preprocessed_out                      false
% 39.69/5.54  --preprocessed_stats                    false
% 39.69/5.54  
% 39.69/5.54  ------ Abstraction refinement Options
% 39.69/5.54  
% 39.69/5.54  --abstr_ref                             []
% 39.69/5.54  --abstr_ref_prep                        false
% 39.69/5.54  --abstr_ref_until_sat                   false
% 39.69/5.54  --abstr_ref_sig_restrict                funpre
% 39.69/5.54  --abstr_ref_af_restrict_to_split_sk     false
% 39.69/5.54  --abstr_ref_under                       []
% 39.69/5.54  
% 39.69/5.54  ------ SAT Options
% 39.69/5.54  
% 39.69/5.54  --sat_mode                              false
% 39.69/5.54  --sat_fm_restart_options                ""
% 39.69/5.54  --sat_gr_def                            false
% 39.69/5.54  --sat_epr_types                         true
% 39.69/5.54  --sat_non_cyclic_types                  false
% 39.69/5.54  --sat_finite_models                     false
% 39.69/5.54  --sat_fm_lemmas                         false
% 39.69/5.54  --sat_fm_prep                           false
% 39.69/5.54  --sat_fm_uc_incr                        true
% 39.69/5.54  --sat_out_model                         small
% 39.69/5.54  --sat_out_clauses                       false
% 39.69/5.54  
% 39.69/5.54  ------ QBF Options
% 39.69/5.54  
% 39.69/5.54  --qbf_mode                              false
% 39.69/5.54  --qbf_elim_univ                         false
% 39.69/5.54  --qbf_dom_inst                          none
% 39.69/5.54  --qbf_dom_pre_inst                      false
% 39.69/5.54  --qbf_sk_in                             false
% 39.69/5.54  --qbf_pred_elim                         true
% 39.69/5.54  --qbf_split                             512
% 39.69/5.54  
% 39.69/5.54  ------ BMC1 Options
% 39.69/5.54  
% 39.69/5.54  --bmc1_incremental                      false
% 39.69/5.54  --bmc1_axioms                           reachable_all
% 39.69/5.54  --bmc1_min_bound                        0
% 39.69/5.54  --bmc1_max_bound                        -1
% 39.69/5.54  --bmc1_max_bound_default                -1
% 39.69/5.54  --bmc1_symbol_reachability              true
% 39.69/5.54  --bmc1_property_lemmas                  false
% 39.69/5.54  --bmc1_k_induction                      false
% 39.69/5.54  --bmc1_non_equiv_states                 false
% 39.69/5.54  --bmc1_deadlock                         false
% 39.69/5.54  --bmc1_ucm                              false
% 39.69/5.54  --bmc1_add_unsat_core                   none
% 39.69/5.54  --bmc1_unsat_core_children              false
% 39.69/5.54  --bmc1_unsat_core_extrapolate_axioms    false
% 39.69/5.54  --bmc1_out_stat                         full
% 39.69/5.54  --bmc1_ground_init                      false
% 39.69/5.54  --bmc1_pre_inst_next_state              false
% 39.69/5.54  --bmc1_pre_inst_state                   false
% 39.69/5.54  --bmc1_pre_inst_reach_state             false
% 39.69/5.54  --bmc1_out_unsat_core                   false
% 39.69/5.54  --bmc1_aig_witness_out                  false
% 39.69/5.54  --bmc1_verbose                          false
% 39.69/5.54  --bmc1_dump_clauses_tptp                false
% 39.69/5.54  --bmc1_dump_unsat_core_tptp             false
% 39.69/5.54  --bmc1_dump_file                        -
% 39.69/5.54  --bmc1_ucm_expand_uc_limit              128
% 39.69/5.54  --bmc1_ucm_n_expand_iterations          6
% 39.69/5.54  --bmc1_ucm_extend_mode                  1
% 39.69/5.54  --bmc1_ucm_init_mode                    2
% 39.69/5.54  --bmc1_ucm_cone_mode                    none
% 39.69/5.54  --bmc1_ucm_reduced_relation_type        0
% 39.69/5.54  --bmc1_ucm_relax_model                  4
% 39.69/5.54  --bmc1_ucm_full_tr_after_sat            true
% 39.69/5.54  --bmc1_ucm_expand_neg_assumptions       false
% 39.69/5.54  --bmc1_ucm_layered_model                none
% 39.69/5.54  --bmc1_ucm_max_lemma_size               10
% 39.69/5.54  
% 39.69/5.54  ------ AIG Options
% 39.69/5.54  
% 39.69/5.54  --aig_mode                              false
% 39.69/5.54  
% 39.69/5.54  ------ Instantiation Options
% 39.69/5.54  
% 39.69/5.54  --instantiation_flag                    true
% 39.69/5.54  --inst_sos_flag                         true
% 39.69/5.54  --inst_sos_phase                        true
% 39.69/5.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.69/5.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.69/5.54  --inst_lit_sel_side                     num_symb
% 39.69/5.54  --inst_solver_per_active                1400
% 39.69/5.54  --inst_solver_calls_frac                1.
% 39.69/5.54  --inst_passive_queue_type               priority_queues
% 39.69/5.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.69/5.54  --inst_passive_queues_freq              [25;2]
% 39.69/5.54  --inst_dismatching                      true
% 39.69/5.54  --inst_eager_unprocessed_to_passive     true
% 39.69/5.54  --inst_prop_sim_given                   true
% 39.69/5.54  --inst_prop_sim_new                     false
% 39.69/5.54  --inst_subs_new                         false
% 39.69/5.54  --inst_eq_res_simp                      false
% 39.69/5.54  --inst_subs_given                       false
% 39.69/5.54  --inst_orphan_elimination               true
% 39.69/5.54  --inst_learning_loop_flag               true
% 39.69/5.54  --inst_learning_start                   3000
% 39.69/5.54  --inst_learning_factor                  2
% 39.69/5.54  --inst_start_prop_sim_after_learn       3
% 39.69/5.54  --inst_sel_renew                        solver
% 39.69/5.54  --inst_lit_activity_flag                true
% 39.69/5.54  --inst_restr_to_given                   false
% 39.69/5.54  --inst_activity_threshold               500
% 39.69/5.54  --inst_out_proof                        true
% 39.69/5.54  
% 39.69/5.54  ------ Resolution Options
% 39.69/5.54  
% 39.69/5.54  --resolution_flag                       true
% 39.69/5.54  --res_lit_sel                           adaptive
% 39.69/5.54  --res_lit_sel_side                      none
% 39.69/5.54  --res_ordering                          kbo
% 39.69/5.54  --res_to_prop_solver                    active
% 39.69/5.54  --res_prop_simpl_new                    false
% 39.69/5.54  --res_prop_simpl_given                  true
% 39.69/5.54  --res_passive_queue_type                priority_queues
% 39.69/5.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.69/5.54  --res_passive_queues_freq               [15;5]
% 39.69/5.54  --res_forward_subs                      full
% 39.69/5.54  --res_backward_subs                     full
% 39.69/5.54  --res_forward_subs_resolution           true
% 39.69/5.54  --res_backward_subs_resolution          true
% 39.69/5.54  --res_orphan_elimination                true
% 39.69/5.54  --res_time_limit                        2.
% 39.69/5.54  --res_out_proof                         true
% 39.69/5.54  
% 39.69/5.54  ------ Superposition Options
% 39.69/5.54  
% 39.69/5.54  --superposition_flag                    true
% 39.69/5.54  --sup_passive_queue_type                priority_queues
% 39.69/5.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.69/5.54  --sup_passive_queues_freq               [8;1;4]
% 39.69/5.54  --demod_completeness_check              fast
% 39.69/5.54  --demod_use_ground                      true
% 39.69/5.54  --sup_to_prop_solver                    passive
% 39.69/5.54  --sup_prop_simpl_new                    true
% 39.69/5.54  --sup_prop_simpl_given                  true
% 39.69/5.54  --sup_fun_splitting                     true
% 39.69/5.54  --sup_smt_interval                      50000
% 39.69/5.54  
% 39.69/5.54  ------ Superposition Simplification Setup
% 39.69/5.54  
% 39.69/5.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.69/5.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.69/5.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.69/5.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.69/5.54  --sup_full_triv                         [TrivRules;PropSubs]
% 39.69/5.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.69/5.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.69/5.54  --sup_immed_triv                        [TrivRules]
% 39.69/5.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.69/5.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.69/5.54  --sup_immed_bw_main                     []
% 39.69/5.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.69/5.54  --sup_input_triv                        [Unflattening;TrivRules]
% 39.69/5.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.69/5.54  --sup_input_bw                          []
% 39.69/5.54  
% 39.69/5.54  ------ Combination Options
% 39.69/5.54  
% 39.69/5.54  --comb_res_mult                         3
% 39.69/5.54  --comb_sup_mult                         2
% 39.69/5.54  --comb_inst_mult                        10
% 39.69/5.54  
% 39.69/5.54  ------ Debug Options
% 39.69/5.54  
% 39.69/5.54  --dbg_backtrace                         false
% 39.69/5.54  --dbg_dump_prop_clauses                 false
% 39.69/5.54  --dbg_dump_prop_clauses_file            -
% 39.69/5.54  --dbg_out_stat                          false
% 39.69/5.54  ------ Parsing...
% 39.69/5.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.69/5.54  
% 39.69/5.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 39.69/5.54  
% 39.69/5.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.69/5.54  
% 39.69/5.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.69/5.54  ------ Proving...
% 39.69/5.54  ------ Problem Properties 
% 39.69/5.54  
% 39.69/5.54  
% 39.69/5.54  clauses                                 26
% 39.69/5.54  conjectures                             2
% 39.69/5.54  EPR                                     2
% 39.69/5.54  Horn                                    26
% 39.69/5.54  unary                                   19
% 39.69/5.54  binary                                  4
% 39.69/5.54  lits                                    36
% 39.69/5.54  lits eq                                 18
% 39.69/5.54  fd_pure                                 0
% 39.69/5.54  fd_pseudo                               0
% 39.69/5.54  fd_cond                                 0
% 39.69/5.54  fd_pseudo_cond                          1
% 39.69/5.54  AC symbols                              0
% 39.69/5.54  
% 39.69/5.54  ------ Schedule dynamic 5 is on 
% 39.69/5.54  
% 39.69/5.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.69/5.54  
% 39.69/5.54  
% 39.69/5.54  ------ 
% 39.69/5.54  Current options:
% 39.69/5.54  ------ 
% 39.69/5.54  
% 39.69/5.54  ------ Input Options
% 39.69/5.54  
% 39.69/5.54  --out_options                           all
% 39.69/5.54  --tptp_safe_out                         true
% 39.69/5.54  --problem_path                          ""
% 39.69/5.54  --include_path                          ""
% 39.69/5.54  --clausifier                            res/vclausify_rel
% 39.69/5.54  --clausifier_options                    ""
% 39.69/5.54  --stdin                                 false
% 39.69/5.54  --stats_out                             all
% 39.69/5.54  
% 39.69/5.54  ------ General Options
% 39.69/5.54  
% 39.69/5.54  --fof                                   false
% 39.69/5.54  --time_out_real                         305.
% 39.69/5.54  --time_out_virtual                      -1.
% 39.69/5.54  --symbol_type_check                     false
% 39.69/5.54  --clausify_out                          false
% 39.69/5.54  --sig_cnt_out                           false
% 39.69/5.54  --trig_cnt_out                          false
% 39.69/5.54  --trig_cnt_out_tolerance                1.
% 39.69/5.54  --trig_cnt_out_sk_spl                   false
% 39.69/5.54  --abstr_cl_out                          false
% 39.69/5.54  
% 39.69/5.54  ------ Global Options
% 39.69/5.54  
% 39.69/5.54  --schedule                              default
% 39.69/5.54  --add_important_lit                     false
% 39.69/5.54  --prop_solver_per_cl                    1000
% 39.69/5.54  --min_unsat_core                        false
% 39.69/5.54  --soft_assumptions                      false
% 39.69/5.54  --soft_lemma_size                       3
% 39.69/5.54  --prop_impl_unit_size                   0
% 39.69/5.54  --prop_impl_unit                        []
% 39.69/5.54  --share_sel_clauses                     true
% 39.69/5.54  --reset_solvers                         false
% 39.69/5.54  --bc_imp_inh                            [conj_cone]
% 39.69/5.54  --conj_cone_tolerance                   3.
% 39.69/5.54  --extra_neg_conj                        none
% 39.69/5.54  --large_theory_mode                     true
% 39.69/5.54  --prolific_symb_bound                   200
% 39.69/5.54  --lt_threshold                          2000
% 39.69/5.54  --clause_weak_htbl                      true
% 39.69/5.54  --gc_record_bc_elim                     false
% 39.69/5.54  
% 39.69/5.54  ------ Preprocessing Options
% 39.69/5.54  
% 39.69/5.54  --preprocessing_flag                    true
% 39.69/5.54  --time_out_prep_mult                    0.1
% 39.69/5.54  --splitting_mode                        input
% 39.69/5.54  --splitting_grd                         true
% 39.69/5.54  --splitting_cvd                         false
% 39.69/5.54  --splitting_cvd_svl                     false
% 39.69/5.54  --splitting_nvd                         32
% 39.69/5.54  --sub_typing                            true
% 39.69/5.54  --prep_gs_sim                           true
% 39.69/5.54  --prep_unflatten                        true
% 39.69/5.54  --prep_res_sim                          true
% 39.69/5.54  --prep_upred                            true
% 39.69/5.54  --prep_sem_filter                       exhaustive
% 39.69/5.54  --prep_sem_filter_out                   false
% 39.69/5.54  --pred_elim                             true
% 39.69/5.54  --res_sim_input                         true
% 39.69/5.54  --eq_ax_congr_red                       true
% 39.69/5.54  --pure_diseq_elim                       true
% 39.69/5.54  --brand_transform                       false
% 39.69/5.54  --non_eq_to_eq                          false
% 39.69/5.54  --prep_def_merge                        true
% 39.69/5.54  --prep_def_merge_prop_impl              false
% 39.69/5.54  --prep_def_merge_mbd                    true
% 39.69/5.54  --prep_def_merge_tr_red                 false
% 39.69/5.54  --prep_def_merge_tr_cl                  false
% 39.69/5.54  --smt_preprocessing                     true
% 39.69/5.54  --smt_ac_axioms                         fast
% 39.69/5.54  --preprocessed_out                      false
% 39.69/5.54  --preprocessed_stats                    false
% 39.69/5.54  
% 39.69/5.54  ------ Abstraction refinement Options
% 39.69/5.54  
% 39.69/5.54  --abstr_ref                             []
% 39.69/5.54  --abstr_ref_prep                        false
% 39.69/5.54  --abstr_ref_until_sat                   false
% 39.69/5.54  --abstr_ref_sig_restrict                funpre
% 39.69/5.54  --abstr_ref_af_restrict_to_split_sk     false
% 39.69/5.54  --abstr_ref_under                       []
% 39.69/5.54  
% 39.69/5.54  ------ SAT Options
% 39.69/5.54  
% 39.69/5.54  --sat_mode                              false
% 39.69/5.54  --sat_fm_restart_options                ""
% 39.69/5.54  --sat_gr_def                            false
% 39.69/5.54  --sat_epr_types                         true
% 39.69/5.54  --sat_non_cyclic_types                  false
% 39.69/5.54  --sat_finite_models                     false
% 39.69/5.54  --sat_fm_lemmas                         false
% 39.69/5.54  --sat_fm_prep                           false
% 39.69/5.54  --sat_fm_uc_incr                        true
% 39.69/5.54  --sat_out_model                         small
% 39.69/5.54  --sat_out_clauses                       false
% 39.69/5.54  
% 39.69/5.54  ------ QBF Options
% 39.69/5.54  
% 39.69/5.54  --qbf_mode                              false
% 39.69/5.54  --qbf_elim_univ                         false
% 39.69/5.54  --qbf_dom_inst                          none
% 39.69/5.54  --qbf_dom_pre_inst                      false
% 39.69/5.54  --qbf_sk_in                             false
% 39.69/5.54  --qbf_pred_elim                         true
% 39.69/5.54  --qbf_split                             512
% 39.69/5.54  
% 39.69/5.54  ------ BMC1 Options
% 39.69/5.54  
% 39.69/5.54  --bmc1_incremental                      false
% 39.69/5.54  --bmc1_axioms                           reachable_all
% 39.69/5.54  --bmc1_min_bound                        0
% 39.69/5.54  --bmc1_max_bound                        -1
% 39.69/5.54  --bmc1_max_bound_default                -1
% 39.69/5.54  --bmc1_symbol_reachability              true
% 39.69/5.54  --bmc1_property_lemmas                  false
% 39.69/5.54  --bmc1_k_induction                      false
% 39.69/5.54  --bmc1_non_equiv_states                 false
% 39.69/5.54  --bmc1_deadlock                         false
% 39.69/5.54  --bmc1_ucm                              false
% 39.69/5.54  --bmc1_add_unsat_core                   none
% 39.69/5.54  --bmc1_unsat_core_children              false
% 39.69/5.54  --bmc1_unsat_core_extrapolate_axioms    false
% 39.69/5.54  --bmc1_out_stat                         full
% 39.69/5.54  --bmc1_ground_init                      false
% 39.69/5.54  --bmc1_pre_inst_next_state              false
% 39.69/5.54  --bmc1_pre_inst_state                   false
% 39.69/5.54  --bmc1_pre_inst_reach_state             false
% 39.69/5.54  --bmc1_out_unsat_core                   false
% 39.69/5.54  --bmc1_aig_witness_out                  false
% 39.69/5.54  --bmc1_verbose                          false
% 39.69/5.54  --bmc1_dump_clauses_tptp                false
% 39.69/5.54  --bmc1_dump_unsat_core_tptp             false
% 39.69/5.54  --bmc1_dump_file                        -
% 39.69/5.54  --bmc1_ucm_expand_uc_limit              128
% 39.69/5.54  --bmc1_ucm_n_expand_iterations          6
% 39.69/5.54  --bmc1_ucm_extend_mode                  1
% 39.69/5.54  --bmc1_ucm_init_mode                    2
% 39.69/5.54  --bmc1_ucm_cone_mode                    none
% 39.69/5.54  --bmc1_ucm_reduced_relation_type        0
% 39.69/5.54  --bmc1_ucm_relax_model                  4
% 39.69/5.54  --bmc1_ucm_full_tr_after_sat            true
% 39.69/5.54  --bmc1_ucm_expand_neg_assumptions       false
% 39.69/5.54  --bmc1_ucm_layered_model                none
% 39.69/5.54  --bmc1_ucm_max_lemma_size               10
% 39.69/5.54  
% 39.69/5.54  ------ AIG Options
% 39.69/5.54  
% 39.69/5.54  --aig_mode                              false
% 39.69/5.54  
% 39.69/5.54  ------ Instantiation Options
% 39.69/5.54  
% 39.69/5.54  --instantiation_flag                    true
% 39.69/5.54  --inst_sos_flag                         true
% 39.69/5.54  --inst_sos_phase                        true
% 39.69/5.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.69/5.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.69/5.54  --inst_lit_sel_side                     none
% 39.69/5.54  --inst_solver_per_active                1400
% 39.69/5.54  --inst_solver_calls_frac                1.
% 39.69/5.54  --inst_passive_queue_type               priority_queues
% 39.69/5.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.69/5.54  --inst_passive_queues_freq              [25;2]
% 39.69/5.54  --inst_dismatching                      true
% 39.69/5.54  --inst_eager_unprocessed_to_passive     true
% 39.69/5.54  --inst_prop_sim_given                   true
% 39.69/5.54  --inst_prop_sim_new                     false
% 39.69/5.54  --inst_subs_new                         false
% 39.69/5.54  --inst_eq_res_simp                      false
% 39.69/5.54  --inst_subs_given                       false
% 39.69/5.54  --inst_orphan_elimination               true
% 39.69/5.54  --inst_learning_loop_flag               true
% 39.69/5.54  --inst_learning_start                   3000
% 39.69/5.54  --inst_learning_factor                  2
% 39.69/5.54  --inst_start_prop_sim_after_learn       3
% 39.69/5.54  --inst_sel_renew                        solver
% 39.69/5.54  --inst_lit_activity_flag                true
% 39.69/5.54  --inst_restr_to_given                   false
% 39.69/5.54  --inst_activity_threshold               500
% 39.69/5.54  --inst_out_proof                        true
% 39.69/5.54  
% 39.69/5.54  ------ Resolution Options
% 39.69/5.54  
% 39.69/5.54  --resolution_flag                       false
% 39.69/5.54  --res_lit_sel                           adaptive
% 39.69/5.54  --res_lit_sel_side                      none
% 39.69/5.54  --res_ordering                          kbo
% 39.69/5.54  --res_to_prop_solver                    active
% 39.69/5.54  --res_prop_simpl_new                    false
% 39.69/5.54  --res_prop_simpl_given                  true
% 39.69/5.54  --res_passive_queue_type                priority_queues
% 39.69/5.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.69/5.54  --res_passive_queues_freq               [15;5]
% 39.69/5.54  --res_forward_subs                      full
% 39.69/5.54  --res_backward_subs                     full
% 39.69/5.54  --res_forward_subs_resolution           true
% 39.69/5.54  --res_backward_subs_resolution          true
% 39.69/5.54  --res_orphan_elimination                true
% 39.69/5.54  --res_time_limit                        2.
% 39.69/5.54  --res_out_proof                         true
% 39.69/5.54  
% 39.69/5.54  ------ Superposition Options
% 39.69/5.54  
% 39.69/5.54  --superposition_flag                    true
% 39.69/5.54  --sup_passive_queue_type                priority_queues
% 39.69/5.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.69/5.54  --sup_passive_queues_freq               [8;1;4]
% 39.69/5.54  --demod_completeness_check              fast
% 39.69/5.54  --demod_use_ground                      true
% 39.69/5.54  --sup_to_prop_solver                    passive
% 39.69/5.54  --sup_prop_simpl_new                    true
% 39.69/5.54  --sup_prop_simpl_given                  true
% 39.69/5.54  --sup_fun_splitting                     true
% 39.69/5.54  --sup_smt_interval                      50000
% 39.69/5.54  
% 39.69/5.54  ------ Superposition Simplification Setup
% 39.69/5.54  
% 39.69/5.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.69/5.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.69/5.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.69/5.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.69/5.54  --sup_full_triv                         [TrivRules;PropSubs]
% 39.69/5.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.69/5.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.69/5.54  --sup_immed_triv                        [TrivRules]
% 39.69/5.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.69/5.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.69/5.54  --sup_immed_bw_main                     []
% 39.69/5.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.69/5.54  --sup_input_triv                        [Unflattening;TrivRules]
% 39.69/5.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.69/5.54  --sup_input_bw                          []
% 39.69/5.54  
% 39.69/5.54  ------ Combination Options
% 39.69/5.54  
% 39.69/5.54  --comb_res_mult                         3
% 39.69/5.54  --comb_sup_mult                         2
% 39.69/5.54  --comb_inst_mult                        10
% 39.69/5.54  
% 39.69/5.54  ------ Debug Options
% 39.69/5.54  
% 39.69/5.54  --dbg_backtrace                         false
% 39.69/5.54  --dbg_dump_prop_clauses                 false
% 39.69/5.54  --dbg_dump_prop_clauses_file            -
% 39.69/5.54  --dbg_out_stat                          false
% 39.69/5.54  
% 39.69/5.54  
% 39.69/5.54  
% 39.69/5.54  
% 39.69/5.54  ------ Proving...
% 39.69/5.54  
% 39.69/5.54  
% 39.69/5.54  % SZS status Theorem for theBenchmark.p
% 39.69/5.54  
% 39.69/5.54  % SZS output start CNFRefutation for theBenchmark.p
% 39.69/5.54  
% 39.69/5.54  fof(f1,axiom,(
% 39.69/5.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f35,plain,(
% 39.69/5.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.69/5.54    inference(nnf_transformation,[],[f1])).
% 39.69/5.54  
% 39.69/5.54  fof(f36,plain,(
% 39.69/5.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.69/5.54    inference(flattening,[],[f35])).
% 39.69/5.54  
% 39.69/5.54  fof(f41,plain,(
% 39.69/5.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 39.69/5.54    inference(cnf_transformation,[],[f36])).
% 39.69/5.54  
% 39.69/5.54  fof(f70,plain,(
% 39.69/5.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.69/5.54    inference(equality_resolution,[],[f41])).
% 39.69/5.54  
% 39.69/5.54  fof(f12,axiom,(
% 39.69/5.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f55,plain,(
% 39.69/5.54    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 39.69/5.54    inference(cnf_transformation,[],[f12])).
% 39.69/5.54  
% 39.69/5.54  fof(f14,axiom,(
% 39.69/5.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f27,plain,(
% 39.69/5.54    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 39.69/5.54    inference(ennf_transformation,[],[f14])).
% 39.69/5.54  
% 39.69/5.54  fof(f28,plain,(
% 39.69/5.54    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 39.69/5.54    inference(flattening,[],[f27])).
% 39.69/5.54  
% 39.69/5.54  fof(f57,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f28])).
% 39.69/5.54  
% 39.69/5.54  fof(f54,plain,(
% 39.69/5.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 39.69/5.54    inference(cnf_transformation,[],[f12])).
% 39.69/5.54  
% 39.69/5.54  fof(f10,axiom,(
% 39.69/5.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f52,plain,(
% 39.69/5.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 39.69/5.54    inference(cnf_transformation,[],[f10])).
% 39.69/5.54  
% 39.69/5.54  fof(f9,axiom,(
% 39.69/5.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f24,plain,(
% 39.69/5.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 39.69/5.54    inference(ennf_transformation,[],[f9])).
% 39.69/5.54  
% 39.69/5.54  fof(f50,plain,(
% 39.69/5.54    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f24])).
% 39.69/5.54  
% 39.69/5.54  fof(f51,plain,(
% 39.69/5.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 39.69/5.54    inference(cnf_transformation,[],[f10])).
% 39.69/5.54  
% 39.69/5.54  fof(f16,axiom,(
% 39.69/5.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f31,plain,(
% 39.69/5.54    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 39.69/5.54    inference(ennf_transformation,[],[f16])).
% 39.69/5.54  
% 39.69/5.54  fof(f32,plain,(
% 39.69/5.54    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 39.69/5.54    inference(flattening,[],[f31])).
% 39.69/5.54  
% 39.69/5.54  fof(f59,plain,(
% 39.69/5.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f32])).
% 39.69/5.54  
% 39.69/5.54  fof(f40,plain,(
% 39.69/5.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.69/5.54    inference(cnf_transformation,[],[f36])).
% 39.69/5.54  
% 39.69/5.54  fof(f71,plain,(
% 39.69/5.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.69/5.54    inference(equality_resolution,[],[f40])).
% 39.69/5.54  
% 39.69/5.54  fof(f18,conjecture,(
% 39.69/5.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f19,negated_conjecture,(
% 39.69/5.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 39.69/5.54    inference(negated_conjecture,[],[f18])).
% 39.69/5.54  
% 39.69/5.54  fof(f33,plain,(
% 39.69/5.54    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 39.69/5.54    inference(ennf_transformation,[],[f19])).
% 39.69/5.54  
% 39.69/5.54  fof(f34,plain,(
% 39.69/5.54    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 39.69/5.54    inference(flattening,[],[f33])).
% 39.69/5.54  
% 39.69/5.54  fof(f38,plain,(
% 39.69/5.54    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 39.69/5.54    introduced(choice_axiom,[])).
% 39.69/5.54  
% 39.69/5.54  fof(f37,plain,(
% 39.69/5.54    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 39.69/5.54    introduced(choice_axiom,[])).
% 39.69/5.54  
% 39.69/5.54  fof(f39,plain,(
% 39.69/5.54    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 39.69/5.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37])).
% 39.69/5.54  
% 39.69/5.54  fof(f63,plain,(
% 39.69/5.54    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 39.69/5.54    inference(cnf_transformation,[],[f39])).
% 39.69/5.54  
% 39.69/5.54  fof(f3,axiom,(
% 39.69/5.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f21,plain,(
% 39.69/5.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.69/5.54    inference(ennf_transformation,[],[f3])).
% 39.69/5.54  
% 39.69/5.54  fof(f44,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f21])).
% 39.69/5.54  
% 39.69/5.54  fof(f2,axiom,(
% 39.69/5.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f20,plain,(
% 39.69/5.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 39.69/5.54    inference(ennf_transformation,[],[f2])).
% 39.69/5.54  
% 39.69/5.54  fof(f43,plain,(
% 39.69/5.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f20])).
% 39.69/5.54  
% 39.69/5.54  fof(f15,axiom,(
% 39.69/5.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f29,plain,(
% 39.69/5.54    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 39.69/5.54    inference(ennf_transformation,[],[f15])).
% 39.69/5.54  
% 39.69/5.54  fof(f30,plain,(
% 39.69/5.54    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 39.69/5.54    inference(flattening,[],[f29])).
% 39.69/5.54  
% 39.69/5.54  fof(f58,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f30])).
% 39.69/5.54  
% 39.69/5.54  fof(f6,axiom,(
% 39.69/5.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f47,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 39.69/5.54    inference(cnf_transformation,[],[f6])).
% 39.69/5.54  
% 39.69/5.54  fof(f5,axiom,(
% 39.69/5.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f46,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f5])).
% 39.69/5.54  
% 39.69/5.54  fof(f65,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 39.69/5.54    inference(definition_unfolding,[],[f47,f46])).
% 39.69/5.54  
% 39.69/5.54  fof(f68,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 39.69/5.54    inference(definition_unfolding,[],[f58,f65])).
% 39.69/5.54  
% 39.69/5.54  fof(f17,axiom,(
% 39.69/5.54    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f60,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 39.69/5.54    inference(cnf_transformation,[],[f17])).
% 39.69/5.54  
% 39.69/5.54  fof(f69,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 39.69/5.54    inference(definition_unfolding,[],[f60,f65])).
% 39.69/5.54  
% 39.69/5.54  fof(f11,axiom,(
% 39.69/5.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f25,plain,(
% 39.69/5.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 39.69/5.54    inference(ennf_transformation,[],[f11])).
% 39.69/5.54  
% 39.69/5.54  fof(f53,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f25])).
% 39.69/5.54  
% 39.69/5.54  fof(f7,axiom,(
% 39.69/5.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f22,plain,(
% 39.69/5.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 39.69/5.54    inference(ennf_transformation,[],[f7])).
% 39.69/5.54  
% 39.69/5.54  fof(f48,plain,(
% 39.69/5.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f22])).
% 39.69/5.54  
% 39.69/5.54  fof(f13,axiom,(
% 39.69/5.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f26,plain,(
% 39.69/5.54    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 39.69/5.54    inference(ennf_transformation,[],[f13])).
% 39.69/5.54  
% 39.69/5.54  fof(f56,plain,(
% 39.69/5.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f26])).
% 39.69/5.54  
% 39.69/5.54  fof(f67,plain,(
% 39.69/5.54    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 39.69/5.54    inference(definition_unfolding,[],[f56,f65])).
% 39.69/5.54  
% 39.69/5.54  fof(f61,plain,(
% 39.69/5.54    v1_relat_1(sK0)),
% 39.69/5.54    inference(cnf_transformation,[],[f39])).
% 39.69/5.54  
% 39.69/5.54  fof(f8,axiom,(
% 39.69/5.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f23,plain,(
% 39.69/5.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 39.69/5.54    inference(ennf_transformation,[],[f8])).
% 39.69/5.54  
% 39.69/5.54  fof(f49,plain,(
% 39.69/5.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f23])).
% 39.69/5.54  
% 39.69/5.54  fof(f62,plain,(
% 39.69/5.54    v1_funct_1(sK0)),
% 39.69/5.54    inference(cnf_transformation,[],[f39])).
% 39.69/5.54  
% 39.69/5.54  fof(f4,axiom,(
% 39.69/5.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 39.69/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.69/5.54  
% 39.69/5.54  fof(f45,plain,(
% 39.69/5.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f4])).
% 39.69/5.54  
% 39.69/5.54  fof(f66,plain,(
% 39.69/5.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 39.69/5.54    inference(definition_unfolding,[],[f45,f65])).
% 39.69/5.54  
% 39.69/5.54  fof(f42,plain,(
% 39.69/5.54    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 39.69/5.54    inference(cnf_transformation,[],[f36])).
% 39.69/5.54  
% 39.69/5.54  fof(f64,plain,(
% 39.69/5.54    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 39.69/5.54    inference(cnf_transformation,[],[f39])).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1,plain,
% 39.69/5.54      ( r1_tarski(X0,X0) ),
% 39.69/5.54      inference(cnf_transformation,[],[f70]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_632,plain,
% 39.69/5.54      ( r1_tarski(X0,X0) = iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_12,plain,
% 39.69/5.54      ( v1_funct_1(k6_relat_1(X0)) ),
% 39.69/5.54      inference(cnf_transformation,[],[f55]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_15,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 39.69/5.54      | ~ v1_funct_1(X1)
% 39.69/5.54      | ~ v1_relat_1(X1)
% 39.69/5.54      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 39.69/5.54      inference(cnf_transformation,[],[f57]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_246,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 39.69/5.54      | ~ v1_relat_1(X1)
% 39.69/5.54      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 39.69/5.54      | k6_relat_1(X2) != X1 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_247,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
% 39.69/5.54      | ~ v1_relat_1(k6_relat_1(X1))
% 39.69/5.54      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_246]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_13,plain,
% 39.69/5.54      ( v1_relat_1(k6_relat_1(X0)) ),
% 39.69/5.54      inference(cnf_transformation,[],[f54]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_257,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
% 39.69/5.54      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
% 39.69/5.54      inference(forward_subsumption_resolution,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_247,c_13]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_626,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
% 39.69/5.54      | r1_tarski(X1,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_9,plain,
% 39.69/5.54      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 39.69/5.54      inference(cnf_transformation,[],[f52]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_638,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
% 39.69/5.54      | r1_tarski(X1,X0) != iProver_top ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_626,c_9]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5131,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0 ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_632,c_638]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_8,plain,
% 39.69/5.54      ( ~ v1_relat_1(X0)
% 39.69/5.54      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 39.69/5.54      inference(cnf_transformation,[],[f50]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_352,plain,
% 39.69/5.54      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 39.69/5.54      | k6_relat_1(X1) != X0 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_353,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_352]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_10,plain,
% 39.69/5.54      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 39.69/5.54      inference(cnf_transformation,[],[f51]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_635,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_353,c_9,c_10]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5143,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_5131,c_635]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_17,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 39.69/5.54      | ~ r1_tarski(X0,k1_relat_1(X1))
% 39.69/5.54      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 39.69/5.54      | ~ v1_funct_1(X1)
% 39.69/5.54      | ~ v1_relat_1(X1) ),
% 39.69/5.54      inference(cnf_transformation,[],[f59]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_226,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 39.69/5.54      | ~ r1_tarski(X0,k1_relat_1(X1))
% 39.69/5.54      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 39.69/5.54      | ~ v1_relat_1(X1)
% 39.69/5.54      | k6_relat_1(X3) != X1 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_227,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
% 39.69/5.54      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
% 39.69/5.54      | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2)
% 39.69/5.54      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_226]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_239,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
% 39.69/5.54      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
% 39.69/5.54      | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) ),
% 39.69/5.54      inference(forward_subsumption_resolution,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_227,c_13]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_627,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 39.69/5.54      | r1_tarski(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top
% 39.69/5.54      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_639,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.69/5.54      | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 39.69/5.54      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_627,c_10]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5788,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.69/5.54      | r1_tarski(X0,X0) != iProver_top
% 39.69/5.54      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_5143,c_639]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2,plain,
% 39.69/5.54      ( r1_tarski(X0,X0) ),
% 39.69/5.54      inference(cnf_transformation,[],[f71]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_68,plain,
% 39.69/5.54      ( r1_tarski(X0,X0) = iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_140282,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.69/5.54      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_5788,c_68]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_20,negated_conjecture,
% 39.69/5.54      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 39.69/5.54      inference(cnf_transformation,[],[f63]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_628,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_4,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 39.69/5.54      inference(cnf_transformation,[],[f44]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_630,plain,
% 39.69/5.54      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2105,plain,
% 39.69/5.54      ( k2_xboole_0(k10_relat_1(sK0,sK2),sK1) = sK1 ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_628,c_630]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_3,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 39.69/5.54      inference(cnf_transformation,[],[f43]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_631,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) = iProver_top
% 39.69/5.54      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_3084,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(sK0,sK2),X0) = iProver_top
% 39.69/5.54      | r1_tarski(sK1,X0) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2105,c_631]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5217,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,sK2))) = k10_relat_1(sK0,sK2)
% 39.69/5.54      | r1_tarski(sK1,X0) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_3084,c_638]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_16,plain,
% 39.69/5.54      ( ~ v1_funct_1(X0)
% 39.69/5.54      | ~ v1_relat_1(X0)
% 39.69/5.54      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 39.69/5.54      inference(cnf_transformation,[],[f68]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_263,plain,
% 39.69/5.54      ( ~ v1_relat_1(X0)
% 39.69/5.54      | k6_relat_1(X1) != X0
% 39.69/5.54      | k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X2)) ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_264,plain,
% 39.69/5.54      ( ~ v1_relat_1(k6_relat_1(X0))
% 39.69/5.54      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_263]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_268,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_264,c_13]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_269,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 39.69/5.54      inference(renaming,[status(thm)],[c_268]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_637,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_269,c_10]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5782,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_5143,c_637]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_18,plain,
% 39.69/5.54      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 39.69/5.54      inference(cnf_transformation,[],[f69]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_11,plain,
% 39.69/5.54      ( ~ v1_relat_1(X0)
% 39.69/5.54      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 39.69/5.54      inference(cnf_transformation,[],[f53]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_346,plain,
% 39.69/5.54      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 39.69/5.54      | k6_relat_1(X2) != X1 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_347,plain,
% 39.69/5.54      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_346]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_636,plain,
% 39.69/5.54      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_18,c_347]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1933,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_636,c_9]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_6,plain,
% 39.69/5.54      ( ~ v1_relat_1(X0)
% 39.69/5.54      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 39.69/5.54      inference(cnf_transformation,[],[f48]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_367,plain,
% 39.69/5.54      ( k6_relat_1(X0) != X1
% 39.69/5.54      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_368,plain,
% 39.69/5.54      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_367]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1939,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_1933,c_368]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5783,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_5782,c_1939]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_80281,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0) = k10_relat_1(sK0,sK2)
% 39.69/5.54      | r1_tarski(sK1,X0) != iProver_top ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_5217,c_5783]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_140346,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(k6_relat_1(sK1),X0)) = k10_relat_1(sK0,sK2)
% 39.69/5.54      | r1_tarski(sK1,X0) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_140282,c_80281]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_14,plain,
% 39.69/5.54      ( ~ v1_relat_1(X0)
% 39.69/5.54      | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 39.69/5.54      inference(cnf_transformation,[],[f67]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_22,negated_conjecture,
% 39.69/5.54      ( v1_relat_1(sK0) ),
% 39.69/5.54      inference(cnf_transformation,[],[f61]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_373,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 39.69/5.54      | sK0 != X1 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_374,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_373]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1926,plain,
% 39.69/5.54      ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)) = k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_374,c_636]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_340,plain,
% 39.69/5.54      ( k6_relat_1(X0) != X1
% 39.69/5.54      | k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3))) = k10_relat_1(k7_relat_1(X1,X2),X3) ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_14,c_13]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_341,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k6_relat_1(X1),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_340]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_8564,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1939,c_341]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_140396,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,sK1),sK2)),X0) = k10_relat_1(sK0,sK2)
% 39.69/5.54      | r1_tarski(sK1,X0) != iProver_top ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_140346,c_1926,c_8564]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_142350,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,sK1),sK2)),sK1) = k10_relat_1(sK0,sK2) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_632,c_140396]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1925,plain,
% 39.69/5.54      ( k6_relat_1(k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X0),X2)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_341,c_636]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 39.69/5.54      inference(cnf_transformation,[],[f49]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_358,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
% 39.69/5.54      | k6_relat_1(X2) != X0 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_359,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_358]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_623,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) = iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_634,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_623,c_10]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_21,negated_conjecture,
% 39.69/5.54      ( v1_funct_1(sK0) ),
% 39.69/5.54      inference(cnf_transformation,[],[f62]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_295,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 39.69/5.54      | ~ v1_relat_1(X1)
% 39.69/5.54      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 39.69/5.54      | sK0 != X1 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_296,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,k2_relat_1(sK0))
% 39.69/5.54      | ~ v1_relat_1(sK0)
% 39.69/5.54      | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0 ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_295]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_300,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,k2_relat_1(sK0))
% 39.69/5.54      | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0 ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_296,c_22]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_624,plain,
% 39.69/5.54      ( k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0
% 39.69/5.54      | r1_tarski(X0,k2_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1454,plain,
% 39.69/5.54      ( k9_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))) = k2_relat_1(sK0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_632,c_624]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_385,plain,
% 39.69/5.54      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | sK0 != X0 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_386,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_385]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1455,plain,
% 39.69/5.54      ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_1454,c_386]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_313,plain,
% 39.69/5.54      ( ~ v1_relat_1(X0)
% 39.69/5.54      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 39.69/5.54      | sK0 != X0 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_314,plain,
% 39.69/5.54      ( ~ v1_relat_1(sK0)
% 39.69/5.54      | k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK0,k1_relat_1(sK0)))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_313]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_318,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK0,k1_relat_1(sK0)))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_314,c_22]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1456,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_1455,c_318]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5,plain,
% 39.69/5.54      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 39.69/5.54      inference(cnf_transformation,[],[f66]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_629,plain,
% 39.69/5.54      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1913,plain,
% 39.69/5.54      ( r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1456,c_629]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2377,plain,
% 39.69/5.54      ( k2_xboole_0(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = X0 ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1913,c_630]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7017,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.69/5.54      | r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X1) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2377,c_631]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_274,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 39.69/5.54      | ~ r1_tarski(X0,k1_relat_1(X1))
% 39.69/5.54      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 39.69/5.54      | ~ v1_relat_1(X1)
% 39.69/5.54      | sK0 != X1 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_275,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,X1))
% 39.69/5.54      | ~ r1_tarski(X0,k1_relat_1(sK0))
% 39.69/5.54      | ~ r1_tarski(k9_relat_1(sK0,X0),X1)
% 39.69/5.54      | ~ v1_relat_1(sK0) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_274]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_279,plain,
% 39.69/5.54      ( ~ r1_tarski(k9_relat_1(sK0,X0),X1)
% 39.69/5.54      | ~ r1_tarski(X0,k1_relat_1(sK0))
% 39.69/5.54      | r1_tarski(X0,k10_relat_1(sK0,X1)) ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_275,c_22]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_280,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,X1))
% 39.69/5.54      | ~ r1_tarski(X0,k1_relat_1(sK0))
% 39.69/5.54      | ~ r1_tarski(k9_relat_1(sK0,X0),X1) ),
% 39.69/5.54      inference(renaming,[status(thm)],[c_279]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_625,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,X1)) = iProver_top
% 39.69/5.54      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top
% 39.69/5.54      | r1_tarski(k9_relat_1(sK0,X0),X1) != iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_23408,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.69/5.54      | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = iProver_top
% 39.69/5.54      | r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_7017,c_625]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_390,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | sK0 != X0 ),
% 39.69/5.54      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_391,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) ),
% 39.69/5.54      inference(unflattening,[status(thm)],[c_390]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_392,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) = iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_25179,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = iProver_top
% 39.69/5.54      | r1_tarski(X0,X1) != iProver_top ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_23408,c_392]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_25180,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.69/5.54      | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = iProver_top ),
% 39.69/5.54      inference(renaming,[status(thm)],[c_25179]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_25193,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,X1))) = k10_relat_1(sK0,X1)
% 39.69/5.54      | r1_tarski(X1,X0) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_25180,c_638]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2623,plain,
% 39.69/5.54      ( k2_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1926,c_368]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2626,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_2623,c_9]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_4651,plain,
% 39.69/5.54      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X1)),X1))) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2626,c_637]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_4659,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_4651,c_1939]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5791,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = k10_relat_1(sK0,X0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_5143,c_2626]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_25197,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X1) = k10_relat_1(sK0,X0)
% 39.69/5.54      | r1_tarski(X0,X1) != iProver_top ),
% 39.69/5.54      inference(demodulation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_25193,c_2626,c_4659,c_5791]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_48436,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),X0) = k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_634,c_25197]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1340,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_635,c_341]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7002,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k9_relat_1(k6_relat_1(X1),X0) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_1340,c_1939]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7004,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X0) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1926,c_7002]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_53062,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_48436,c_7004]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_53107,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_53062,c_635,c_2626]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_53694,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),k10_relat_1(sK0,X0)) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_53107,c_7004]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_53725,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),k10_relat_1(sK0,X0)) = k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_53694,c_2626,c_48436]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_56388,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),X2),k10_relat_1(sK0,X0)) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1)))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_53725,c_341]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_56411,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))),X2),k10_relat_1(sK0,X0)) = k10_relat_1(k7_relat_1(sK0,X2),k10_relat_1(k6_relat_1(X0),X1)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_56388,c_374]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_56745,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(sK0,X0)) = k10_relat_1(k7_relat_1(sK0,X1),k10_relat_1(k6_relat_1(X0),X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_635,c_56411]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_56788,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(sK0,X0)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_56745,c_635]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_58818,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)),X2)),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X2)),X1) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1925,c_56788]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_58860,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X2)),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X2)),X1) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_58818,c_1926]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_143799,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(sK1),sK1)),sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_142350,c_58860]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_3082,plain,
% 39.69/5.54      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_632,c_631]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5915,plain,
% 39.69/5.54      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_3082,c_631]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7144,plain,
% 39.69/5.54      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_5915,c_631]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_10564,plain,
% 39.69/5.54      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3),X4)) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_7144,c_631]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5676,plain,
% 39.69/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.69/5.54      | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X0))) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_632,c_639]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_36834,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),k9_relat_1(sK0,X0))))) = iProver_top
% 39.69/5.54      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top
% 39.69/5.54      | r1_tarski(k9_relat_1(sK0,X0),X1) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_5676,c_625]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_622,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) = iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_0,plain,
% 39.69/5.54      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 39.69/5.54      inference(cnf_transformation,[],[f42]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_633,plain,
% 39.69/5.54      ( X0 = X1
% 39.69/5.54      | r1_tarski(X0,X1) != iProver_top
% 39.69/5.54      | r1_tarski(X1,X0) != iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_4205,plain,
% 39.69/5.54      ( k10_relat_1(sK0,X0) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k10_relat_1(sK0,X0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_622,c_633]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_46706,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),k9_relat_1(sK0,k1_relat_1(sK0))))) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k9_relat_1(sK0,k1_relat_1(sK0)),X0) != iProver_top
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_36834,c_4205]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1928,plain,
% 39.69/5.54      ( k6_relat_1(k9_relat_1(sK0,k10_relat_1(sK0,X0))) = k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1456,c_636]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2605,plain,
% 39.69/5.54      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1928,c_9]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2913,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k2_relat_1(sK0)) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2605,c_368]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_46728,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
% 39.69/5.54      | r1_tarski(k2_relat_1(sK0),X0) != iProver_top ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_46706,c_1455,c_2913]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_754,plain,
% 39.69/5.54      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
% 39.69/5.54      inference(instantiation,[status(thm)],[c_1]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_755,plain,
% 39.69/5.54      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top ),
% 39.69/5.54      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_47319,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k2_relat_1(sK0),X0) != iProver_top ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_46728,c_755]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_47339,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k9_relat_1(sK0,k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3))))) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_10564,c_47319]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2103,plain,
% 39.69/5.54      ( k2_xboole_0(X0,X0) = X0 ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_632,c_630]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_14211,plain,
% 39.69/5.54      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3),X4),X5)) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_10564,c_631]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_19598,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k9_relat_1(sK0,X0),X1),X2),X3),X4),X5))) = iProver_top
% 39.69/5.54      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_14211,c_625]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_23072,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k9_relat_1(sK0,k1_relat_1(sK0)),X0),X1),X2),X3),X4)) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_19598,c_4205]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_23077,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3),X4)) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_23072,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_24432,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3),X4)) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_23077,c_755]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_24447,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2103,c_24432]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_47353,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_47339,c_1455,c_24447]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_57471,plain,
% 39.69/5.54      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_47353,c_1913]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_57484,plain,
% 39.69/5.54      ( r1_tarski(k2_relat_1(sK0),k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))) = iProver_top ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_57471,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_58435,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))),k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0)))))) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_57484,c_47319]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_58438,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))),k2_relat_1(sK0))) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_58435,c_1455,c_47353]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_56755,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))),X1),k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,X1),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_386,c_56411]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1837,plain,
% 39.69/5.54      ( k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) = k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_634,c_624]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5139,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1913,c_638]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_31236,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) = k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1837,c_5139]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_31278,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) = k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_31236,c_1837]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_31279,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),X0) = k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_31278,c_635,c_5783,c_8564]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2599,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) = k6_relat_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_386,c_1928]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2611,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) = k6_relat_1(k2_relat_1(sK0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_2599,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_3410,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) = k2_relat_1(k6_relat_1(k2_relat_1(sK0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2611,c_368]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_3417,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) = k2_relat_1(sK0) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_3410,c_9,c_2913]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_4652,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_3417,c_637]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_4658,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_4652,c_1456]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1941,plain,
% 39.69/5.54      ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_1939,c_636]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_9417,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k6_relat_1(k9_relat_1(sK0,k10_relat_1(sK0,X0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_4658,c_1941]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_9490,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_9417,c_1928]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_31280,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0)),X0) = k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_31279,c_9490]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_31281,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_31280,c_7002]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_56775,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))),X1),k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,X1),k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_56755,c_31281]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_47328,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k9_relat_1(sK0,k10_relat_1(sK0,k2_xboole_0(k2_relat_1(sK0),X0))))) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_3082,c_47319]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5917,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,k2_xboole_0(k9_relat_1(sK0,X0),X1))) = iProver_top
% 39.69/5.54      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_3082,c_625]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_6891,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k9_relat_1(sK0,k1_relat_1(sK0)),X0)) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_5917,c_4205]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_6892,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_relat_1(sK0),X0)) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_6891,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7610,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_relat_1(sK0),X0)) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_6892,c_755]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_47357,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_47328,c_1455,c_7610]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_49075,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))),k2_relat_1(sK0)) = k6_relat_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_47357,c_1928]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_49083,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))),k2_relat_1(sK0)) = k6_relat_1(k2_relat_1(sK0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_49075,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_50081,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) = k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_49083,c_7002]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7622,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0)) = k6_relat_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_7610,c_1928]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7628,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0)) = k6_relat_1(k2_relat_1(sK0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_7622,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_50122,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) = k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0)) ),
% 39.69/5.54      inference(demodulation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_50081,c_7628,c_8564,c_31281]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_50123,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k2_relat_1(sK0)),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X0)),k2_relat_1(sK0))) = k2_relat_1(sK0) ),
% 39.69/5.54      inference(demodulation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_50122,c_386,c_1455,c_2913,c_31281]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_50927,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X1)),k2_relat_1(sK0))) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_50123,c_341]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_50949,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k10_relat_1(k6_relat_1(k2_xboole_0(k2_relat_1(sK0),X1)),k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_50927,c_1456]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_63829,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k10_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2103,c_50949]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_63852,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k9_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_relat_1(sK0))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_63829,c_31281]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_63853,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k9_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_63852,c_2913]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_63854,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(sK0)),X0),k2_relat_1(sK0)) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_63853,c_386,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_63956,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(sK0)),X1)),k2_relat_1(sK0)) = k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(X0),X1))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1925,c_63854]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_68276,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k2_relat_1(sK0)) = k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2611,c_63956]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_68332,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)),k2_relat_1(sK0)) = k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_68276,c_1837,c_31281]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_68333,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k9_relat_1(sK0,k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_68332,c_1941,c_63854]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_82484,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),X1),k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,X1),k9_relat_1(sK0,k10_relat_1(sK0,X0))) ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_56775,c_56775,c_68333]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_82487,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),X1)),k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X1)),k9_relat_1(sK0,k10_relat_1(sK0,X0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1926,c_82484]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_130310,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X1),X2),X3),X4)),k2_relat_1(sK0))),k2_relat_1(sK0))))) = k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),X0)),k1_relat_1(sK0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_58438,c_82487]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_130404,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X1),X2),X3),X4)),k2_relat_1(sK0))),k2_relat_1(sK0))))) = k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0)),k1_relat_1(sK0)) ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_130310,c_386,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_10563,plain,
% 39.69/5.54      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_7144,c_630]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_47331,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k9_relat_1(sK0,k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1))))) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_5915,c_47319]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7146,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k9_relat_1(sK0,X0),X1),X2))) = iProver_top
% 39.69/5.54      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_5915,c_625]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_8812,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k9_relat_1(sK0,k1_relat_1(sK0)),X0),X1)) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_7146,c_4205]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_8813,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)) = k1_relat_1(sK0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_8812,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_8855,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_8813,c_755]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_47355,plain,
% 39.69/5.54      ( k10_relat_1(sK0,k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_47331,c_1455,c_8855]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_49753,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))),k2_relat_1(sK0)) = k6_relat_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_47355,c_1928]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_49761,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))),k2_relat_1(sK0)) = k6_relat_1(k2_relat_1(sK0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_49753,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_68281,plain,
% 39.69/5.54      ( k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))),X2))) = k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK0)),X2)),k2_relat_1(sK0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_49761,c_63956]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_68327,plain,
% 39.69/5.54      ( k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1)),k2_relat_1(sK0))),X2))) = k9_relat_1(sK0,k10_relat_1(sK0,X2)) ),
% 39.69/5.54      inference(demodulation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_68281,c_1941,c_31281,c_63854]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_85445,plain,
% 39.69/5.54      ( k9_relat_1(sK0,k10_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_relat_1(sK0),X0),X1),X2),X3)),k2_relat_1(sK0))),X4))) = k9_relat_1(sK0,k10_relat_1(sK0,X4)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_10563,c_68327]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_2106,plain,
% 39.69/5.54      ( k2_xboole_0(k10_relat_1(sK0,X0),k1_relat_1(sK0)) = k1_relat_1(sK0) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_622,c_630]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1636,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,k9_relat_1(sK0,X0))) = iProver_top
% 39.69/5.54      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_632,c_625]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_3083,plain,
% 39.69/5.54      ( r1_tarski(X0,k10_relat_1(sK0,k9_relat_1(sK0,k2_xboole_0(X0,X1)))) = iProver_top
% 39.69/5.54      | r1_tarski(k2_xboole_0(X0,X1),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1636,c_631]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_44726,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k2_xboole_0(X0,X1)))),k10_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k2_xboole_0(X0,X1)))),X0)) = X0
% 39.69/5.54      | r1_tarski(k2_xboole_0(X0,X1),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_3083,c_638]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_44753,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,X0),k9_relat_1(sK0,k2_xboole_0(X0,X1))) = X0
% 39.69/5.54      | r1_tarski(k2_xboole_0(X0,X1),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(demodulation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_44726,c_2626,c_4659,c_5791]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_118607,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k2_xboole_0(k10_relat_1(sK0,X0),k1_relat_1(sK0)))) = k10_relat_1(sK0,X0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_2106,c_44753]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_118769,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k2_relat_1(sK0)) = k10_relat_1(sK0,X0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_118607,c_1455,c_2106]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_3078,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,X0),k2_relat_1(sK0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(sK0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_386,c_2626]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_118770,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k1_relat_1(sK0)) = k10_relat_1(sK0,X0)
% 39.69/5.54      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_118769,c_3078]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_118980,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k1_relat_1(sK0)) = k10_relat_1(sK0,X0) ),
% 39.69/5.54      inference(global_propositional_subsumption,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_118770,c_755]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_130405,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))) = k10_relat_1(sK0,X0) ),
% 39.69/5.54      inference(demodulation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_130404,c_7004,c_85445,c_118980]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_130406,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k2_relat_1(sK0)) = k10_relat_1(sK0,X0) ),
% 39.69/5.54      inference(light_normalisation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_130405,c_386,c_1455]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_132856,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k9_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X0)) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_4659,c_4659,c_5791]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_132857,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_132856,c_2626,c_4659]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1910,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_341,c_629]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_7345,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1910,c_638]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_132917,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)),X2)),X1) = k10_relat_1(k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)),X2) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_132857,c_7345]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_132932,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X2)),X1) = k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X2) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_132917,c_1926]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_133933,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k2_relat_1(sK0))),X1) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k2_relat_1(sK0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_130406,c_132932]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_134143,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k2_relat_1(sK0)) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_133933,c_130406]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_1911,plain,
% 39.69/5.54      ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),X0) = iProver_top ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_374,c_629]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_5138,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k10_relat_1(k7_relat_1(sK0,X0),X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_1911,c_638]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_135880,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1))) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k2_relat_1(sK0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_134143,c_5138]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_135899,plain,
% 39.69/5.54      ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1))) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_135880,c_134143]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_135900,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)),X1) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) ),
% 39.69/5.54      inference(demodulation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_135899,c_635,c_5783,c_8564]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_132912,plain,
% 39.69/5.54      ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k6_relat_1(k10_relat_1(k7_relat_1(sK0,X1),X0)) ),
% 39.69/5.54      inference(superposition,[status(thm)],[c_132857,c_1941]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_135901,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X0) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
% 39.69/5.54      inference(light_normalisation,[status(thm)],[c_135900,c_132912]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_135902,plain,
% 39.69/5.54      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_135901,c_7004]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_143812,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,sK2)),sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 39.69/5.54      inference(demodulation,
% 39.69/5.54                [status(thm)],
% 39.69/5.54                [c_143799,c_635,c_2626,c_135902]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_143813,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 39.69/5.54      inference(demodulation,[status(thm)],[c_143812,c_5791]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_418,plain,( X0 = X0 ),theory(equality) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_869,plain,
% 39.69/5.54      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 39.69/5.54      inference(instantiation,[status(thm)],[c_418]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_419,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_668,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
% 39.69/5.54      | k10_relat_1(sK0,sK2) != X0
% 39.69/5.54      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 39.69/5.54      inference(instantiation,[status(thm)],[c_419]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_744,plain,
% 39.69/5.54      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
% 39.69/5.54      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 39.69/5.54      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 39.69/5.54      inference(instantiation,[status(thm)],[c_668]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(c_19,negated_conjecture,
% 39.69/5.54      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 39.69/5.54      inference(cnf_transformation,[],[f64]) ).
% 39.69/5.54  
% 39.69/5.54  cnf(contradiction,plain,
% 39.69/5.54      ( $false ),
% 39.69/5.54      inference(minisat,[status(thm)],[c_143813,c_869,c_744,c_19]) ).
% 39.69/5.54  
% 39.69/5.54  
% 39.69/5.54  % SZS output end CNFRefutation for theBenchmark.p
% 39.69/5.54  
% 39.69/5.54  ------                               Statistics
% 39.69/5.54  
% 39.69/5.54  ------ General
% 39.69/5.54  
% 39.69/5.54  abstr_ref_over_cycles:                  0
% 39.69/5.54  abstr_ref_under_cycles:                 0
% 39.69/5.54  gc_basic_clause_elim:                   0
% 39.69/5.54  forced_gc_time:                         0
% 39.69/5.54  parsing_time:                           0.01
% 39.69/5.54  unif_index_cands_time:                  0.
% 39.69/5.54  unif_index_add_time:                    0.
% 39.69/5.54  orderings_time:                         0.
% 39.69/5.54  out_proof_time:                         0.043
% 39.69/5.54  total_time:                             5.001
% 39.69/5.54  num_of_symbols:                         47
% 39.69/5.54  num_of_terms:                           176162
% 39.69/5.54  
% 39.69/5.54  ------ Preprocessing
% 39.69/5.54  
% 39.69/5.54  num_of_splits:                          0
% 39.69/5.54  num_of_split_atoms:                     0
% 39.69/5.54  num_of_reused_defs:                     0
% 39.69/5.54  num_eq_ax_congr_red:                    9
% 39.69/5.54  num_of_sem_filtered_clauses:            1
% 39.69/5.54  num_of_subtypes:                        0
% 39.69/5.54  monotx_restored_types:                  0
% 39.69/5.54  sat_num_of_epr_types:                   0
% 39.69/5.54  sat_num_of_non_cyclic_types:            0
% 39.69/5.54  sat_guarded_non_collapsed_types:        0
% 39.69/5.54  num_pure_diseq_elim:                    0
% 39.69/5.54  simp_replaced_by:                       0
% 39.69/5.54  res_preprocessed:                       99
% 39.69/5.54  prep_upred:                             0
% 39.69/5.54  prep_unflattend:                        16
% 39.69/5.54  smt_new_axioms:                         0
% 39.69/5.54  pred_elim_cands:                        3
% 39.69/5.54  pred_elim:                              2
% 39.69/5.54  pred_elim_cl:                           -4
% 39.69/5.54  pred_elim_cycles:                       3
% 39.69/5.54  merged_defs:                            0
% 39.69/5.54  merged_defs_ncl:                        0
% 39.69/5.54  bin_hyper_res:                          0
% 39.69/5.54  prep_cycles:                            3
% 39.69/5.54  pred_elim_time:                         0.004
% 39.69/5.54  splitting_time:                         0.
% 39.69/5.54  sem_filter_time:                        0.
% 39.69/5.54  monotx_time:                            0.
% 39.69/5.54  subtype_inf_time:                       0.
% 39.69/5.54  
% 39.69/5.54  ------ Problem properties
% 39.69/5.54  
% 39.69/5.54  clauses:                                26
% 39.69/5.54  conjectures:                            2
% 39.69/5.54  epr:                                    2
% 39.69/5.54  horn:                                   26
% 39.69/5.54  ground:                                 3
% 39.69/5.54  unary:                                  19
% 39.69/5.54  binary:                                 4
% 39.69/5.54  lits:                                   36
% 39.69/5.54  lits_eq:                                18
% 39.69/5.54  fd_pure:                                0
% 39.69/5.54  fd_pseudo:                              0
% 39.69/5.54  fd_cond:                                0
% 39.69/5.54  fd_pseudo_cond:                         1
% 39.69/5.54  ac_symbols:                             0
% 39.69/5.54  
% 39.69/5.54  ------ Propositional Solver
% 39.69/5.54  
% 39.69/5.54  prop_solver_calls:                      64
% 39.69/5.54  prop_fast_solver_calls:                 1510
% 39.69/5.54  smt_solver_calls:                       0
% 39.69/5.54  smt_fast_solver_calls:                  0
% 39.69/5.54  prop_num_of_clauses:                    61964
% 39.69/5.54  prop_preprocess_simplified:             78737
% 39.69/5.54  prop_fo_subsumed:                       40
% 39.69/5.54  prop_solver_time:                       0.
% 39.69/5.54  smt_solver_time:                        0.
% 39.69/5.54  smt_fast_solver_time:                   0.
% 39.69/5.54  prop_fast_solver_time:                  0.
% 39.69/5.54  prop_unsat_core_time:                   0.008
% 39.69/5.54  
% 39.69/5.54  ------ QBF
% 39.69/5.54  
% 39.69/5.54  qbf_q_res:                              0
% 39.69/5.54  qbf_num_tautologies:                    0
% 39.69/5.54  qbf_prep_cycles:                        0
% 39.69/5.54  
% 39.69/5.54  ------ BMC1
% 39.69/5.54  
% 39.69/5.54  bmc1_current_bound:                     -1
% 39.69/5.54  bmc1_last_solved_bound:                 -1
% 39.69/5.54  bmc1_unsat_core_size:                   -1
% 39.69/5.54  bmc1_unsat_core_parents_size:           -1
% 39.69/5.54  bmc1_merge_next_fun:                    0
% 39.69/5.54  bmc1_unsat_core_clauses_time:           0.
% 39.69/5.54  
% 39.69/5.54  ------ Instantiation
% 39.69/5.54  
% 39.69/5.54  inst_num_of_clauses:                    1306
% 39.69/5.54  inst_num_in_passive:                    409
% 39.69/5.54  inst_num_in_active:                     2816
% 39.69/5.54  inst_num_in_unprocessed:                500
% 39.69/5.54  inst_num_of_loops:                      3399
% 39.69/5.54  inst_num_of_learning_restarts:          1
% 39.69/5.54  inst_num_moves_active_passive:          580
% 39.69/5.54  inst_lit_activity:                      0
% 39.69/5.54  inst_lit_activity_moves:                2
% 39.69/5.54  inst_num_tautologies:                   0
% 39.69/5.54  inst_num_prop_implied:                  0
% 39.69/5.54  inst_num_existing_simplified:           0
% 39.69/5.54  inst_num_eq_res_simplified:             0
% 39.69/5.54  inst_num_child_elim:                    0
% 39.69/5.54  inst_num_of_dismatching_blockings:      16068
% 39.69/5.54  inst_num_of_non_proper_insts:           16728
% 39.69/5.54  inst_num_of_duplicates:                 0
% 39.69/5.54  inst_inst_num_from_inst_to_res:         0
% 39.69/5.54  inst_dismatching_checking_time:         0.
% 39.69/5.54  
% 39.69/5.54  ------ Resolution
% 39.69/5.54  
% 39.69/5.54  res_num_of_clauses:                     38
% 39.69/5.54  res_num_in_passive:                     38
% 39.69/5.54  res_num_in_active:                      0
% 39.69/5.54  res_num_of_loops:                       102
% 39.69/5.54  res_forward_subset_subsumed:            1762
% 39.69/5.54  res_backward_subset_subsumed:           34
% 39.69/5.54  res_forward_subsumed:                   0
% 39.69/5.54  res_backward_subsumed:                  0
% 39.69/5.54  res_forward_subsumption_resolution:     2
% 39.69/5.54  res_backward_subsumption_resolution:    0
% 39.69/5.54  res_clause_to_clause_subsumption:       57541
% 39.69/5.54  res_orphan_elimination:                 0
% 39.69/5.54  res_tautology_del:                      815
% 39.69/5.54  res_num_eq_res_simplified:              0
% 39.69/5.54  res_num_sel_changes:                    0
% 39.69/5.54  res_moves_from_active_to_pass:          0
% 39.69/5.54  
% 39.69/5.54  ------ Superposition
% 39.69/5.54  
% 39.69/5.54  sup_time_total:                         0.
% 39.69/5.54  sup_time_generating:                    0.
% 39.69/5.54  sup_time_sim_full:                      0.
% 39.69/5.54  sup_time_sim_immed:                     0.
% 39.69/5.54  
% 39.69/5.54  sup_num_of_clauses:                     9286
% 39.69/5.54  sup_num_in_active:                      586
% 39.69/5.54  sup_num_in_passive:                     8700
% 39.69/5.54  sup_num_of_loops:                       679
% 39.69/5.54  sup_fw_superposition:                   10603
% 39.69/5.54  sup_bw_superposition:                   10473
% 39.69/5.54  sup_immediate_simplified:               9547
% 39.69/5.54  sup_given_eliminated:                   4
% 39.69/5.54  comparisons_done:                       0
% 39.69/5.54  comparisons_avoided:                    0
% 39.69/5.54  
% 39.69/5.54  ------ Simplifications
% 39.69/5.54  
% 39.69/5.54  
% 39.69/5.54  sim_fw_subset_subsumed:                 154
% 39.69/5.54  sim_bw_subset_subsumed:                 55
% 39.69/5.54  sim_fw_subsumed:                        1945
% 39.69/5.54  sim_bw_subsumed:                        84
% 39.69/5.54  sim_fw_subsumption_res:                 0
% 39.69/5.54  sim_bw_subsumption_res:                 0
% 39.69/5.54  sim_tautology_del:                      226
% 39.69/5.54  sim_eq_tautology_del:                   1552
% 39.69/5.54  sim_eq_res_simp:                        0
% 39.69/5.54  sim_fw_demodulated:                     5488
% 39.69/5.54  sim_bw_demodulated:                     181
% 39.69/5.54  sim_light_normalised:                   3951
% 39.69/5.54  sim_joinable_taut:                      0
% 39.69/5.54  sim_joinable_simp:                      0
% 39.69/5.54  sim_ac_normalised:                      0
% 39.69/5.54  sim_smt_subsumption:                    0
% 39.69/5.54  
%------------------------------------------------------------------------------
