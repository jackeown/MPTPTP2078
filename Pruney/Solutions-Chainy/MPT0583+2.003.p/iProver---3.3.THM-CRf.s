%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:57 EST 2020

% Result     : Theorem 55.16s
% Output     : CNFRefutation 55.16s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 683 expanded)
%              Number of clauses        :   61 ( 124 expanded)
%              Number of leaves         :   28 ( 204 expanded)
%              Depth                    :   21
%              Number of atoms          :  250 ( 846 expanded)
%              Number of equality atoms :  149 ( 703 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f17,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f84,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f91,plain,(
    ! [X0,X1] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f55,f85])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f61,f85])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f85])).

fof(f93,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f25,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r1_xboole_0(X1,k1_relat_1(X0))
           => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(X0,X1)
          & r1_xboole_0(X1,k1_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(X0,X1)
          & r1_xboole_0(X1,k1_relat_1(X0)) )
     => ( k1_xboole_0 != k7_relat_1(X0,sK2)
        & r1_xboole_0(sK2,k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k7_relat_1(X0,X1)
            & r1_xboole_0(X1,k1_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(sK1,X1)
          & r1_xboole_0(X1,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK2)
    & r1_xboole_0(sK2,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f46,f45])).

fof(f80,plain,(
    r1_xboole_0(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) ) ),
    inference(definition_unfolding,[],[f53,f85,f86])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,X0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f64,f86])).

fof(f19,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f18,axiom,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f70,f82])).

fof(f95,plain,(
    ! [X0] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f87])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    k1_xboole_0 != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1094,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
    | ~ v1_relat_1(sK1)
    | k9_relat_1(sK1,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_65337,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK2)
    | ~ v1_relat_1(sK1)
    | k9_relat_1(sK1,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1094])).

cnf(c_6,plain,
    ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_11,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_909,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1792,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_909])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_908,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2420,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_1792,c_908])).

cnf(c_12,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_13,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1383,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_13])).

cnf(c_1385,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1383,c_11])).

cnf(c_1408,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k5_enumset1(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1385,c_12])).

cnf(c_9,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1410,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1385,c_9])).

cnf(c_1411,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k5_enumset1(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1385,c_13])).

cnf(c_1418,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1408,c_1410,c_1411])).

cnf(c_1420,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1418,c_11,c_1385])).

cnf(c_2428,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2420,c_1420])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_906,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2734,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_906])).

cnf(c_3415,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2734,c_1792])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_899,plain,
    ( r1_xboole_0(sK2,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_907,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),X1)
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4281,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_relat_1(sK1)),sK2) = k2_xboole_0(k4_xboole_0(X0,sK2),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_899,c_907])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_912,plain,
    ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = iProver_top
    | r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1009,plain,
    ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = iProver_top
    | r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_912,c_12])).

cnf(c_5317,plain,
    ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k2_xboole_0(X1,k1_relat_1(sK1))))) = iProver_top
    | r1_tarski(X0,k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X1,k1_relat_1(sK1))),k2_xboole_0(k4_xboole_0(X1,sK2),k1_relat_1(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4281,c_1009])).

cnf(c_5904,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),k1_relat_1(sK1)),k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k2_xboole_0(X0,k1_relat_1(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3415,c_5317])).

cnf(c_7266,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK2),k1_relat_1(sK1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_5904])).

cnf(c_15,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_17,plain,
    ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_971,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15,c_17])).

cnf(c_1119,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_971,c_9])).

cnf(c_7287,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7266,c_1119,c_2428])).

cnf(c_7304,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7287])).

cnf(c_404,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1999,plain,
    ( k9_relat_1(sK1,sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k9_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_2000,plain,
    ( k9_relat_1(sK1,sK2) != k1_xboole_0
    | k1_xboole_0 = k9_relat_1(sK1,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1089,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1874,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,sK2)) = k9_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_1323,plain,
    ( k2_relat_1(k7_relat_1(sK1,sK2)) != X0
    | k2_relat_1(k7_relat_1(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_1873,plain,
    ( k2_relat_1(k7_relat_1(sK1,sK2)) != k9_relat_1(sK1,sK2)
    | k2_relat_1(k7_relat_1(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != k9_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1070,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1197,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1075,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | k2_relat_1(k7_relat_1(sK1,sK2)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_403,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_428,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65337,c_7304,c_2000,c_1874,c_1873,c_1197,c_1075,c_428,c_24,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.16/7.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.16/7.50  
% 55.16/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.16/7.50  
% 55.16/7.50  ------  iProver source info
% 55.16/7.50  
% 55.16/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.16/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.16/7.50  git: non_committed_changes: false
% 55.16/7.50  git: last_make_outside_of_git: false
% 55.16/7.50  
% 55.16/7.50  ------ 
% 55.16/7.50  
% 55.16/7.50  ------ Input Options
% 55.16/7.50  
% 55.16/7.50  --out_options                           all
% 55.16/7.50  --tptp_safe_out                         true
% 55.16/7.50  --problem_path                          ""
% 55.16/7.50  --include_path                          ""
% 55.16/7.50  --clausifier                            res/vclausify_rel
% 55.16/7.50  --clausifier_options                    --mode clausify
% 55.16/7.50  --stdin                                 false
% 55.16/7.50  --stats_out                             all
% 55.16/7.50  
% 55.16/7.50  ------ General Options
% 55.16/7.50  
% 55.16/7.50  --fof                                   false
% 55.16/7.50  --time_out_real                         305.
% 55.16/7.50  --time_out_virtual                      -1.
% 55.16/7.50  --symbol_type_check                     false
% 55.16/7.50  --clausify_out                          false
% 55.16/7.50  --sig_cnt_out                           false
% 55.16/7.50  --trig_cnt_out                          false
% 55.16/7.50  --trig_cnt_out_tolerance                1.
% 55.16/7.50  --trig_cnt_out_sk_spl                   false
% 55.16/7.50  --abstr_cl_out                          false
% 55.16/7.50  
% 55.16/7.50  ------ Global Options
% 55.16/7.50  
% 55.16/7.50  --schedule                              default
% 55.16/7.50  --add_important_lit                     false
% 55.16/7.50  --prop_solver_per_cl                    1000
% 55.16/7.50  --min_unsat_core                        false
% 55.16/7.50  --soft_assumptions                      false
% 55.16/7.50  --soft_lemma_size                       3
% 55.16/7.50  --prop_impl_unit_size                   0
% 55.16/7.50  --prop_impl_unit                        []
% 55.16/7.50  --share_sel_clauses                     true
% 55.16/7.50  --reset_solvers                         false
% 55.16/7.50  --bc_imp_inh                            [conj_cone]
% 55.16/7.50  --conj_cone_tolerance                   3.
% 55.16/7.50  --extra_neg_conj                        none
% 55.16/7.50  --large_theory_mode                     true
% 55.16/7.50  --prolific_symb_bound                   200
% 55.16/7.50  --lt_threshold                          2000
% 55.16/7.50  --clause_weak_htbl                      true
% 55.16/7.50  --gc_record_bc_elim                     false
% 55.16/7.50  
% 55.16/7.50  ------ Preprocessing Options
% 55.16/7.50  
% 55.16/7.50  --preprocessing_flag                    true
% 55.16/7.50  --time_out_prep_mult                    0.1
% 55.16/7.50  --splitting_mode                        input
% 55.16/7.50  --splitting_grd                         true
% 55.16/7.50  --splitting_cvd                         false
% 55.16/7.50  --splitting_cvd_svl                     false
% 55.16/7.50  --splitting_nvd                         32
% 55.16/7.50  --sub_typing                            true
% 55.16/7.50  --prep_gs_sim                           true
% 55.16/7.50  --prep_unflatten                        true
% 55.16/7.50  --prep_res_sim                          true
% 55.16/7.50  --prep_upred                            true
% 55.16/7.50  --prep_sem_filter                       exhaustive
% 55.16/7.50  --prep_sem_filter_out                   false
% 55.16/7.50  --pred_elim                             true
% 55.16/7.50  --res_sim_input                         true
% 55.16/7.50  --eq_ax_congr_red                       true
% 55.16/7.50  --pure_diseq_elim                       true
% 55.16/7.50  --brand_transform                       false
% 55.16/7.50  --non_eq_to_eq                          false
% 55.16/7.50  --prep_def_merge                        true
% 55.16/7.50  --prep_def_merge_prop_impl              false
% 55.16/7.50  --prep_def_merge_mbd                    true
% 55.16/7.50  --prep_def_merge_tr_red                 false
% 55.16/7.50  --prep_def_merge_tr_cl                  false
% 55.16/7.50  --smt_preprocessing                     true
% 55.16/7.50  --smt_ac_axioms                         fast
% 55.16/7.50  --preprocessed_out                      false
% 55.16/7.50  --preprocessed_stats                    false
% 55.16/7.50  
% 55.16/7.50  ------ Abstraction refinement Options
% 55.16/7.50  
% 55.16/7.50  --abstr_ref                             []
% 55.16/7.50  --abstr_ref_prep                        false
% 55.16/7.50  --abstr_ref_until_sat                   false
% 55.16/7.50  --abstr_ref_sig_restrict                funpre
% 55.16/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.16/7.50  --abstr_ref_under                       []
% 55.16/7.50  
% 55.16/7.50  ------ SAT Options
% 55.16/7.50  
% 55.16/7.50  --sat_mode                              false
% 55.16/7.50  --sat_fm_restart_options                ""
% 55.16/7.50  --sat_gr_def                            false
% 55.16/7.50  --sat_epr_types                         true
% 55.16/7.50  --sat_non_cyclic_types                  false
% 55.16/7.50  --sat_finite_models                     false
% 55.16/7.50  --sat_fm_lemmas                         false
% 55.16/7.50  --sat_fm_prep                           false
% 55.16/7.50  --sat_fm_uc_incr                        true
% 55.16/7.50  --sat_out_model                         small
% 55.16/7.50  --sat_out_clauses                       false
% 55.16/7.50  
% 55.16/7.50  ------ QBF Options
% 55.16/7.50  
% 55.16/7.50  --qbf_mode                              false
% 55.16/7.50  --qbf_elim_univ                         false
% 55.16/7.50  --qbf_dom_inst                          none
% 55.16/7.50  --qbf_dom_pre_inst                      false
% 55.16/7.50  --qbf_sk_in                             false
% 55.16/7.50  --qbf_pred_elim                         true
% 55.16/7.50  --qbf_split                             512
% 55.16/7.50  
% 55.16/7.50  ------ BMC1 Options
% 55.16/7.50  
% 55.16/7.50  --bmc1_incremental                      false
% 55.16/7.50  --bmc1_axioms                           reachable_all
% 55.16/7.50  --bmc1_min_bound                        0
% 55.16/7.50  --bmc1_max_bound                        -1
% 55.16/7.50  --bmc1_max_bound_default                -1
% 55.16/7.50  --bmc1_symbol_reachability              true
% 55.16/7.50  --bmc1_property_lemmas                  false
% 55.16/7.50  --bmc1_k_induction                      false
% 55.16/7.50  --bmc1_non_equiv_states                 false
% 55.16/7.50  --bmc1_deadlock                         false
% 55.16/7.50  --bmc1_ucm                              false
% 55.16/7.50  --bmc1_add_unsat_core                   none
% 55.16/7.50  --bmc1_unsat_core_children              false
% 55.16/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.16/7.50  --bmc1_out_stat                         full
% 55.16/7.50  --bmc1_ground_init                      false
% 55.16/7.50  --bmc1_pre_inst_next_state              false
% 55.16/7.50  --bmc1_pre_inst_state                   false
% 55.16/7.50  --bmc1_pre_inst_reach_state             false
% 55.16/7.50  --bmc1_out_unsat_core                   false
% 55.16/7.50  --bmc1_aig_witness_out                  false
% 55.16/7.50  --bmc1_verbose                          false
% 55.16/7.50  --bmc1_dump_clauses_tptp                false
% 55.16/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.16/7.50  --bmc1_dump_file                        -
% 55.16/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.16/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.16/7.50  --bmc1_ucm_extend_mode                  1
% 55.16/7.50  --bmc1_ucm_init_mode                    2
% 55.16/7.50  --bmc1_ucm_cone_mode                    none
% 55.16/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.16/7.50  --bmc1_ucm_relax_model                  4
% 55.16/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.16/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.16/7.50  --bmc1_ucm_layered_model                none
% 55.16/7.50  --bmc1_ucm_max_lemma_size               10
% 55.16/7.50  
% 55.16/7.50  ------ AIG Options
% 55.16/7.50  
% 55.16/7.50  --aig_mode                              false
% 55.16/7.50  
% 55.16/7.50  ------ Instantiation Options
% 55.16/7.50  
% 55.16/7.50  --instantiation_flag                    true
% 55.16/7.50  --inst_sos_flag                         false
% 55.16/7.50  --inst_sos_phase                        true
% 55.16/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.16/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.16/7.50  --inst_lit_sel_side                     num_symb
% 55.16/7.50  --inst_solver_per_active                1400
% 55.16/7.50  --inst_solver_calls_frac                1.
% 55.16/7.50  --inst_passive_queue_type               priority_queues
% 55.16/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.16/7.50  --inst_passive_queues_freq              [25;2]
% 55.16/7.50  --inst_dismatching                      true
% 55.16/7.50  --inst_eager_unprocessed_to_passive     true
% 55.16/7.50  --inst_prop_sim_given                   true
% 55.16/7.50  --inst_prop_sim_new                     false
% 55.16/7.50  --inst_subs_new                         false
% 55.16/7.50  --inst_eq_res_simp                      false
% 55.16/7.50  --inst_subs_given                       false
% 55.16/7.50  --inst_orphan_elimination               true
% 55.16/7.50  --inst_learning_loop_flag               true
% 55.16/7.50  --inst_learning_start                   3000
% 55.16/7.50  --inst_learning_factor                  2
% 55.16/7.50  --inst_start_prop_sim_after_learn       3
% 55.16/7.50  --inst_sel_renew                        solver
% 55.16/7.50  --inst_lit_activity_flag                true
% 55.16/7.50  --inst_restr_to_given                   false
% 55.16/7.50  --inst_activity_threshold               500
% 55.16/7.50  --inst_out_proof                        true
% 55.16/7.50  
% 55.16/7.50  ------ Resolution Options
% 55.16/7.50  
% 55.16/7.50  --resolution_flag                       true
% 55.16/7.50  --res_lit_sel                           adaptive
% 55.16/7.50  --res_lit_sel_side                      none
% 55.16/7.50  --res_ordering                          kbo
% 55.16/7.50  --res_to_prop_solver                    active
% 55.16/7.50  --res_prop_simpl_new                    false
% 55.16/7.50  --res_prop_simpl_given                  true
% 55.16/7.50  --res_passive_queue_type                priority_queues
% 55.16/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.16/7.50  --res_passive_queues_freq               [15;5]
% 55.16/7.50  --res_forward_subs                      full
% 55.16/7.50  --res_backward_subs                     full
% 55.16/7.50  --res_forward_subs_resolution           true
% 55.16/7.50  --res_backward_subs_resolution          true
% 55.16/7.50  --res_orphan_elimination                true
% 55.16/7.50  --res_time_limit                        2.
% 55.16/7.50  --res_out_proof                         true
% 55.16/7.50  
% 55.16/7.50  ------ Superposition Options
% 55.16/7.50  
% 55.16/7.50  --superposition_flag                    true
% 55.16/7.50  --sup_passive_queue_type                priority_queues
% 55.16/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.16/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.16/7.50  --demod_completeness_check              fast
% 55.16/7.50  --demod_use_ground                      true
% 55.16/7.50  --sup_to_prop_solver                    passive
% 55.16/7.50  --sup_prop_simpl_new                    true
% 55.16/7.50  --sup_prop_simpl_given                  true
% 55.16/7.50  --sup_fun_splitting                     false
% 55.16/7.50  --sup_smt_interval                      50000
% 55.16/7.50  
% 55.16/7.50  ------ Superposition Simplification Setup
% 55.16/7.50  
% 55.16/7.50  --sup_indices_passive                   []
% 55.16/7.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.16/7.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.16/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.16/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.16/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.16/7.50  --sup_full_bw                           [BwDemod]
% 55.16/7.50  --sup_immed_triv                        [TrivRules]
% 55.16/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.16/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.16/7.50  --sup_immed_bw_main                     []
% 55.16/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.16/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.16/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.16/7.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.16/7.50  
% 55.16/7.50  ------ Combination Options
% 55.16/7.50  
% 55.16/7.50  --comb_res_mult                         3
% 55.16/7.50  --comb_sup_mult                         2
% 55.16/7.50  --comb_inst_mult                        10
% 55.16/7.50  
% 55.16/7.50  ------ Debug Options
% 55.16/7.50  
% 55.16/7.50  --dbg_backtrace                         false
% 55.16/7.50  --dbg_dump_prop_clauses                 false
% 55.16/7.50  --dbg_dump_prop_clauses_file            -
% 55.16/7.50  --dbg_out_stat                          false
% 55.16/7.50  ------ Parsing...
% 55.16/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.16/7.50  
% 55.16/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.16/7.50  
% 55.16/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.16/7.50  
% 55.16/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.16/7.50  ------ Proving...
% 55.16/7.50  ------ Problem Properties 
% 55.16/7.50  
% 55.16/7.50  
% 55.16/7.50  clauses                                 27
% 55.16/7.50  conjectures                             3
% 55.16/7.50  EPR                                     2
% 55.16/7.50  Horn                                    26
% 55.16/7.50  unary                                   10
% 55.16/7.50  binary                                  11
% 55.16/7.50  lits                                    50
% 55.16/7.50  lits eq                                 19
% 55.16/7.50  fd_pure                                 0
% 55.16/7.50  fd_pseudo                               0
% 55.16/7.50  fd_cond                                 2
% 55.16/7.50  fd_pseudo_cond                          0
% 55.16/7.50  AC symbols                              0
% 55.16/7.50  
% 55.16/7.50  ------ Schedule dynamic 5 is on 
% 55.16/7.50  
% 55.16/7.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.16/7.50  
% 55.16/7.50  
% 55.16/7.50  ------ 
% 55.16/7.50  Current options:
% 55.16/7.50  ------ 
% 55.16/7.50  
% 55.16/7.50  ------ Input Options
% 55.16/7.50  
% 55.16/7.50  --out_options                           all
% 55.16/7.50  --tptp_safe_out                         true
% 55.16/7.50  --problem_path                          ""
% 55.16/7.50  --include_path                          ""
% 55.16/7.50  --clausifier                            res/vclausify_rel
% 55.16/7.50  --clausifier_options                    --mode clausify
% 55.16/7.50  --stdin                                 false
% 55.16/7.50  --stats_out                             all
% 55.16/7.50  
% 55.16/7.50  ------ General Options
% 55.16/7.50  
% 55.16/7.50  --fof                                   false
% 55.16/7.50  --time_out_real                         305.
% 55.16/7.50  --time_out_virtual                      -1.
% 55.16/7.50  --symbol_type_check                     false
% 55.16/7.50  --clausify_out                          false
% 55.16/7.50  --sig_cnt_out                           false
% 55.16/7.50  --trig_cnt_out                          false
% 55.16/7.50  --trig_cnt_out_tolerance                1.
% 55.16/7.50  --trig_cnt_out_sk_spl                   false
% 55.16/7.50  --abstr_cl_out                          false
% 55.16/7.50  
% 55.16/7.50  ------ Global Options
% 55.16/7.50  
% 55.16/7.50  --schedule                              default
% 55.16/7.50  --add_important_lit                     false
% 55.16/7.50  --prop_solver_per_cl                    1000
% 55.16/7.50  --min_unsat_core                        false
% 55.16/7.50  --soft_assumptions                      false
% 55.16/7.50  --soft_lemma_size                       3
% 55.16/7.50  --prop_impl_unit_size                   0
% 55.16/7.50  --prop_impl_unit                        []
% 55.16/7.50  --share_sel_clauses                     true
% 55.16/7.50  --reset_solvers                         false
% 55.16/7.50  --bc_imp_inh                            [conj_cone]
% 55.16/7.50  --conj_cone_tolerance                   3.
% 55.16/7.50  --extra_neg_conj                        none
% 55.16/7.50  --large_theory_mode                     true
% 55.16/7.50  --prolific_symb_bound                   200
% 55.16/7.50  --lt_threshold                          2000
% 55.16/7.50  --clause_weak_htbl                      true
% 55.16/7.50  --gc_record_bc_elim                     false
% 55.16/7.50  
% 55.16/7.50  ------ Preprocessing Options
% 55.16/7.50  
% 55.16/7.50  --preprocessing_flag                    true
% 55.16/7.50  --time_out_prep_mult                    0.1
% 55.16/7.50  --splitting_mode                        input
% 55.16/7.50  --splitting_grd                         true
% 55.16/7.50  --splitting_cvd                         false
% 55.16/7.50  --splitting_cvd_svl                     false
% 55.16/7.50  --splitting_nvd                         32
% 55.16/7.50  --sub_typing                            true
% 55.16/7.50  --prep_gs_sim                           true
% 55.16/7.50  --prep_unflatten                        true
% 55.16/7.50  --prep_res_sim                          true
% 55.16/7.50  --prep_upred                            true
% 55.16/7.50  --prep_sem_filter                       exhaustive
% 55.16/7.50  --prep_sem_filter_out                   false
% 55.16/7.50  --pred_elim                             true
% 55.16/7.50  --res_sim_input                         true
% 55.16/7.50  --eq_ax_congr_red                       true
% 55.16/7.50  --pure_diseq_elim                       true
% 55.16/7.50  --brand_transform                       false
% 55.16/7.50  --non_eq_to_eq                          false
% 55.16/7.50  --prep_def_merge                        true
% 55.16/7.50  --prep_def_merge_prop_impl              false
% 55.16/7.50  --prep_def_merge_mbd                    true
% 55.16/7.50  --prep_def_merge_tr_red                 false
% 55.16/7.50  --prep_def_merge_tr_cl                  false
% 55.16/7.50  --smt_preprocessing                     true
% 55.16/7.50  --smt_ac_axioms                         fast
% 55.16/7.50  --preprocessed_out                      false
% 55.16/7.50  --preprocessed_stats                    false
% 55.16/7.50  
% 55.16/7.50  ------ Abstraction refinement Options
% 55.16/7.50  
% 55.16/7.50  --abstr_ref                             []
% 55.16/7.50  --abstr_ref_prep                        false
% 55.16/7.50  --abstr_ref_until_sat                   false
% 55.16/7.50  --abstr_ref_sig_restrict                funpre
% 55.16/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.16/7.50  --abstr_ref_under                       []
% 55.16/7.50  
% 55.16/7.50  ------ SAT Options
% 55.16/7.50  
% 55.16/7.50  --sat_mode                              false
% 55.16/7.50  --sat_fm_restart_options                ""
% 55.16/7.50  --sat_gr_def                            false
% 55.16/7.50  --sat_epr_types                         true
% 55.16/7.50  --sat_non_cyclic_types                  false
% 55.16/7.50  --sat_finite_models                     false
% 55.16/7.50  --sat_fm_lemmas                         false
% 55.16/7.50  --sat_fm_prep                           false
% 55.16/7.50  --sat_fm_uc_incr                        true
% 55.16/7.50  --sat_out_model                         small
% 55.16/7.50  --sat_out_clauses                       false
% 55.16/7.50  
% 55.16/7.50  ------ QBF Options
% 55.16/7.50  
% 55.16/7.50  --qbf_mode                              false
% 55.16/7.50  --qbf_elim_univ                         false
% 55.16/7.50  --qbf_dom_inst                          none
% 55.16/7.50  --qbf_dom_pre_inst                      false
% 55.16/7.50  --qbf_sk_in                             false
% 55.16/7.50  --qbf_pred_elim                         true
% 55.16/7.50  --qbf_split                             512
% 55.16/7.50  
% 55.16/7.50  ------ BMC1 Options
% 55.16/7.50  
% 55.16/7.50  --bmc1_incremental                      false
% 55.16/7.50  --bmc1_axioms                           reachable_all
% 55.16/7.50  --bmc1_min_bound                        0
% 55.16/7.50  --bmc1_max_bound                        -1
% 55.16/7.50  --bmc1_max_bound_default                -1
% 55.16/7.50  --bmc1_symbol_reachability              true
% 55.16/7.50  --bmc1_property_lemmas                  false
% 55.16/7.50  --bmc1_k_induction                      false
% 55.16/7.50  --bmc1_non_equiv_states                 false
% 55.16/7.50  --bmc1_deadlock                         false
% 55.16/7.50  --bmc1_ucm                              false
% 55.16/7.50  --bmc1_add_unsat_core                   none
% 55.16/7.50  --bmc1_unsat_core_children              false
% 55.16/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.16/7.50  --bmc1_out_stat                         full
% 55.16/7.50  --bmc1_ground_init                      false
% 55.16/7.50  --bmc1_pre_inst_next_state              false
% 55.16/7.50  --bmc1_pre_inst_state                   false
% 55.16/7.50  --bmc1_pre_inst_reach_state             false
% 55.16/7.50  --bmc1_out_unsat_core                   false
% 55.16/7.50  --bmc1_aig_witness_out                  false
% 55.16/7.50  --bmc1_verbose                          false
% 55.16/7.50  --bmc1_dump_clauses_tptp                false
% 55.16/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.16/7.50  --bmc1_dump_file                        -
% 55.16/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.16/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.16/7.50  --bmc1_ucm_extend_mode                  1
% 55.16/7.50  --bmc1_ucm_init_mode                    2
% 55.16/7.50  --bmc1_ucm_cone_mode                    none
% 55.16/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.16/7.50  --bmc1_ucm_relax_model                  4
% 55.16/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.16/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.16/7.50  --bmc1_ucm_layered_model                none
% 55.16/7.50  --bmc1_ucm_max_lemma_size               10
% 55.16/7.50  
% 55.16/7.50  ------ AIG Options
% 55.16/7.50  
% 55.16/7.50  --aig_mode                              false
% 55.16/7.50  
% 55.16/7.50  ------ Instantiation Options
% 55.16/7.50  
% 55.16/7.50  --instantiation_flag                    true
% 55.16/7.50  --inst_sos_flag                         false
% 55.16/7.50  --inst_sos_phase                        true
% 55.16/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.16/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.16/7.50  --inst_lit_sel_side                     none
% 55.16/7.50  --inst_solver_per_active                1400
% 55.16/7.50  --inst_solver_calls_frac                1.
% 55.16/7.50  --inst_passive_queue_type               priority_queues
% 55.16/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.16/7.50  --inst_passive_queues_freq              [25;2]
% 55.16/7.50  --inst_dismatching                      true
% 55.16/7.50  --inst_eager_unprocessed_to_passive     true
% 55.16/7.50  --inst_prop_sim_given                   true
% 55.16/7.50  --inst_prop_sim_new                     false
% 55.16/7.50  --inst_subs_new                         false
% 55.16/7.50  --inst_eq_res_simp                      false
% 55.16/7.50  --inst_subs_given                       false
% 55.16/7.50  --inst_orphan_elimination               true
% 55.16/7.50  --inst_learning_loop_flag               true
% 55.16/7.50  --inst_learning_start                   3000
% 55.16/7.50  --inst_learning_factor                  2
% 55.16/7.50  --inst_start_prop_sim_after_learn       3
% 55.16/7.50  --inst_sel_renew                        solver
% 55.16/7.50  --inst_lit_activity_flag                true
% 55.16/7.50  --inst_restr_to_given                   false
% 55.16/7.50  --inst_activity_threshold               500
% 55.16/7.50  --inst_out_proof                        true
% 55.16/7.50  
% 55.16/7.50  ------ Resolution Options
% 55.16/7.50  
% 55.16/7.50  --resolution_flag                       false
% 55.16/7.50  --res_lit_sel                           adaptive
% 55.16/7.50  --res_lit_sel_side                      none
% 55.16/7.50  --res_ordering                          kbo
% 55.16/7.50  --res_to_prop_solver                    active
% 55.16/7.50  --res_prop_simpl_new                    false
% 55.16/7.50  --res_prop_simpl_given                  true
% 55.16/7.50  --res_passive_queue_type                priority_queues
% 55.16/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.16/7.50  --res_passive_queues_freq               [15;5]
% 55.16/7.50  --res_forward_subs                      full
% 55.16/7.50  --res_backward_subs                     full
% 55.16/7.50  --res_forward_subs_resolution           true
% 55.16/7.50  --res_backward_subs_resolution          true
% 55.16/7.50  --res_orphan_elimination                true
% 55.16/7.50  --res_time_limit                        2.
% 55.16/7.50  --res_out_proof                         true
% 55.16/7.50  
% 55.16/7.50  ------ Superposition Options
% 55.16/7.50  
% 55.16/7.50  --superposition_flag                    true
% 55.16/7.50  --sup_passive_queue_type                priority_queues
% 55.16/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.16/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.16/7.50  --demod_completeness_check              fast
% 55.16/7.50  --demod_use_ground                      true
% 55.16/7.50  --sup_to_prop_solver                    passive
% 55.16/7.50  --sup_prop_simpl_new                    true
% 55.16/7.50  --sup_prop_simpl_given                  true
% 55.16/7.50  --sup_fun_splitting                     false
% 55.16/7.50  --sup_smt_interval                      50000
% 55.16/7.50  
% 55.16/7.50  ------ Superposition Simplification Setup
% 55.16/7.50  
% 55.16/7.50  --sup_indices_passive                   []
% 55.16/7.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.16/7.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.16/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.16/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.16/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.16/7.50  --sup_full_bw                           [BwDemod]
% 55.16/7.50  --sup_immed_triv                        [TrivRules]
% 55.16/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.16/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.16/7.50  --sup_immed_bw_main                     []
% 55.16/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.16/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.16/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.16/7.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.16/7.50  
% 55.16/7.50  ------ Combination Options
% 55.16/7.50  
% 55.16/7.50  --comb_res_mult                         3
% 55.16/7.50  --comb_sup_mult                         2
% 55.16/7.50  --comb_inst_mult                        10
% 55.16/7.50  
% 55.16/7.50  ------ Debug Options
% 55.16/7.50  
% 55.16/7.50  --dbg_backtrace                         false
% 55.16/7.50  --dbg_dump_prop_clauses                 false
% 55.16/7.50  --dbg_dump_prop_clauses_file            -
% 55.16/7.50  --dbg_out_stat                          false
% 55.16/7.50  
% 55.16/7.50  
% 55.16/7.50  
% 55.16/7.50  
% 55.16/7.50  ------ Proving...
% 55.16/7.50  
% 55.16/7.50  
% 55.16/7.50  % SZS status Theorem for theBenchmark.p
% 55.16/7.50  
% 55.16/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.16/7.50  
% 55.16/7.50  fof(f23,axiom,(
% 55.16/7.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f33,plain,(
% 55.16/7.50    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 55.16/7.50    inference(ennf_transformation,[],[f23])).
% 55.16/7.50  
% 55.16/7.50  fof(f44,plain,(
% 55.16/7.50    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 55.16/7.50    inference(nnf_transformation,[],[f33])).
% 55.16/7.50  
% 55.16/7.50  fof(f76,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f44])).
% 55.16/7.50  
% 55.16/7.50  fof(f4,axiom,(
% 55.16/7.50    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f55,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 55.16/7.50    inference(cnf_transformation,[],[f4])).
% 55.16/7.50  
% 55.16/7.50  fof(f20,axiom,(
% 55.16/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f72,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.16/7.50    inference(cnf_transformation,[],[f20])).
% 55.16/7.50  
% 55.16/7.50  fof(f17,axiom,(
% 55.16/7.50    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f69,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f17])).
% 55.16/7.50  
% 55.16/7.50  fof(f14,axiom,(
% 55.16/7.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f66,plain,(
% 55.16/7.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f14])).
% 55.16/7.50  
% 55.16/7.50  fof(f15,axiom,(
% 55.16/7.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f67,plain,(
% 55.16/7.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f15])).
% 55.16/7.50  
% 55.16/7.50  fof(f16,axiom,(
% 55.16/7.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f68,plain,(
% 55.16/7.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f16])).
% 55.16/7.50  
% 55.16/7.50  fof(f82,plain,(
% 55.16/7.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 55.16/7.50    inference(definition_unfolding,[],[f67,f68])).
% 55.16/7.50  
% 55.16/7.50  fof(f83,plain,(
% 55.16/7.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 55.16/7.50    inference(definition_unfolding,[],[f66,f82])).
% 55.16/7.50  
% 55.16/7.50  fof(f84,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 55.16/7.50    inference(definition_unfolding,[],[f69,f83])).
% 55.16/7.50  
% 55.16/7.50  fof(f85,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 55.16/7.50    inference(definition_unfolding,[],[f72,f84])).
% 55.16/7.50  
% 55.16/7.50  fof(f91,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X1))) = X0) )),
% 55.16/7.50    inference(definition_unfolding,[],[f55,f85])).
% 55.16/7.50  
% 55.16/7.50  fof(f8,axiom,(
% 55.16/7.50    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f60,plain,(
% 55.16/7.50    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 55.16/7.50    inference(cnf_transformation,[],[f8])).
% 55.16/7.50  
% 55.16/7.50  fof(f5,axiom,(
% 55.16/7.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f43,plain,(
% 55.16/7.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 55.16/7.50    inference(nnf_transformation,[],[f5])).
% 55.16/7.50  
% 55.16/7.50  fof(f56,plain,(
% 55.16/7.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 55.16/7.50    inference(cnf_transformation,[],[f43])).
% 55.16/7.50  
% 55.16/7.50  fof(f7,axiom,(
% 55.16/7.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f28,plain,(
% 55.16/7.50    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 55.16/7.50    inference(ennf_transformation,[],[f7])).
% 55.16/7.50  
% 55.16/7.50  fof(f59,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f28])).
% 55.16/7.50  
% 55.16/7.50  fof(f9,axiom,(
% 55.16/7.50    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f61,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 55.16/7.50    inference(cnf_transformation,[],[f9])).
% 55.16/7.50  
% 55.16/7.50  fof(f92,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 55.16/7.50    inference(definition_unfolding,[],[f61,f85])).
% 55.16/7.50  
% 55.16/7.50  fof(f10,axiom,(
% 55.16/7.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f62,plain,(
% 55.16/7.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.16/7.50    inference(cnf_transformation,[],[f10])).
% 55.16/7.50  
% 55.16/7.50  fof(f2,axiom,(
% 55.16/7.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f51,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 55.16/7.50    inference(cnf_transformation,[],[f2])).
% 55.16/7.50  
% 55.16/7.50  fof(f86,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 55.16/7.50    inference(definition_unfolding,[],[f51,f85])).
% 55.16/7.50  
% 55.16/7.50  fof(f93,plain,(
% 55.16/7.50    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0) )),
% 55.16/7.50    inference(definition_unfolding,[],[f62,f86])).
% 55.16/7.50  
% 55.16/7.50  fof(f6,axiom,(
% 55.16/7.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f58,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f6])).
% 55.16/7.50  
% 55.16/7.50  fof(f13,axiom,(
% 55.16/7.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f30,plain,(
% 55.16/7.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 55.16/7.50    inference(ennf_transformation,[],[f13])).
% 55.16/7.50  
% 55.16/7.50  fof(f65,plain,(
% 55.16/7.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f30])).
% 55.16/7.50  
% 55.16/7.50  fof(f25,conjecture,(
% 55.16/7.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f26,negated_conjecture,(
% 55.16/7.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 55.16/7.50    inference(negated_conjecture,[],[f25])).
% 55.16/7.50  
% 55.16/7.50  fof(f36,plain,(
% 55.16/7.50    ? [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0))),
% 55.16/7.50    inference(ennf_transformation,[],[f26])).
% 55.16/7.50  
% 55.16/7.50  fof(f46,plain,(
% 55.16/7.50    ( ! [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) => (k1_xboole_0 != k7_relat_1(X0,sK2) & r1_xboole_0(sK2,k1_relat_1(X0)))) )),
% 55.16/7.50    introduced(choice_axiom,[])).
% 55.16/7.50  
% 55.16/7.50  fof(f45,plain,(
% 55.16/7.50    ? [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0)) => (? [X1] : (k1_xboole_0 != k7_relat_1(sK1,X1) & r1_xboole_0(X1,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 55.16/7.50    introduced(choice_axiom,[])).
% 55.16/7.50  
% 55.16/7.50  fof(f47,plain,(
% 55.16/7.50    (k1_xboole_0 != k7_relat_1(sK1,sK2) & r1_xboole_0(sK2,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 55.16/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f46,f45])).
% 55.16/7.50  
% 55.16/7.50  fof(f80,plain,(
% 55.16/7.50    r1_xboole_0(sK2,k1_relat_1(sK1))),
% 55.16/7.50    inference(cnf_transformation,[],[f47])).
% 55.16/7.50  
% 55.16/7.50  fof(f11,axiom,(
% 55.16/7.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f29,plain,(
% 55.16/7.50    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 55.16/7.50    inference(ennf_transformation,[],[f11])).
% 55.16/7.50  
% 55.16/7.50  fof(f63,plain,(
% 55.16/7.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f29])).
% 55.16/7.50  
% 55.16/7.50  fof(f3,axiom,(
% 55.16/7.50    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f41,plain,(
% 55.16/7.50    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 55.16/7.50    inference(nnf_transformation,[],[f3])).
% 55.16/7.50  
% 55.16/7.50  fof(f42,plain,(
% 55.16/7.50    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 55.16/7.50    inference(flattening,[],[f41])).
% 55.16/7.50  
% 55.16/7.50  fof(f53,plain,(
% 55.16/7.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 55.16/7.50    inference(cnf_transformation,[],[f42])).
% 55.16/7.50  
% 55.16/7.50  fof(f89,plain,(
% 55.16/7.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))) )),
% 55.16/7.50    inference(definition_unfolding,[],[f53,f85,f86])).
% 55.16/7.50  
% 55.16/7.50  fof(f12,axiom,(
% 55.16/7.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f64,plain,(
% 55.16/7.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 55.16/7.50    inference(cnf_transformation,[],[f12])).
% 55.16/7.50  
% 55.16/7.50  fof(f94,plain,(
% 55.16/7.50    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,X0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0) )),
% 55.16/7.50    inference(definition_unfolding,[],[f64,f86])).
% 55.16/7.50  
% 55.16/7.50  fof(f19,axiom,(
% 55.16/7.50    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f71,plain,(
% 55.16/7.50    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 55.16/7.50    inference(cnf_transformation,[],[f19])).
% 55.16/7.50  
% 55.16/7.50  fof(f18,axiom,(
% 55.16/7.50    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f70,plain,(
% 55.16/7.50    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f18])).
% 55.16/7.50  
% 55.16/7.50  fof(f87,plain,(
% 55.16/7.50    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 55.16/7.50    inference(definition_unfolding,[],[f70,f82])).
% 55.16/7.50  
% 55.16/7.50  fof(f95,plain,(
% 55.16/7.50    ( ! [X0] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 55.16/7.50    inference(definition_unfolding,[],[f71,f87])).
% 55.16/7.50  
% 55.16/7.50  fof(f22,axiom,(
% 55.16/7.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f32,plain,(
% 55.16/7.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 55.16/7.50    inference(ennf_transformation,[],[f22])).
% 55.16/7.50  
% 55.16/7.50  fof(f74,plain,(
% 55.16/7.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f32])).
% 55.16/7.50  
% 55.16/7.50  fof(f21,axiom,(
% 55.16/7.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f31,plain,(
% 55.16/7.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 55.16/7.50    inference(ennf_transformation,[],[f21])).
% 55.16/7.50  
% 55.16/7.50  fof(f73,plain,(
% 55.16/7.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f31])).
% 55.16/7.50  
% 55.16/7.50  fof(f24,axiom,(
% 55.16/7.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 55.16/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.16/7.50  
% 55.16/7.50  fof(f34,plain,(
% 55.16/7.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 55.16/7.50    inference(ennf_transformation,[],[f24])).
% 55.16/7.50  
% 55.16/7.50  fof(f35,plain,(
% 55.16/7.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 55.16/7.50    inference(flattening,[],[f34])).
% 55.16/7.50  
% 55.16/7.50  fof(f78,plain,(
% 55.16/7.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 55.16/7.50    inference(cnf_transformation,[],[f35])).
% 55.16/7.50  
% 55.16/7.50  fof(f81,plain,(
% 55.16/7.50    k1_xboole_0 != k7_relat_1(sK1,sK2)),
% 55.16/7.50    inference(cnf_transformation,[],[f47])).
% 55.16/7.50  
% 55.16/7.50  fof(f79,plain,(
% 55.16/7.50    v1_relat_1(sK1)),
% 55.16/7.50    inference(cnf_transformation,[],[f47])).
% 55.16/7.50  
% 55.16/7.50  cnf(c_20,plain,
% 55.16/7.50      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 55.16/7.50      | ~ v1_relat_1(X0)
% 55.16/7.50      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 55.16/7.50      inference(cnf_transformation,[],[f76]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1094,plain,
% 55.16/7.50      ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
% 55.16/7.50      | ~ v1_relat_1(sK1)
% 55.16/7.50      | k9_relat_1(sK1,X0) = k1_xboole_0 ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_20]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_65337,plain,
% 55.16/7.50      ( ~ r1_xboole_0(k1_relat_1(sK1),sK2)
% 55.16/7.50      | ~ v1_relat_1(sK1)
% 55.16/7.50      | k9_relat_1(sK1,sK2) = k1_xboole_0 ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_1094]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_6,plain,
% 55.16/7.50      ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X1))) = X0 ),
% 55.16/7.50      inference(cnf_transformation,[],[f91]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_11,plain,
% 55.16/7.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.16/7.50      inference(cnf_transformation,[],[f60]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_8,plain,
% 55.16/7.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 55.16/7.50      inference(cnf_transformation,[],[f56]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_909,plain,
% 55.16/7.50      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 55.16/7.50      | r1_tarski(X0,X1) = iProver_top ),
% 55.16/7.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1792,plain,
% 55.16/7.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_11,c_909]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_10,plain,
% 55.16/7.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 55.16/7.50      inference(cnf_transformation,[],[f59]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_908,plain,
% 55.16/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
% 55.16/7.50      | r1_tarski(X0,X1) != iProver_top ),
% 55.16/7.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_2420,plain,
% 55.16/7.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_1792,c_908]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_12,plain,
% 55.16/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 55.16/7.50      inference(cnf_transformation,[],[f92]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_13,plain,
% 55.16/7.50      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
% 55.16/7.50      inference(cnf_transformation,[],[f93]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1383,plain,
% 55.16/7.50      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_12,c_13]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1385,plain,
% 55.16/7.50      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 55.16/7.50      inference(light_normalisation,[status(thm)],[c_1383,c_11]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1408,plain,
% 55.16/7.50      ( k4_xboole_0(X0,k1_setfam_1(k5_enumset1(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_1385,c_12]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_9,plain,
% 55.16/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 55.16/7.50      inference(cnf_transformation,[],[f58]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1410,plain,
% 55.16/7.50      ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_1385,c_9]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1411,plain,
% 55.16/7.50      ( k4_xboole_0(X0,k1_setfam_1(k5_enumset1(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k4_xboole_0(X0,k1_xboole_0) ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_1385,c_13]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1418,plain,
% 55.16/7.50      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k1_xboole_0) ),
% 55.16/7.50      inference(light_normalisation,[status(thm)],[c_1408,c_1410,c_1411]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1420,plain,
% 55.16/7.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.16/7.50      inference(demodulation,[status(thm)],[c_1418,c_11,c_1385]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_2428,plain,
% 55.16/7.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 55.16/7.50      inference(light_normalisation,[status(thm)],[c_2420,c_1420]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_16,plain,
% 55.16/7.50      ( ~ r1_tarski(X0,X1)
% 55.16/7.50      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 55.16/7.50      inference(cnf_transformation,[],[f65]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_906,plain,
% 55.16/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.16/7.50      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
% 55.16/7.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_2734,plain,
% 55.16/7.50      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top
% 55.16/7.50      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_2428,c_906]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_3415,plain,
% 55.16/7.50      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 55.16/7.50      inference(forward_subsumption_resolution,
% 55.16/7.50                [status(thm)],
% 55.16/7.50                [c_2734,c_1792]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_25,negated_conjecture,
% 55.16/7.50      ( r1_xboole_0(sK2,k1_relat_1(sK1)) ),
% 55.16/7.50      inference(cnf_transformation,[],[f80]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_899,plain,
% 55.16/7.50      ( r1_xboole_0(sK2,k1_relat_1(sK1)) = iProver_top ),
% 55.16/7.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_14,plain,
% 55.16/7.50      ( ~ r1_xboole_0(X0,X1)
% 55.16/7.50      | k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) ),
% 55.16/7.50      inference(cnf_transformation,[],[f63]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_907,plain,
% 55.16/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),X1)
% 55.16/7.50      | r1_xboole_0(X2,X1) != iProver_top ),
% 55.16/7.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_4281,plain,
% 55.16/7.50      ( k4_xboole_0(k2_xboole_0(X0,k1_relat_1(sK1)),sK2) = k2_xboole_0(k4_xboole_0(X0,sK2),k1_relat_1(sK1)) ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_899,c_907]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_4,plain,
% 55.16/7.50      ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
% 55.16/7.50      | ~ r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) ),
% 55.16/7.50      inference(cnf_transformation,[],[f89]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_912,plain,
% 55.16/7.50      ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = iProver_top
% 55.16/7.50      | r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) != iProver_top ),
% 55.16/7.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1009,plain,
% 55.16/7.50      ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = iProver_top
% 55.16/7.50      | r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) != iProver_top ),
% 55.16/7.50      inference(demodulation,[status(thm)],[c_912,c_12]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_5317,plain,
% 55.16/7.50      ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k2_xboole_0(X1,k1_relat_1(sK1))))) = iProver_top
% 55.16/7.50      | r1_tarski(X0,k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X1,k1_relat_1(sK1))),k2_xboole_0(k4_xboole_0(X1,sK2),k1_relat_1(sK1)))) != iProver_top ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_4281,c_1009]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_5904,plain,
% 55.16/7.50      ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),k1_relat_1(sK1)),k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k2_xboole_0(X0,k1_relat_1(sK1))))) = iProver_top ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_3415,c_5317]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_7266,plain,
% 55.16/7.50      ( r1_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK2),k1_relat_1(sK1)),sK2) = iProver_top ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_6,c_5904]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_15,plain,
% 55.16/7.50      ( k4_xboole_0(k2_xboole_0(X0,X0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
% 55.16/7.50      inference(cnf_transformation,[],[f94]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_17,plain,
% 55.16/7.50      ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 55.16/7.50      inference(cnf_transformation,[],[f95]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_971,plain,
% 55.16/7.50      ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k1_xboole_0 ),
% 55.16/7.50      inference(light_normalisation,[status(thm)],[c_15,c_17]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1119,plain,
% 55.16/7.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.16/7.50      inference(superposition,[status(thm)],[c_971,c_9]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_7287,plain,
% 55.16/7.50      ( r1_xboole_0(k1_relat_1(sK1),sK2) = iProver_top ),
% 55.16/7.50      inference(demodulation,[status(thm)],[c_7266,c_1119,c_2428]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_7304,plain,
% 55.16/7.50      ( r1_xboole_0(k1_relat_1(sK1),sK2) ),
% 55.16/7.50      inference(predicate_to_equality_rev,[status(thm)],[c_7287]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_404,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1999,plain,
% 55.16/7.50      ( k9_relat_1(sK1,sK2) != X0
% 55.16/7.50      | k1_xboole_0 != X0
% 55.16/7.50      | k1_xboole_0 = k9_relat_1(sK1,sK2) ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_404]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_2000,plain,
% 55.16/7.50      ( k9_relat_1(sK1,sK2) != k1_xboole_0
% 55.16/7.50      | k1_xboole_0 = k9_relat_1(sK1,sK2)
% 55.16/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_1999]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_19,plain,
% 55.16/7.50      ( ~ v1_relat_1(X0)
% 55.16/7.50      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 55.16/7.50      inference(cnf_transformation,[],[f74]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1089,plain,
% 55.16/7.50      ( ~ v1_relat_1(sK1)
% 55.16/7.50      | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_19]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1874,plain,
% 55.16/7.50      ( ~ v1_relat_1(sK1)
% 55.16/7.50      | k2_relat_1(k7_relat_1(sK1,sK2)) = k9_relat_1(sK1,sK2) ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_1089]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1323,plain,
% 55.16/7.50      ( k2_relat_1(k7_relat_1(sK1,sK2)) != X0
% 55.16/7.50      | k2_relat_1(k7_relat_1(sK1,sK2)) = k1_xboole_0
% 55.16/7.50      | k1_xboole_0 != X0 ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_404]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1873,plain,
% 55.16/7.50      ( k2_relat_1(k7_relat_1(sK1,sK2)) != k9_relat_1(sK1,sK2)
% 55.16/7.50      | k2_relat_1(k7_relat_1(sK1,sK2)) = k1_xboole_0
% 55.16/7.50      | k1_xboole_0 != k9_relat_1(sK1,sK2) ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_1323]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_18,plain,
% 55.16/7.50      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 55.16/7.50      inference(cnf_transformation,[],[f73]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1070,plain,
% 55.16/7.50      ( v1_relat_1(k7_relat_1(sK1,X0)) | ~ v1_relat_1(sK1) ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_18]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1197,plain,
% 55.16/7.50      ( v1_relat_1(k7_relat_1(sK1,sK2)) | ~ v1_relat_1(sK1) ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_1070]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_22,plain,
% 55.16/7.50      ( ~ v1_relat_1(X0)
% 55.16/7.50      | k2_relat_1(X0) != k1_xboole_0
% 55.16/7.50      | k1_xboole_0 = X0 ),
% 55.16/7.50      inference(cnf_transformation,[],[f78]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_1075,plain,
% 55.16/7.50      ( ~ v1_relat_1(k7_relat_1(sK1,sK2))
% 55.16/7.50      | k2_relat_1(k7_relat_1(sK1,sK2)) != k1_xboole_0
% 55.16/7.50      | k1_xboole_0 = k7_relat_1(sK1,sK2) ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_22]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_403,plain,( X0 = X0 ),theory(equality) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_428,plain,
% 55.16/7.50      ( k1_xboole_0 = k1_xboole_0 ),
% 55.16/7.50      inference(instantiation,[status(thm)],[c_403]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_24,negated_conjecture,
% 55.16/7.50      ( k1_xboole_0 != k7_relat_1(sK1,sK2) ),
% 55.16/7.50      inference(cnf_transformation,[],[f81]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(c_26,negated_conjecture,
% 55.16/7.50      ( v1_relat_1(sK1) ),
% 55.16/7.50      inference(cnf_transformation,[],[f79]) ).
% 55.16/7.50  
% 55.16/7.50  cnf(contradiction,plain,
% 55.16/7.50      ( $false ),
% 55.16/7.50      inference(minisat,
% 55.16/7.50                [status(thm)],
% 55.16/7.50                [c_65337,c_7304,c_2000,c_1874,c_1873,c_1197,c_1075,c_428,
% 55.16/7.50                 c_24,c_26]) ).
% 55.16/7.50  
% 55.16/7.50  
% 55.16/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.16/7.50  
% 55.16/7.50  ------                               Statistics
% 55.16/7.50  
% 55.16/7.50  ------ General
% 55.16/7.50  
% 55.16/7.50  abstr_ref_over_cycles:                  0
% 55.16/7.50  abstr_ref_under_cycles:                 0
% 55.16/7.50  gc_basic_clause_elim:                   0
% 55.16/7.50  forced_gc_time:                         0
% 55.16/7.50  parsing_time:                           0.01
% 55.16/7.50  unif_index_cands_time:                  0.
% 55.16/7.50  unif_index_add_time:                    0.
% 55.16/7.50  orderings_time:                         0.
% 55.16/7.50  out_proof_time:                         0.012
% 55.16/7.50  total_time:                             6.605
% 55.16/7.50  num_of_symbols:                         47
% 55.16/7.50  num_of_terms:                           76354
% 55.16/7.50  
% 55.16/7.50  ------ Preprocessing
% 55.16/7.50  
% 55.16/7.50  num_of_splits:                          0
% 55.16/7.50  num_of_split_atoms:                     0
% 55.16/7.50  num_of_reused_defs:                     0
% 55.16/7.50  num_eq_ax_congr_red:                    22
% 55.16/7.50  num_of_sem_filtered_clauses:            1
% 55.16/7.50  num_of_subtypes:                        0
% 55.16/7.50  monotx_restored_types:                  0
% 55.16/7.50  sat_num_of_epr_types:                   0
% 55.16/7.50  sat_num_of_non_cyclic_types:            0
% 55.16/7.50  sat_guarded_non_collapsed_types:        0
% 55.16/7.50  num_pure_diseq_elim:                    0
% 55.16/7.50  simp_replaced_by:                       0
% 55.16/7.50  res_preprocessed:                       108
% 55.16/7.50  prep_upred:                             0
% 55.16/7.50  prep_unflattend:                        12
% 55.16/7.50  smt_new_axioms:                         0
% 55.16/7.50  pred_elim_cands:                        4
% 55.16/7.50  pred_elim:                              0
% 55.16/7.50  pred_elim_cl:                           0
% 55.16/7.50  pred_elim_cycles:                       1
% 55.16/7.50  merged_defs:                            6
% 55.16/7.50  merged_defs_ncl:                        0
% 55.16/7.50  bin_hyper_res:                          6
% 55.16/7.50  prep_cycles:                            3
% 55.16/7.50  pred_elim_time:                         0.003
% 55.16/7.50  splitting_time:                         0.
% 55.16/7.50  sem_filter_time:                        0.
% 55.16/7.50  monotx_time:                            0.
% 55.16/7.50  subtype_inf_time:                       0.
% 55.16/7.50  
% 55.16/7.50  ------ Problem properties
% 55.16/7.50  
% 55.16/7.50  clauses:                                27
% 55.16/7.50  conjectures:                            3
% 55.16/7.50  epr:                                    2
% 55.16/7.50  horn:                                   26
% 55.16/7.50  ground:                                 3
% 55.16/7.50  unary:                                  10
% 55.16/7.50  binary:                                 11
% 55.16/7.50  lits:                                   50
% 55.16/7.50  lits_eq:                                19
% 55.16/7.50  fd_pure:                                0
% 55.16/7.50  fd_pseudo:                              0
% 55.16/7.50  fd_cond:                                2
% 55.16/7.50  fd_pseudo_cond:                         0
% 55.16/7.50  ac_symbols:                             0
% 55.16/7.50  
% 55.16/7.50  ------ Propositional Solver
% 55.16/7.50  
% 55.16/7.50  prop_solver_calls:                      25
% 55.16/7.50  prop_fast_solver_calls:                 819
% 55.16/7.50  smt_solver_calls:                       0
% 55.16/7.50  smt_fast_solver_calls:                  0
% 55.16/7.50  prop_num_of_clauses:                    19857
% 55.16/7.50  prop_preprocess_simplified:             21078
% 55.16/7.50  prop_fo_subsumed:                       2
% 55.16/7.50  prop_solver_time:                       0.
% 55.16/7.50  smt_solver_time:                        0.
% 55.16/7.50  smt_fast_solver_time:                   0.
% 55.16/7.50  prop_fast_solver_time:                  0.
% 55.16/7.50  prop_unsat_core_time:                   0.002
% 55.16/7.50  
% 55.16/7.50  ------ QBF
% 55.16/7.50  
% 55.16/7.50  qbf_q_res:                              0
% 55.16/7.50  qbf_num_tautologies:                    0
% 55.16/7.50  qbf_prep_cycles:                        0
% 55.16/7.50  
% 55.16/7.50  ------ BMC1
% 55.16/7.50  
% 55.16/7.50  bmc1_current_bound:                     -1
% 55.16/7.50  bmc1_last_solved_bound:                 -1
% 55.16/7.50  bmc1_unsat_core_size:                   -1
% 55.16/7.50  bmc1_unsat_core_parents_size:           -1
% 55.16/7.50  bmc1_merge_next_fun:                    0
% 55.16/7.50  bmc1_unsat_core_clauses_time:           0.
% 55.16/7.50  
% 55.16/7.50  ------ Instantiation
% 55.16/7.50  
% 55.16/7.50  inst_num_of_clauses:                    3238
% 55.16/7.50  inst_num_in_passive:                    2183
% 55.16/7.50  inst_num_in_active:                     983
% 55.16/7.50  inst_num_in_unprocessed:                71
% 55.16/7.50  inst_num_of_loops:                      1163
% 55.16/7.50  inst_num_of_learning_restarts:          0
% 55.16/7.50  inst_num_moves_active_passive:          177
% 55.16/7.50  inst_lit_activity:                      0
% 55.16/7.50  inst_lit_activity_moves:                0
% 55.16/7.50  inst_num_tautologies:                   0
% 55.16/7.50  inst_num_prop_implied:                  0
% 55.16/7.50  inst_num_existing_simplified:           0
% 55.16/7.50  inst_num_eq_res_simplified:             0
% 55.16/7.50  inst_num_child_elim:                    0
% 55.16/7.50  inst_num_of_dismatching_blockings:      1636
% 55.16/7.50  inst_num_of_non_proper_insts:           2254
% 55.16/7.50  inst_num_of_duplicates:                 0
% 55.16/7.50  inst_inst_num_from_inst_to_res:         0
% 55.16/7.50  inst_dismatching_checking_time:         0.
% 55.16/7.50  
% 55.16/7.50  ------ Resolution
% 55.16/7.50  
% 55.16/7.50  res_num_of_clauses:                     0
% 55.16/7.50  res_num_in_passive:                     0
% 55.16/7.50  res_num_in_active:                      0
% 55.16/7.50  res_num_of_loops:                       111
% 55.16/7.50  res_forward_subset_subsumed:            195
% 55.16/7.50  res_backward_subset_subsumed:           0
% 55.16/7.50  res_forward_subsumed:                   0
% 55.16/7.50  res_backward_subsumed:                  0
% 55.16/7.50  res_forward_subsumption_resolution:     0
% 55.16/7.50  res_backward_subsumption_resolution:    0
% 55.16/7.50  res_clause_to_clause_subsumption:       21103
% 55.16/7.50  res_orphan_elimination:                 0
% 55.16/7.50  res_tautology_del:                      167
% 55.16/7.50  res_num_eq_res_simplified:              0
% 55.16/7.50  res_num_sel_changes:                    0
% 55.16/7.50  res_moves_from_active_to_pass:          0
% 55.16/7.50  
% 55.16/7.50  ------ Superposition
% 55.16/7.50  
% 55.16/7.50  sup_time_total:                         0.
% 55.16/7.50  sup_time_generating:                    0.
% 55.16/7.50  sup_time_sim_full:                      0.
% 55.16/7.50  sup_time_sim_immed:                     0.
% 55.16/7.50  
% 55.16/7.50  sup_num_of_clauses:                     4807
% 55.16/7.50  sup_num_in_active:                      216
% 55.16/7.50  sup_num_in_passive:                     4591
% 55.16/7.50  sup_num_of_loops:                       232
% 55.16/7.50  sup_fw_superposition:                   4506
% 55.16/7.50  sup_bw_superposition:                   7723
% 55.16/7.50  sup_immediate_simplified:               7259
% 55.16/7.50  sup_given_eliminated:                   1
% 55.16/7.50  comparisons_done:                       0
% 55.16/7.50  comparisons_avoided:                    0
% 55.16/7.50  
% 55.16/7.50  ------ Simplifications
% 55.16/7.50  
% 55.16/7.50  
% 55.16/7.50  sim_fw_subset_subsumed:                 15
% 55.16/7.50  sim_bw_subset_subsumed:                 4
% 55.16/7.50  sim_fw_subsumed:                        1254
% 55.16/7.50  sim_bw_subsumed:                        13
% 55.16/7.50  sim_fw_subsumption_res:                 1
% 55.16/7.50  sim_bw_subsumption_res:                 0
% 55.16/7.50  sim_tautology_del:                      25
% 55.16/7.50  sim_eq_tautology_del:                   192
% 55.16/7.50  sim_eq_res_simp:                        7
% 55.16/7.50  sim_fw_demodulated:                     1451
% 55.16/7.50  sim_bw_demodulated:                     413
% 55.16/7.50  sim_light_normalised:                   5214
% 55.16/7.50  sim_joinable_taut:                      0
% 55.16/7.50  sim_joinable_simp:                      0
% 55.16/7.50  sim_ac_normalised:                      0
% 55.16/7.50  sim_smt_subsumption:                    0
% 55.16/7.50  
%------------------------------------------------------------------------------
