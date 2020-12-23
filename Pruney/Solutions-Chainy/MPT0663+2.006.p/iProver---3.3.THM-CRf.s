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
% DateTime   : Thu Dec  3 11:51:00 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 726 expanded)
%              Number of clauses        :   45 ( 115 expanded)
%              Number of leaves         :   16 ( 216 expanded)
%              Depth                    :   21
%              Number of atoms          :  220 ( 996 expanded)
%              Number of equality atoms :  101 ( 741 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f53])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f54])).

fof(f57,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f55,f55])).

fof(f12,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f55])).

fof(f58,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f27])).

fof(f50,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    r2_hidden(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_0,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_690,plain,
    ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_1583,plain,
    ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_0,c_690])).

cnf(c_1589,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_1583,c_690])).

cnf(c_692,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_690,c_11])).

cnf(c_2,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1021,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_692,c_2])).

cnf(c_689,plain,
    ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_11,c_2])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_345,plain,
    ( r2_hidden(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_783,plain,
    ( r2_hidden(sK0,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_345])).

cnf(c_787,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_689,c_783])).

cnf(c_1315,plain,
    ( r2_hidden(sK0,k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1021,c_787])).

cnf(c_1801,plain,
    ( r2_hidden(sK0,k2_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(k1_relat_1(sK2))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1589,c_1315])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_347,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1466,plain,
    ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) = iProver_top
    | r2_hidden(X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) != iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_347])).

cnf(c_1480,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) != iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1466,c_2])).

cnf(c_7,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_350,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_351,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2799,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1480,c_350,c_351])).

cnf(c_2803,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_2799])).

cnf(c_2804,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_2799])).

cnf(c_8710,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_2804])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_354,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k7_relat_1(X1,X2),X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_346,plain,
    ( k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
    | r2_hidden(X2,k1_relat_1(k7_relat_1(X0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2645,plain,
    ( k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_354,c_346])).

cnf(c_11959,plain,
    ( k1_funct_1(k7_relat_1(sK2,X0),sK0) = k1_funct_1(sK2,sK0)
    | r2_hidden(sK0,X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8710,c_2645])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12104,plain,
    ( k1_funct_1(k7_relat_1(sK2,X0),sK0) = k1_funct_1(sK2,sK0)
    | r2_hidden(sK0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11959,c_17,c_18])).

cnf(c_12116,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_2803,c_12104])).

cnf(c_13,negated_conjecture,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12322,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_12116,c_13])).

cnf(c_126,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1918,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12322,c_1918])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:42:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 4.11/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.01  
% 4.11/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.11/1.01  
% 4.11/1.01  ------  iProver source info
% 4.11/1.01  
% 4.11/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.11/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.11/1.01  git: non_committed_changes: false
% 4.11/1.01  git: last_make_outside_of_git: false
% 4.11/1.01  
% 4.11/1.01  ------ 
% 4.11/1.01  ------ Parsing...
% 4.11/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.11/1.01  
% 4.11/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.11/1.01  
% 4.11/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.11/1.01  
% 4.11/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.11/1.01  ------ Proving...
% 4.11/1.01  ------ Problem Properties 
% 4.11/1.01  
% 4.11/1.01  
% 4.11/1.01  clauses                                 17
% 4.11/1.01  conjectures                             4
% 4.11/1.01  EPR                                     2
% 4.11/1.01  Horn                                    17
% 4.11/1.01  unary                                   10
% 4.11/1.01  binary                                  0
% 4.11/1.01  lits                                    37
% 4.11/1.01  lits eq                                 6
% 4.11/1.01  fd_pure                                 0
% 4.11/1.01  fd_pseudo                               0
% 4.11/1.01  fd_cond                                 0
% 4.11/1.01  fd_pseudo_cond                          0
% 4.11/1.01  AC symbols                              0
% 4.11/1.01  
% 4.11/1.01  ------ Input Options Time Limit: Unbounded
% 4.11/1.01  
% 4.11/1.01  
% 4.11/1.01  ------ 
% 4.11/1.01  Current options:
% 4.11/1.01  ------ 
% 4.11/1.01  
% 4.11/1.01  
% 4.11/1.01  
% 4.11/1.01  
% 4.11/1.01  ------ Proving...
% 4.11/1.01  
% 4.11/1.01  
% 4.11/1.01  % SZS status Theorem for theBenchmark.p
% 4.11/1.01  
% 4.11/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.11/1.01  
% 4.11/1.01  fof(f1,axiom,(
% 4.11/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f29,plain,(
% 4.11/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f1])).
% 4.11/1.01  
% 4.11/1.01  fof(f2,axiom,(
% 4.11/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f30,plain,(
% 4.11/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f2])).
% 4.11/1.01  
% 4.11/1.01  fof(f3,axiom,(
% 4.11/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f31,plain,(
% 4.11/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f3])).
% 4.11/1.01  
% 4.11/1.01  fof(f4,axiom,(
% 4.11/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f32,plain,(
% 4.11/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f4])).
% 4.11/1.01  
% 4.11/1.01  fof(f5,axiom,(
% 4.11/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f33,plain,(
% 4.11/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f5])).
% 4.11/1.01  
% 4.11/1.01  fof(f6,axiom,(
% 4.11/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f34,plain,(
% 4.11/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f6])).
% 4.11/1.01  
% 4.11/1.01  fof(f52,plain,(
% 4.11/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 4.11/1.01    inference(definition_unfolding,[],[f33,f34])).
% 4.11/1.01  
% 4.11/1.01  fof(f53,plain,(
% 4.11/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 4.11/1.01    inference(definition_unfolding,[],[f32,f52])).
% 4.11/1.01  
% 4.11/1.01  fof(f54,plain,(
% 4.11/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 4.11/1.01    inference(definition_unfolding,[],[f31,f53])).
% 4.11/1.01  
% 4.11/1.01  fof(f55,plain,(
% 4.11/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 4.11/1.01    inference(definition_unfolding,[],[f30,f54])).
% 4.11/1.01  
% 4.11/1.01  fof(f57,plain,(
% 4.11/1.01    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) )),
% 4.11/1.01    inference(definition_unfolding,[],[f29,f55,f55])).
% 4.11/1.01  
% 4.11/1.01  fof(f12,axiom,(
% 4.11/1.01    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f46,plain,(
% 4.11/1.01    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 4.11/1.01    inference(cnf_transformation,[],[f12])).
% 4.11/1.01  
% 4.11/1.01  fof(f7,axiom,(
% 4.11/1.01    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f35,plain,(
% 4.11/1.01    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f7])).
% 4.11/1.01  
% 4.11/1.01  fof(f56,plain,(
% 4.11/1.01    ( ! [X0,X1] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 4.11/1.01    inference(definition_unfolding,[],[f35,f55])).
% 4.11/1.01  
% 4.11/1.01  fof(f58,plain,(
% 4.11/1.01    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 4.11/1.01    inference(definition_unfolding,[],[f46,f56])).
% 4.11/1.01  
% 4.11/1.01  fof(f8,axiom,(
% 4.11/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f37,plain,(
% 4.11/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.11/1.01    inference(cnf_transformation,[],[f8])).
% 4.11/1.01  
% 4.11/1.01  fof(f36,plain,(
% 4.11/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.11/1.01    inference(cnf_transformation,[],[f8])).
% 4.11/1.01  
% 4.11/1.01  fof(f14,conjecture,(
% 4.11/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f15,negated_conjecture,(
% 4.11/1.01    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 4.11/1.01    inference(negated_conjecture,[],[f14])).
% 4.11/1.01  
% 4.11/1.01  fof(f21,plain,(
% 4.11/1.01    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.11/1.01    inference(ennf_transformation,[],[f15])).
% 4.11/1.01  
% 4.11/1.01  fof(f22,plain,(
% 4.11/1.01    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.11/1.01    inference(flattening,[],[f21])).
% 4.11/1.01  
% 4.11/1.01  fof(f27,plain,(
% 4.11/1.01    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 4.11/1.01    introduced(choice_axiom,[])).
% 4.11/1.01  
% 4.11/1.01  fof(f28,plain,(
% 4.11/1.01    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 4.11/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f27])).
% 4.11/1.01  
% 4.11/1.01  fof(f50,plain,(
% 4.11/1.01    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 4.11/1.01    inference(cnf_transformation,[],[f28])).
% 4.11/1.01  
% 4.11/1.01  fof(f59,plain,(
% 4.11/1.01    r2_hidden(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 4.11/1.01    inference(definition_unfolding,[],[f50,f56])).
% 4.11/1.01  
% 4.11/1.01  fof(f11,axiom,(
% 4.11/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f17,plain,(
% 4.11/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.11/1.01    inference(ennf_transformation,[],[f11])).
% 4.11/1.01  
% 4.11/1.01  fof(f18,plain,(
% 4.11/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.11/1.01    inference(flattening,[],[f17])).
% 4.11/1.01  
% 4.11/1.01  fof(f25,plain,(
% 4.11/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.11/1.01    inference(nnf_transformation,[],[f18])).
% 4.11/1.01  
% 4.11/1.01  fof(f26,plain,(
% 4.11/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.11/1.01    inference(flattening,[],[f25])).
% 4.11/1.01  
% 4.11/1.01  fof(f43,plain,(
% 4.11/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f26])).
% 4.11/1.01  
% 4.11/1.01  fof(f10,axiom,(
% 4.11/1.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f41,plain,(
% 4.11/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.11/1.01    inference(cnf_transformation,[],[f10])).
% 4.11/1.01  
% 4.11/1.01  fof(f42,plain,(
% 4.11/1.01    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 4.11/1.01    inference(cnf_transformation,[],[f10])).
% 4.11/1.01  
% 4.11/1.01  fof(f9,axiom,(
% 4.11/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f16,plain,(
% 4.11/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 4.11/1.01    inference(ennf_transformation,[],[f9])).
% 4.11/1.01  
% 4.11/1.01  fof(f23,plain,(
% 4.11/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 4.11/1.01    inference(nnf_transformation,[],[f16])).
% 4.11/1.01  
% 4.11/1.01  fof(f24,plain,(
% 4.11/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 4.11/1.01    inference(flattening,[],[f23])).
% 4.11/1.01  
% 4.11/1.01  fof(f40,plain,(
% 4.11/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f24])).
% 4.11/1.01  
% 4.11/1.01  fof(f13,axiom,(
% 4.11/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 4.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.01  
% 4.11/1.01  fof(f19,plain,(
% 4.11/1.01    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.11/1.01    inference(ennf_transformation,[],[f13])).
% 4.11/1.01  
% 4.11/1.01  fof(f20,plain,(
% 4.11/1.01    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.11/1.01    inference(flattening,[],[f19])).
% 4.11/1.01  
% 4.11/1.01  fof(f47,plain,(
% 4.11/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.11/1.01    inference(cnf_transformation,[],[f20])).
% 4.11/1.01  
% 4.11/1.01  fof(f48,plain,(
% 4.11/1.01    v1_relat_1(sK2)),
% 4.11/1.01    inference(cnf_transformation,[],[f28])).
% 4.11/1.01  
% 4.11/1.01  fof(f49,plain,(
% 4.11/1.01    v1_funct_1(sK2)),
% 4.11/1.01    inference(cnf_transformation,[],[f28])).
% 4.11/1.01  
% 4.11/1.01  fof(f51,plain,(
% 4.11/1.01    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 4.11/1.01    inference(cnf_transformation,[],[f28])).
% 4.11/1.01  
% 4.11/1.01  cnf(c_0,plain,
% 4.11/1.01      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
% 4.11/1.01      inference(cnf_transformation,[],[f57]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_11,plain,
% 4.11/1.01      ( k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 4.11/1.01      inference(cnf_transformation,[],[f58]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1,plain,
% 4.11/1.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 4.11/1.01      inference(cnf_transformation,[],[f37]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_690,plain,
% 4.11/1.01      ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1583,plain,
% 4.11/1.01      ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_0,c_690]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1589,plain,
% 4.11/1.01      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_1583,c_690]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_692,plain,
% 4.11/1.01      ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 4.11/1.01      inference(demodulation,[status(thm)],[c_690,c_11]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_2,plain,
% 4.11/1.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 4.11/1.01      inference(cnf_transformation,[],[f36]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1021,plain,
% 4.11/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_692,c_2]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_689,plain,
% 4.11/1.01      ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_11,c_2]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_14,negated_conjecture,
% 4.11/1.01      ( r2_hidden(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
% 4.11/1.01      inference(cnf_transformation,[],[f59]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_345,plain,
% 4.11/1.01      ( r2_hidden(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) = iProver_top ),
% 4.11/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_783,plain,
% 4.11/1.01      ( r2_hidden(sK0,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k1_relat_1(sK2)))) = iProver_top ),
% 4.11/1.01      inference(demodulation,[status(thm)],[c_0,c_345]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_787,plain,
% 4.11/1.01      ( r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)))) = iProver_top ),
% 4.11/1.01      inference(demodulation,[status(thm)],[c_689,c_783]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1315,plain,
% 4.11/1.01      ( r2_hidden(sK0,k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)))) = iProver_top ),
% 4.11/1.01      inference(demodulation,[status(thm)],[c_1021,c_787]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1801,plain,
% 4.11/1.01      ( r2_hidden(sK0,k2_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(k1_relat_1(sK2))))) = iProver_top ),
% 4.11/1.01      inference(demodulation,[status(thm)],[c_1589,c_1315]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_10,plain,
% 4.11/1.01      ( r2_hidden(X0,k1_relat_1(X1))
% 4.11/1.01      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 4.11/1.01      | ~ v1_funct_1(X1)
% 4.11/1.01      | ~ v1_relat_1(X1) ),
% 4.11/1.01      inference(cnf_transformation,[],[f43]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_347,plain,
% 4.11/1.01      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 4.11/1.01      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) != iProver_top
% 4.11/1.01      | v1_funct_1(X1) != iProver_top
% 4.11/1.01      | v1_relat_1(X1) != iProver_top ),
% 4.11/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1466,plain,
% 4.11/1.01      ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) = iProver_top
% 4.11/1.01      | r2_hidden(X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) != iProver_top
% 4.11/1.01      | v1_funct_1(k6_relat_1(X1)) != iProver_top
% 4.11/1.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_1021,c_347]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1480,plain,
% 4.11/1.01      ( r2_hidden(X0,X1) = iProver_top
% 4.11/1.01      | r2_hidden(X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) != iProver_top
% 4.11/1.01      | v1_funct_1(k6_relat_1(X1)) != iProver_top
% 4.11/1.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.11/1.01      inference(demodulation,[status(thm)],[c_1466,c_2]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_7,plain,
% 4.11/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 4.11/1.01      inference(cnf_transformation,[],[f41]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_350,plain,
% 4.11/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 4.11/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_6,plain,
% 4.11/1.01      ( v1_funct_1(k6_relat_1(X0)) ),
% 4.11/1.01      inference(cnf_transformation,[],[f42]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_351,plain,
% 4.11/1.01      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 4.11/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_2799,plain,
% 4.11/1.01      ( r2_hidden(X0,X1) = iProver_top
% 4.11/1.01      | r2_hidden(X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) != iProver_top ),
% 4.11/1.01      inference(forward_subsumption_resolution,
% 4.11/1.01                [status(thm)],
% 4.11/1.01                [c_1480,c_350,c_351]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_2803,plain,
% 4.11/1.01      ( r2_hidden(sK0,sK1) = iProver_top ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_1801,c_2799]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_2804,plain,
% 4.11/1.01      ( r2_hidden(X0,X1) = iProver_top
% 4.11/1.01      | r2_hidden(X0,k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) != iProver_top ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_1589,c_2799]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_8710,plain,
% 4.11/1.01      ( r2_hidden(sK0,k1_relat_1(sK2)) = iProver_top ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_1801,c_2804]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_3,plain,
% 4.11/1.01      ( ~ r2_hidden(X0,X1)
% 4.11/1.01      | ~ r2_hidden(X0,k1_relat_1(X2))
% 4.11/1.01      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 4.11/1.01      | ~ v1_relat_1(X2) ),
% 4.11/1.01      inference(cnf_transformation,[],[f40]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_354,plain,
% 4.11/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.11/1.01      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 4.11/1.01      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
% 4.11/1.01      | v1_relat_1(X2) != iProver_top ),
% 4.11/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_12,plain,
% 4.11/1.01      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 4.11/1.01      | ~ v1_funct_1(X1)
% 4.11/1.01      | ~ v1_relat_1(X1)
% 4.11/1.01      | k1_funct_1(k7_relat_1(X1,X2),X0) = k1_funct_1(X1,X0) ),
% 4.11/1.01      inference(cnf_transformation,[],[f47]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_346,plain,
% 4.11/1.01      ( k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
% 4.11/1.01      | r2_hidden(X2,k1_relat_1(k7_relat_1(X0,X1))) != iProver_top
% 4.11/1.01      | v1_funct_1(X0) != iProver_top
% 4.11/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.11/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_2645,plain,
% 4.11/1.01      ( k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
% 4.11/1.01      | r2_hidden(X2,X1) != iProver_top
% 4.11/1.01      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 4.11/1.01      | v1_funct_1(X0) != iProver_top
% 4.11/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_354,c_346]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_11959,plain,
% 4.11/1.01      ( k1_funct_1(k7_relat_1(sK2,X0),sK0) = k1_funct_1(sK2,sK0)
% 4.11/1.01      | r2_hidden(sK0,X0) != iProver_top
% 4.11/1.01      | v1_funct_1(sK2) != iProver_top
% 4.11/1.01      | v1_relat_1(sK2) != iProver_top ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_8710,c_2645]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_16,negated_conjecture,
% 4.11/1.01      ( v1_relat_1(sK2) ),
% 4.11/1.01      inference(cnf_transformation,[],[f48]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_17,plain,
% 4.11/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 4.11/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_15,negated_conjecture,
% 4.11/1.01      ( v1_funct_1(sK2) ),
% 4.11/1.01      inference(cnf_transformation,[],[f49]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_18,plain,
% 4.11/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 4.11/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_12104,plain,
% 4.11/1.01      ( k1_funct_1(k7_relat_1(sK2,X0),sK0) = k1_funct_1(sK2,sK0)
% 4.11/1.01      | r2_hidden(sK0,X0) != iProver_top ),
% 4.11/1.01      inference(global_propositional_subsumption,
% 4.11/1.01                [status(thm)],
% 4.11/1.01                [c_11959,c_17,c_18]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_12116,plain,
% 4.11/1.01      ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
% 4.11/1.01      inference(superposition,[status(thm)],[c_2803,c_12104]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_13,negated_conjecture,
% 4.11/1.01      ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
% 4.11/1.01      inference(cnf_transformation,[],[f51]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_12322,plain,
% 4.11/1.01      ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) ),
% 4.11/1.01      inference(demodulation,[status(thm)],[c_12116,c_13]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_126,plain,( X0 = X0 ),theory(equality) ).
% 4.11/1.01  
% 4.11/1.01  cnf(c_1918,plain,
% 4.11/1.01      ( k1_funct_1(sK2,sK0) = k1_funct_1(sK2,sK0) ),
% 4.11/1.01      inference(instantiation,[status(thm)],[c_126]) ).
% 4.11/1.01  
% 4.11/1.01  cnf(contradiction,plain,
% 4.11/1.01      ( $false ),
% 4.11/1.01      inference(minisat,[status(thm)],[c_12322,c_1918]) ).
% 4.11/1.01  
% 4.11/1.01  
% 4.11/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.11/1.01  
% 4.11/1.01  ------                               Statistics
% 4.11/1.01  
% 4.11/1.01  ------ Selected
% 4.11/1.01  
% 4.11/1.01  total_time:                             0.374
% 4.11/1.01  
%------------------------------------------------------------------------------
