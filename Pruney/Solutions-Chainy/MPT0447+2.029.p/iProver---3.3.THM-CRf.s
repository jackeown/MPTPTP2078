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
% DateTime   : Thu Dec  3 11:43:14 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 880 expanded)
%              Number of clauses        :  103 ( 270 expanded)
%              Number of leaves         :   26 ( 233 expanded)
%              Depth                    :   21
%              Number of atoms          :  354 (1684 expanded)
%              Number of equality atoms :  162 ( 673 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK1))
        & r1_tarski(X0,sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f39,f38])).

fof(f63,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f54])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f71,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f55,f66,f66])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f54,f66])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X0))) = k1_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f54,f54])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ) ),
    inference(definition_unfolding,[],[f46,f54])).

fof(f64,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X0))) = k2_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f54,f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f65,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_621,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_626,plain,
    ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1978,plain,
    ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k1_relat_1(sK1))) = k3_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_621,c_626])).

cnf(c_13,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1238,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13,c_14])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_629,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_632,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X2 != X1
    | k4_xboole_0(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_214,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
    | v1_xboole_0(k4_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_228,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
    | k4_xboole_0(X0,X1) != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_214])).

cnf(c_229,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_619,plain,
    ( k1_xboole_0 = k4_xboole_0(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_1739,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_619])).

cnf(c_10147,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_629,c_1739])).

cnf(c_10854,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1238,c_10147])).

cnf(c_10953,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10854,c_14])).

cnf(c_1243,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1238,c_14])).

cnf(c_12990,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10953,c_1243])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13056,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_12990,c_8])).

cnf(c_14449,plain,
    ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k1_relat_1(sK1))) = k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k1_relat_1(sK1))) ),
    inference(superposition,[status(thm)],[c_1978,c_13056])).

cnf(c_14521,plain,
    ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k1_relat_1(sK1))) = k3_relat_1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_14449,c_1978])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_620,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X0))) = k1_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_625,plain,
    ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X0))) = k1_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3225,plain,
    ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) = k1_relat_1(k5_xboole_0(sK1,k4_xboole_0(X0,sK1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_625])).

cnf(c_3839,plain,
    ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) = k1_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_620,c_3225])).

cnf(c_11,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_628,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1244,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_628])).

cnf(c_1245,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1244,c_14])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_631,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1571,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_631])).

cnf(c_1592,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X0)),X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1571])).

cnf(c_1596,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1592,c_14])).

cnf(c_1719,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1)),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1596])).

cnf(c_1728,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X0,X1))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1719,c_14])).

cnf(c_3850,plain,
    ( r1_tarski(k1_relat_1(sK0),k5_xboole_0(k1_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(X0,k1_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3839,c_1728])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_622,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_630,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3234,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_630])).

cnf(c_1166,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_629,c_619])).

cnf(c_10163,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X1))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1739])).

cnf(c_10166,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10163,c_8,c_1166])).

cnf(c_20199,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3234,c_10166])).

cnf(c_20612,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_622,c_20199])).

cnf(c_21908,plain,
    ( r1_tarski(k1_relat_1(sK0),k5_xboole_0(k1_relat_1(k5_xboole_0(sK1,k1_xboole_0)),k4_xboole_0(X0,k1_relat_1(k5_xboole_0(sK1,k1_xboole_0))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3850,c_20612])).

cnf(c_21909,plain,
    ( r1_tarski(k1_relat_1(sK0),k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(X0,k1_relat_1(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21908,c_8])).

cnf(c_21918,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14521,c_21909])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X0))) = k2_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_624,plain,
    ( k5_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X0))) = k2_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1866,plain,
    ( k5_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(X0),k2_relat_1(sK0))) = k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(X0,sK0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_624])).

cnf(c_2842,plain,
    ( k5_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_621,c_1866])).

cnf(c_1725,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X2)),X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_631])).

cnf(c_7467,plain,
    ( r1_tarski(k2_relat_1(sK0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),X1)),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2842,c_1725])).

cnf(c_1865,plain,
    ( k5_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(X0),k2_relat_1(sK1))) = k2_relat_1(k5_xboole_0(sK1,k4_xboole_0(X0,sK1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_624])).

cnf(c_2675,plain,
    ( k5_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) = k2_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_620,c_1865])).

cnf(c_2814,plain,
    ( k5_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_2675,c_1243])).

cnf(c_8781,plain,
    ( k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k2_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_2814,c_2842])).

cnf(c_20717,plain,
    ( k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k2_relat_1(k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_20612,c_8781])).

cnf(c_20718,plain,
    ( k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k2_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_20717,c_8])).

cnf(c_21253,plain,
    ( r1_tarski(k2_relat_1(sK0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k2_relat_1(sK1),X1)),X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7467,c_20718])).

cnf(c_21267,plain,
    ( r1_tarski(k2_relat_1(sK0),k5_xboole_0(X0,k4_xboole_0(k3_relat_1(sK1),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1978,c_21253])).

cnf(c_21497,plain,
    ( r1_tarski(k2_relat_1(sK0),k5_xboole_0(k3_relat_1(sK1),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_21267])).

cnf(c_21505,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21497,c_8])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4384,plain,
    ( r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),X0)
    | ~ r1_tarski(k2_relat_1(sK0),X0)
    | ~ r1_tarski(k1_relat_1(sK0),X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_16265,plain,
    ( r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4384])).

cnf(c_16270,plain,
    ( r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1)) = iProver_top
    | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16265])).

cnf(c_357,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_665,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != X1
    | k3_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_724,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(X1)
    | k3_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_2454,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(X0))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(X0)
    | k3_relat_1(sK0) != k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_3720,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(sK1)
    | k3_relat_1(sK0) != k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_2454])).

cnf(c_3721,plain,
    ( k3_relat_1(sK1) != k3_relat_1(sK1)
    | k3_relat_1(sK0) != k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)))
    | r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1)) != iProver_top
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3720])).

cnf(c_356,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_826,plain,
    ( X0 != X1
    | k3_relat_1(sK0) != X1
    | k3_relat_1(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_1061,plain,
    ( X0 != k3_relat_1(sK0)
    | k3_relat_1(sK0) = X0
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1288,plain,
    ( k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))) != k3_relat_1(sK0)
    | k3_relat_1(sK0) = k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)))
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_355,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_773,plain,
    ( k3_relat_1(sK1) = k3_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_363,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_371,plain,
    ( k3_relat_1(sK0) = k3_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_63,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_59,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_33,plain,
    ( ~ v1_relat_1(sK0)
    | k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))) = k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21918,c_21505,c_16270,c_3721,c_1288,c_773,c_371,c_63,c_59,c_33,c_25,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:33:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.68/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/1.48  
% 7.68/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.68/1.48  
% 7.68/1.48  ------  iProver source info
% 7.68/1.48  
% 7.68/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.68/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.68/1.48  git: non_committed_changes: false
% 7.68/1.48  git: last_make_outside_of_git: false
% 7.68/1.48  
% 7.68/1.48  ------ 
% 7.68/1.48  
% 7.68/1.48  ------ Input Options
% 7.68/1.48  
% 7.68/1.48  --out_options                           all
% 7.68/1.48  --tptp_safe_out                         true
% 7.68/1.48  --problem_path                          ""
% 7.68/1.48  --include_path                          ""
% 7.68/1.48  --clausifier                            res/vclausify_rel
% 7.68/1.48  --clausifier_options                    ""
% 7.68/1.48  --stdin                                 false
% 7.68/1.48  --stats_out                             all
% 7.68/1.48  
% 7.68/1.48  ------ General Options
% 7.68/1.48  
% 7.68/1.48  --fof                                   false
% 7.68/1.48  --time_out_real                         305.
% 7.68/1.48  --time_out_virtual                      -1.
% 7.68/1.48  --symbol_type_check                     false
% 7.68/1.48  --clausify_out                          false
% 7.68/1.48  --sig_cnt_out                           false
% 7.68/1.48  --trig_cnt_out                          false
% 7.68/1.48  --trig_cnt_out_tolerance                1.
% 7.68/1.48  --trig_cnt_out_sk_spl                   false
% 7.68/1.48  --abstr_cl_out                          false
% 7.68/1.48  
% 7.68/1.48  ------ Global Options
% 7.68/1.48  
% 7.68/1.48  --schedule                              default
% 7.68/1.48  --add_important_lit                     false
% 7.68/1.48  --prop_solver_per_cl                    1000
% 7.68/1.48  --min_unsat_core                        false
% 7.68/1.48  --soft_assumptions                      false
% 7.68/1.48  --soft_lemma_size                       3
% 7.68/1.48  --prop_impl_unit_size                   0
% 7.68/1.48  --prop_impl_unit                        []
% 7.68/1.48  --share_sel_clauses                     true
% 7.68/1.48  --reset_solvers                         false
% 7.68/1.48  --bc_imp_inh                            [conj_cone]
% 7.68/1.48  --conj_cone_tolerance                   3.
% 7.68/1.48  --extra_neg_conj                        none
% 7.68/1.48  --large_theory_mode                     true
% 7.68/1.48  --prolific_symb_bound                   200
% 7.68/1.48  --lt_threshold                          2000
% 7.68/1.48  --clause_weak_htbl                      true
% 7.68/1.48  --gc_record_bc_elim                     false
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing Options
% 7.68/1.48  
% 7.68/1.48  --preprocessing_flag                    true
% 7.68/1.48  --time_out_prep_mult                    0.1
% 7.68/1.48  --splitting_mode                        input
% 7.68/1.48  --splitting_grd                         true
% 7.68/1.48  --splitting_cvd                         false
% 7.68/1.48  --splitting_cvd_svl                     false
% 7.68/1.48  --splitting_nvd                         32
% 7.68/1.48  --sub_typing                            true
% 7.68/1.48  --prep_gs_sim                           true
% 7.68/1.48  --prep_unflatten                        true
% 7.68/1.48  --prep_res_sim                          true
% 7.68/1.48  --prep_upred                            true
% 7.68/1.48  --prep_sem_filter                       exhaustive
% 7.68/1.48  --prep_sem_filter_out                   false
% 7.68/1.48  --pred_elim                             true
% 7.68/1.48  --res_sim_input                         true
% 7.68/1.48  --eq_ax_congr_red                       true
% 7.68/1.48  --pure_diseq_elim                       true
% 7.68/1.48  --brand_transform                       false
% 7.68/1.48  --non_eq_to_eq                          false
% 7.68/1.48  --prep_def_merge                        true
% 7.68/1.48  --prep_def_merge_prop_impl              false
% 7.68/1.48  --prep_def_merge_mbd                    true
% 7.68/1.48  --prep_def_merge_tr_red                 false
% 7.68/1.48  --prep_def_merge_tr_cl                  false
% 7.68/1.48  --smt_preprocessing                     true
% 7.68/1.48  --smt_ac_axioms                         fast
% 7.68/1.48  --preprocessed_out                      false
% 7.68/1.48  --preprocessed_stats                    false
% 7.68/1.48  
% 7.68/1.48  ------ Abstraction refinement Options
% 7.68/1.48  
% 7.68/1.48  --abstr_ref                             []
% 7.68/1.48  --abstr_ref_prep                        false
% 7.68/1.48  --abstr_ref_until_sat                   false
% 7.68/1.48  --abstr_ref_sig_restrict                funpre
% 7.68/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.48  --abstr_ref_under                       []
% 7.68/1.48  
% 7.68/1.48  ------ SAT Options
% 7.68/1.48  
% 7.68/1.48  --sat_mode                              false
% 7.68/1.48  --sat_fm_restart_options                ""
% 7.68/1.48  --sat_gr_def                            false
% 7.68/1.48  --sat_epr_types                         true
% 7.68/1.48  --sat_non_cyclic_types                  false
% 7.68/1.48  --sat_finite_models                     false
% 7.68/1.48  --sat_fm_lemmas                         false
% 7.68/1.48  --sat_fm_prep                           false
% 7.68/1.48  --sat_fm_uc_incr                        true
% 7.68/1.48  --sat_out_model                         small
% 7.68/1.48  --sat_out_clauses                       false
% 7.68/1.48  
% 7.68/1.48  ------ QBF Options
% 7.68/1.48  
% 7.68/1.48  --qbf_mode                              false
% 7.68/1.48  --qbf_elim_univ                         false
% 7.68/1.48  --qbf_dom_inst                          none
% 7.68/1.48  --qbf_dom_pre_inst                      false
% 7.68/1.48  --qbf_sk_in                             false
% 7.68/1.48  --qbf_pred_elim                         true
% 7.68/1.48  --qbf_split                             512
% 7.68/1.48  
% 7.68/1.48  ------ BMC1 Options
% 7.68/1.48  
% 7.68/1.48  --bmc1_incremental                      false
% 7.68/1.48  --bmc1_axioms                           reachable_all
% 7.68/1.48  --bmc1_min_bound                        0
% 7.68/1.48  --bmc1_max_bound                        -1
% 7.68/1.48  --bmc1_max_bound_default                -1
% 7.68/1.48  --bmc1_symbol_reachability              true
% 7.68/1.48  --bmc1_property_lemmas                  false
% 7.68/1.48  --bmc1_k_induction                      false
% 7.68/1.48  --bmc1_non_equiv_states                 false
% 7.68/1.48  --bmc1_deadlock                         false
% 7.68/1.48  --bmc1_ucm                              false
% 7.68/1.48  --bmc1_add_unsat_core                   none
% 7.68/1.48  --bmc1_unsat_core_children              false
% 7.68/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.48  --bmc1_out_stat                         full
% 7.68/1.48  --bmc1_ground_init                      false
% 7.68/1.48  --bmc1_pre_inst_next_state              false
% 7.68/1.48  --bmc1_pre_inst_state                   false
% 7.68/1.48  --bmc1_pre_inst_reach_state             false
% 7.68/1.48  --bmc1_out_unsat_core                   false
% 7.68/1.48  --bmc1_aig_witness_out                  false
% 7.68/1.48  --bmc1_verbose                          false
% 7.68/1.48  --bmc1_dump_clauses_tptp                false
% 7.68/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.48  --bmc1_dump_file                        -
% 7.68/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.48  --bmc1_ucm_extend_mode                  1
% 7.68/1.48  --bmc1_ucm_init_mode                    2
% 7.68/1.48  --bmc1_ucm_cone_mode                    none
% 7.68/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.48  --bmc1_ucm_relax_model                  4
% 7.68/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.48  --bmc1_ucm_layered_model                none
% 7.68/1.48  --bmc1_ucm_max_lemma_size               10
% 7.68/1.48  
% 7.68/1.48  ------ AIG Options
% 7.68/1.48  
% 7.68/1.48  --aig_mode                              false
% 7.68/1.48  
% 7.68/1.48  ------ Instantiation Options
% 7.68/1.48  
% 7.68/1.48  --instantiation_flag                    true
% 7.68/1.48  --inst_sos_flag                         true
% 7.68/1.48  --inst_sos_phase                        true
% 7.68/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.48  --inst_lit_sel_side                     num_symb
% 7.68/1.48  --inst_solver_per_active                1400
% 7.68/1.48  --inst_solver_calls_frac                1.
% 7.68/1.48  --inst_passive_queue_type               priority_queues
% 7.68/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.48  --inst_passive_queues_freq              [25;2]
% 7.68/1.48  --inst_dismatching                      true
% 7.68/1.48  --inst_eager_unprocessed_to_passive     true
% 7.68/1.48  --inst_prop_sim_given                   true
% 7.68/1.48  --inst_prop_sim_new                     false
% 7.68/1.48  --inst_subs_new                         false
% 7.68/1.48  --inst_eq_res_simp                      false
% 7.68/1.48  --inst_subs_given                       false
% 7.68/1.48  --inst_orphan_elimination               true
% 7.68/1.48  --inst_learning_loop_flag               true
% 7.68/1.48  --inst_learning_start                   3000
% 7.68/1.48  --inst_learning_factor                  2
% 7.68/1.48  --inst_start_prop_sim_after_learn       3
% 7.68/1.48  --inst_sel_renew                        solver
% 7.68/1.48  --inst_lit_activity_flag                true
% 7.68/1.48  --inst_restr_to_given                   false
% 7.68/1.48  --inst_activity_threshold               500
% 7.68/1.48  --inst_out_proof                        true
% 7.68/1.48  
% 7.68/1.48  ------ Resolution Options
% 7.68/1.48  
% 7.68/1.48  --resolution_flag                       true
% 7.68/1.48  --res_lit_sel                           adaptive
% 7.68/1.48  --res_lit_sel_side                      none
% 7.68/1.48  --res_ordering                          kbo
% 7.68/1.48  --res_to_prop_solver                    active
% 7.68/1.48  --res_prop_simpl_new                    false
% 7.68/1.48  --res_prop_simpl_given                  true
% 7.68/1.48  --res_passive_queue_type                priority_queues
% 7.68/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.48  --res_passive_queues_freq               [15;5]
% 7.68/1.48  --res_forward_subs                      full
% 7.68/1.48  --res_backward_subs                     full
% 7.68/1.48  --res_forward_subs_resolution           true
% 7.68/1.48  --res_backward_subs_resolution          true
% 7.68/1.48  --res_orphan_elimination                true
% 7.68/1.48  --res_time_limit                        2.
% 7.68/1.48  --res_out_proof                         true
% 7.68/1.48  
% 7.68/1.48  ------ Superposition Options
% 7.68/1.48  
% 7.68/1.48  --superposition_flag                    true
% 7.68/1.48  --sup_passive_queue_type                priority_queues
% 7.68/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.48  --demod_completeness_check              fast
% 7.68/1.48  --demod_use_ground                      true
% 7.68/1.48  --sup_to_prop_solver                    passive
% 7.68/1.48  --sup_prop_simpl_new                    true
% 7.68/1.48  --sup_prop_simpl_given                  true
% 7.68/1.48  --sup_fun_splitting                     true
% 7.68/1.48  --sup_smt_interval                      50000
% 7.68/1.48  
% 7.68/1.48  ------ Superposition Simplification Setup
% 7.68/1.48  
% 7.68/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.68/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.68/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.68/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.68/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.68/1.48  --sup_immed_triv                        [TrivRules]
% 7.68/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_immed_bw_main                     []
% 7.68/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.68/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_input_bw                          []
% 7.68/1.48  
% 7.68/1.48  ------ Combination Options
% 7.68/1.48  
% 7.68/1.48  --comb_res_mult                         3
% 7.68/1.48  --comb_sup_mult                         2
% 7.68/1.48  --comb_inst_mult                        10
% 7.68/1.48  
% 7.68/1.48  ------ Debug Options
% 7.68/1.48  
% 7.68/1.48  --dbg_backtrace                         false
% 7.68/1.48  --dbg_dump_prop_clauses                 false
% 7.68/1.48  --dbg_dump_prop_clauses_file            -
% 7.68/1.48  --dbg_out_stat                          false
% 7.68/1.48  ------ Parsing...
% 7.68/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.48  ------ Proving...
% 7.68/1.48  ------ Problem Properties 
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  clauses                                 19
% 7.68/1.48  conjectures                             4
% 7.68/1.48  EPR                                     6
% 7.68/1.48  Horn                                    19
% 7.68/1.48  unary                                   10
% 7.68/1.48  binary                                  4
% 7.68/1.48  lits                                    33
% 7.68/1.48  lits eq                                 8
% 7.68/1.48  fd_pure                                 0
% 7.68/1.48  fd_pseudo                               0
% 7.68/1.48  fd_cond                                 0
% 7.68/1.48  fd_pseudo_cond                          1
% 7.68/1.48  AC symbols                              0
% 7.68/1.48  
% 7.68/1.48  ------ Schedule dynamic 5 is on 
% 7.68/1.48  
% 7.68/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  ------ 
% 7.68/1.48  Current options:
% 7.68/1.48  ------ 
% 7.68/1.48  
% 7.68/1.48  ------ Input Options
% 7.68/1.48  
% 7.68/1.48  --out_options                           all
% 7.68/1.48  --tptp_safe_out                         true
% 7.68/1.48  --problem_path                          ""
% 7.68/1.48  --include_path                          ""
% 7.68/1.48  --clausifier                            res/vclausify_rel
% 7.68/1.48  --clausifier_options                    ""
% 7.68/1.48  --stdin                                 false
% 7.68/1.48  --stats_out                             all
% 7.68/1.48  
% 7.68/1.48  ------ General Options
% 7.68/1.48  
% 7.68/1.48  --fof                                   false
% 7.68/1.48  --time_out_real                         305.
% 7.68/1.48  --time_out_virtual                      -1.
% 7.68/1.48  --symbol_type_check                     false
% 7.68/1.48  --clausify_out                          false
% 7.68/1.48  --sig_cnt_out                           false
% 7.68/1.48  --trig_cnt_out                          false
% 7.68/1.48  --trig_cnt_out_tolerance                1.
% 7.68/1.48  --trig_cnt_out_sk_spl                   false
% 7.68/1.48  --abstr_cl_out                          false
% 7.68/1.48  
% 7.68/1.48  ------ Global Options
% 7.68/1.48  
% 7.68/1.48  --schedule                              default
% 7.68/1.48  --add_important_lit                     false
% 7.68/1.48  --prop_solver_per_cl                    1000
% 7.68/1.48  --min_unsat_core                        false
% 7.68/1.48  --soft_assumptions                      false
% 7.68/1.48  --soft_lemma_size                       3
% 7.68/1.48  --prop_impl_unit_size                   0
% 7.68/1.48  --prop_impl_unit                        []
% 7.68/1.48  --share_sel_clauses                     true
% 7.68/1.48  --reset_solvers                         false
% 7.68/1.48  --bc_imp_inh                            [conj_cone]
% 7.68/1.48  --conj_cone_tolerance                   3.
% 7.68/1.48  --extra_neg_conj                        none
% 7.68/1.48  --large_theory_mode                     true
% 7.68/1.48  --prolific_symb_bound                   200
% 7.68/1.48  --lt_threshold                          2000
% 7.68/1.48  --clause_weak_htbl                      true
% 7.68/1.48  --gc_record_bc_elim                     false
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing Options
% 7.68/1.48  
% 7.68/1.48  --preprocessing_flag                    true
% 7.68/1.48  --time_out_prep_mult                    0.1
% 7.68/1.48  --splitting_mode                        input
% 7.68/1.48  --splitting_grd                         true
% 7.68/1.48  --splitting_cvd                         false
% 7.68/1.48  --splitting_cvd_svl                     false
% 7.68/1.48  --splitting_nvd                         32
% 7.68/1.48  --sub_typing                            true
% 7.68/1.48  --prep_gs_sim                           true
% 7.68/1.48  --prep_unflatten                        true
% 7.68/1.48  --prep_res_sim                          true
% 7.68/1.48  --prep_upred                            true
% 7.68/1.48  --prep_sem_filter                       exhaustive
% 7.68/1.48  --prep_sem_filter_out                   false
% 7.68/1.48  --pred_elim                             true
% 7.68/1.48  --res_sim_input                         true
% 7.68/1.48  --eq_ax_congr_red                       true
% 7.68/1.48  --pure_diseq_elim                       true
% 7.68/1.48  --brand_transform                       false
% 7.68/1.48  --non_eq_to_eq                          false
% 7.68/1.48  --prep_def_merge                        true
% 7.68/1.48  --prep_def_merge_prop_impl              false
% 7.68/1.48  --prep_def_merge_mbd                    true
% 7.68/1.48  --prep_def_merge_tr_red                 false
% 7.68/1.48  --prep_def_merge_tr_cl                  false
% 7.68/1.48  --smt_preprocessing                     true
% 7.68/1.48  --smt_ac_axioms                         fast
% 7.68/1.48  --preprocessed_out                      false
% 7.68/1.48  --preprocessed_stats                    false
% 7.68/1.48  
% 7.68/1.48  ------ Abstraction refinement Options
% 7.68/1.48  
% 7.68/1.48  --abstr_ref                             []
% 7.68/1.48  --abstr_ref_prep                        false
% 7.68/1.48  --abstr_ref_until_sat                   false
% 7.68/1.48  --abstr_ref_sig_restrict                funpre
% 7.68/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.48  --abstr_ref_under                       []
% 7.68/1.48  
% 7.68/1.48  ------ SAT Options
% 7.68/1.48  
% 7.68/1.48  --sat_mode                              false
% 7.68/1.48  --sat_fm_restart_options                ""
% 7.68/1.48  --sat_gr_def                            false
% 7.68/1.48  --sat_epr_types                         true
% 7.68/1.48  --sat_non_cyclic_types                  false
% 7.68/1.48  --sat_finite_models                     false
% 7.68/1.48  --sat_fm_lemmas                         false
% 7.68/1.48  --sat_fm_prep                           false
% 7.68/1.48  --sat_fm_uc_incr                        true
% 7.68/1.48  --sat_out_model                         small
% 7.68/1.48  --sat_out_clauses                       false
% 7.68/1.48  
% 7.68/1.48  ------ QBF Options
% 7.68/1.48  
% 7.68/1.48  --qbf_mode                              false
% 7.68/1.48  --qbf_elim_univ                         false
% 7.68/1.48  --qbf_dom_inst                          none
% 7.68/1.48  --qbf_dom_pre_inst                      false
% 7.68/1.48  --qbf_sk_in                             false
% 7.68/1.48  --qbf_pred_elim                         true
% 7.68/1.48  --qbf_split                             512
% 7.68/1.48  
% 7.68/1.48  ------ BMC1 Options
% 7.68/1.48  
% 7.68/1.48  --bmc1_incremental                      false
% 7.68/1.48  --bmc1_axioms                           reachable_all
% 7.68/1.48  --bmc1_min_bound                        0
% 7.68/1.48  --bmc1_max_bound                        -1
% 7.68/1.48  --bmc1_max_bound_default                -1
% 7.68/1.48  --bmc1_symbol_reachability              true
% 7.68/1.48  --bmc1_property_lemmas                  false
% 7.68/1.48  --bmc1_k_induction                      false
% 7.68/1.48  --bmc1_non_equiv_states                 false
% 7.68/1.48  --bmc1_deadlock                         false
% 7.68/1.48  --bmc1_ucm                              false
% 7.68/1.48  --bmc1_add_unsat_core                   none
% 7.68/1.48  --bmc1_unsat_core_children              false
% 7.68/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.48  --bmc1_out_stat                         full
% 7.68/1.48  --bmc1_ground_init                      false
% 7.68/1.48  --bmc1_pre_inst_next_state              false
% 7.68/1.48  --bmc1_pre_inst_state                   false
% 7.68/1.48  --bmc1_pre_inst_reach_state             false
% 7.68/1.48  --bmc1_out_unsat_core                   false
% 7.68/1.48  --bmc1_aig_witness_out                  false
% 7.68/1.48  --bmc1_verbose                          false
% 7.68/1.48  --bmc1_dump_clauses_tptp                false
% 7.68/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.48  --bmc1_dump_file                        -
% 7.68/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.48  --bmc1_ucm_extend_mode                  1
% 7.68/1.48  --bmc1_ucm_init_mode                    2
% 7.68/1.48  --bmc1_ucm_cone_mode                    none
% 7.68/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.48  --bmc1_ucm_relax_model                  4
% 7.68/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.48  --bmc1_ucm_layered_model                none
% 7.68/1.48  --bmc1_ucm_max_lemma_size               10
% 7.68/1.48  
% 7.68/1.48  ------ AIG Options
% 7.68/1.48  
% 7.68/1.48  --aig_mode                              false
% 7.68/1.48  
% 7.68/1.48  ------ Instantiation Options
% 7.68/1.48  
% 7.68/1.48  --instantiation_flag                    true
% 7.68/1.48  --inst_sos_flag                         true
% 7.68/1.48  --inst_sos_phase                        true
% 7.68/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.48  --inst_lit_sel_side                     none
% 7.68/1.48  --inst_solver_per_active                1400
% 7.68/1.48  --inst_solver_calls_frac                1.
% 7.68/1.48  --inst_passive_queue_type               priority_queues
% 7.68/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.48  --inst_passive_queues_freq              [25;2]
% 7.68/1.48  --inst_dismatching                      true
% 7.68/1.48  --inst_eager_unprocessed_to_passive     true
% 7.68/1.48  --inst_prop_sim_given                   true
% 7.68/1.48  --inst_prop_sim_new                     false
% 7.68/1.48  --inst_subs_new                         false
% 7.68/1.48  --inst_eq_res_simp                      false
% 7.68/1.48  --inst_subs_given                       false
% 7.68/1.48  --inst_orphan_elimination               true
% 7.68/1.48  --inst_learning_loop_flag               true
% 7.68/1.48  --inst_learning_start                   3000
% 7.68/1.48  --inst_learning_factor                  2
% 7.68/1.48  --inst_start_prop_sim_after_learn       3
% 7.68/1.48  --inst_sel_renew                        solver
% 7.68/1.48  --inst_lit_activity_flag                true
% 7.68/1.48  --inst_restr_to_given                   false
% 7.68/1.48  --inst_activity_threshold               500
% 7.68/1.48  --inst_out_proof                        true
% 7.68/1.48  
% 7.68/1.48  ------ Resolution Options
% 7.68/1.48  
% 7.68/1.48  --resolution_flag                       false
% 7.68/1.48  --res_lit_sel                           adaptive
% 7.68/1.48  --res_lit_sel_side                      none
% 7.68/1.48  --res_ordering                          kbo
% 7.68/1.48  --res_to_prop_solver                    active
% 7.68/1.48  --res_prop_simpl_new                    false
% 7.68/1.48  --res_prop_simpl_given                  true
% 7.68/1.48  --res_passive_queue_type                priority_queues
% 7.68/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.48  --res_passive_queues_freq               [15;5]
% 7.68/1.48  --res_forward_subs                      full
% 7.68/1.48  --res_backward_subs                     full
% 7.68/1.48  --res_forward_subs_resolution           true
% 7.68/1.48  --res_backward_subs_resolution          true
% 7.68/1.48  --res_orphan_elimination                true
% 7.68/1.48  --res_time_limit                        2.
% 7.68/1.48  --res_out_proof                         true
% 7.68/1.48  
% 7.68/1.48  ------ Superposition Options
% 7.68/1.48  
% 7.68/1.48  --superposition_flag                    true
% 7.68/1.48  --sup_passive_queue_type                priority_queues
% 7.68/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.48  --demod_completeness_check              fast
% 7.68/1.48  --demod_use_ground                      true
% 7.68/1.48  --sup_to_prop_solver                    passive
% 7.68/1.48  --sup_prop_simpl_new                    true
% 7.68/1.48  --sup_prop_simpl_given                  true
% 7.68/1.48  --sup_fun_splitting                     true
% 7.68/1.48  --sup_smt_interval                      50000
% 7.68/1.48  
% 7.68/1.48  ------ Superposition Simplification Setup
% 7.68/1.48  
% 7.68/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.68/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.68/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.68/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.68/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.68/1.48  --sup_immed_triv                        [TrivRules]
% 7.68/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_immed_bw_main                     []
% 7.68/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.68/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_input_bw                          []
% 7.68/1.48  
% 7.68/1.48  ------ Combination Options
% 7.68/1.48  
% 7.68/1.48  --comb_res_mult                         3
% 7.68/1.48  --comb_sup_mult                         2
% 7.68/1.48  --comb_inst_mult                        10
% 7.68/1.48  
% 7.68/1.48  ------ Debug Options
% 7.68/1.48  
% 7.68/1.48  --dbg_backtrace                         false
% 7.68/1.48  --dbg_dump_prop_clauses                 false
% 7.68/1.48  --dbg_dump_prop_clauses_file            -
% 7.68/1.48  --dbg_out_stat                          false
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  ------ Proving...
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  % SZS status Theorem for theBenchmark.p
% 7.68/1.48  
% 7.68/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.68/1.48  
% 7.68/1.48  fof(f20,conjecture,(
% 7.68/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f21,negated_conjecture,(
% 7.68/1.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.68/1.48    inference(negated_conjecture,[],[f20])).
% 7.68/1.48  
% 7.68/1.48  fof(f34,plain,(
% 7.68/1.48    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.68/1.48    inference(ennf_transformation,[],[f21])).
% 7.68/1.48  
% 7.68/1.48  fof(f35,plain,(
% 7.68/1.48    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.68/1.48    inference(flattening,[],[f34])).
% 7.68/1.48  
% 7.68/1.48  fof(f39,plain,(
% 7.68/1.48    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK1)) & r1_tarski(X0,sK1) & v1_relat_1(sK1))) )),
% 7.68/1.48    introduced(choice_axiom,[])).
% 7.68/1.48  
% 7.68/1.48  fof(f38,plain,(
% 7.68/1.48    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.68/1.48    introduced(choice_axiom,[])).
% 7.68/1.48  
% 7.68/1.48  fof(f40,plain,(
% 7.68/1.48    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.68/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f39,f38])).
% 7.68/1.48  
% 7.68/1.48  fof(f63,plain,(
% 7.68/1.48    v1_relat_1(sK1)),
% 7.68/1.48    inference(cnf_transformation,[],[f40])).
% 7.68/1.48  
% 7.68/1.48  fof(f17,axiom,(
% 7.68/1.48    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f31,plain,(
% 7.68/1.48    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.68/1.48    inference(ennf_transformation,[],[f17])).
% 7.68/1.48  
% 7.68/1.48  fof(f59,plain,(
% 7.68/1.48    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f31])).
% 7.68/1.48  
% 7.68/1.48  fof(f12,axiom,(
% 7.68/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f54,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.68/1.48    inference(cnf_transformation,[],[f12])).
% 7.68/1.48  
% 7.68/1.48  fof(f73,plain,(
% 7.68/1.48    ( ! [X0] : (k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.68/1.48    inference(definition_unfolding,[],[f59,f54])).
% 7.68/1.48  
% 7.68/1.48  fof(f13,axiom,(
% 7.68/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f55,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f13])).
% 7.68/1.48  
% 7.68/1.48  fof(f14,axiom,(
% 7.68/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f56,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f14])).
% 7.68/1.48  
% 7.68/1.48  fof(f15,axiom,(
% 7.68/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f57,plain,(
% 7.68/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f15])).
% 7.68/1.48  
% 7.68/1.48  fof(f66,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.68/1.48    inference(definition_unfolding,[],[f56,f57])).
% 7.68/1.48  
% 7.68/1.48  fof(f71,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 7.68/1.48    inference(definition_unfolding,[],[f55,f66,f66])).
% 7.68/1.48  
% 7.68/1.48  fof(f16,axiom,(
% 7.68/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f58,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.68/1.48    inference(cnf_transformation,[],[f16])).
% 7.68/1.48  
% 7.68/1.48  fof(f72,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 7.68/1.48    inference(definition_unfolding,[],[f58,f54,f66])).
% 7.68/1.48  
% 7.68/1.48  fof(f6,axiom,(
% 7.68/1.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f48,plain,(
% 7.68/1.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f6])).
% 7.68/1.48  
% 7.68/1.48  fof(f3,axiom,(
% 7.68/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f23,plain,(
% 7.68/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.68/1.48    inference(ennf_transformation,[],[f3])).
% 7.68/1.48  
% 7.68/1.48  fof(f45,plain,(
% 7.68/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f23])).
% 7.68/1.48  
% 7.68/1.48  fof(f67,plain,(
% 7.68/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 7.68/1.48    inference(definition_unfolding,[],[f45,f54])).
% 7.68/1.48  
% 7.68/1.48  fof(f1,axiom,(
% 7.68/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f22,plain,(
% 7.68/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.68/1.48    inference(ennf_transformation,[],[f1])).
% 7.68/1.48  
% 7.68/1.48  fof(f41,plain,(
% 7.68/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f22])).
% 7.68/1.48  
% 7.68/1.48  fof(f8,axiom,(
% 7.68/1.48    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f27,plain,(
% 7.68/1.48    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 7.68/1.48    inference(ennf_transformation,[],[f8])).
% 7.68/1.48  
% 7.68/1.48  fof(f28,plain,(
% 7.68/1.48    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 7.68/1.48    inference(flattening,[],[f27])).
% 7.68/1.48  
% 7.68/1.48  fof(f50,plain,(
% 7.68/1.48    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f28])).
% 7.68/1.48  
% 7.68/1.48  fof(f9,axiom,(
% 7.68/1.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f51,plain,(
% 7.68/1.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f9])).
% 7.68/1.48  
% 7.68/1.48  fof(f7,axiom,(
% 7.68/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f49,plain,(
% 7.68/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.68/1.48    inference(cnf_transformation,[],[f7])).
% 7.68/1.48  
% 7.68/1.48  fof(f62,plain,(
% 7.68/1.48    v1_relat_1(sK0)),
% 7.68/1.48    inference(cnf_transformation,[],[f40])).
% 7.68/1.48  
% 7.68/1.48  fof(f18,axiom,(
% 7.68/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f32,plain,(
% 7.68/1.48    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.68/1.48    inference(ennf_transformation,[],[f18])).
% 7.68/1.48  
% 7.68/1.48  fof(f60,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f32])).
% 7.68/1.48  
% 7.68/1.48  fof(f74,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X0))) = k1_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.68/1.48    inference(definition_unfolding,[],[f60,f54,f54])).
% 7.68/1.48  
% 7.68/1.48  fof(f10,axiom,(
% 7.68/1.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f52,plain,(
% 7.68/1.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.68/1.48    inference(cnf_transformation,[],[f10])).
% 7.68/1.48  
% 7.68/1.48  fof(f69,plain,(
% 7.68/1.48    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 7.68/1.48    inference(definition_unfolding,[],[f52,f54])).
% 7.68/1.48  
% 7.68/1.48  fof(f4,axiom,(
% 7.68/1.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f24,plain,(
% 7.68/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.68/1.48    inference(ennf_transformation,[],[f4])).
% 7.68/1.48  
% 7.68/1.48  fof(f46,plain,(
% 7.68/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f24])).
% 7.68/1.48  
% 7.68/1.48  fof(f68,plain,(
% 7.68/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2)) )),
% 7.68/1.48    inference(definition_unfolding,[],[f46,f54])).
% 7.68/1.48  
% 7.68/1.48  fof(f64,plain,(
% 7.68/1.48    r1_tarski(sK0,sK1)),
% 7.68/1.48    inference(cnf_transformation,[],[f40])).
% 7.68/1.48  
% 7.68/1.48  fof(f5,axiom,(
% 7.68/1.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f25,plain,(
% 7.68/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.68/1.48    inference(ennf_transformation,[],[f5])).
% 7.68/1.48  
% 7.68/1.48  fof(f26,plain,(
% 7.68/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.68/1.48    inference(flattening,[],[f25])).
% 7.68/1.48  
% 7.68/1.48  fof(f47,plain,(
% 7.68/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f26])).
% 7.68/1.48  
% 7.68/1.48  fof(f19,axiom,(
% 7.68/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f33,plain,(
% 7.68/1.48    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.68/1.48    inference(ennf_transformation,[],[f19])).
% 7.68/1.48  
% 7.68/1.48  fof(f61,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f33])).
% 7.68/1.48  
% 7.68/1.48  fof(f75,plain,(
% 7.68/1.48    ( ! [X0,X1] : (k5_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X0))) = k2_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.68/1.48    inference(definition_unfolding,[],[f61,f54,f54])).
% 7.68/1.48  
% 7.68/1.48  fof(f11,axiom,(
% 7.68/1.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f29,plain,(
% 7.68/1.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.68/1.48    inference(ennf_transformation,[],[f11])).
% 7.68/1.48  
% 7.68/1.48  fof(f30,plain,(
% 7.68/1.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.68/1.48    inference(flattening,[],[f29])).
% 7.68/1.48  
% 7.68/1.48  fof(f53,plain,(
% 7.68/1.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f30])).
% 7.68/1.48  
% 7.68/1.48  fof(f70,plain,(
% 7.68/1.48    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.68/1.48    inference(definition_unfolding,[],[f53,f54])).
% 7.68/1.48  
% 7.68/1.48  fof(f2,axiom,(
% 7.68/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.68/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.48  
% 7.68/1.48  fof(f36,plain,(
% 7.68/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.68/1.48    inference(nnf_transformation,[],[f2])).
% 7.68/1.48  
% 7.68/1.48  fof(f37,plain,(
% 7.68/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.68/1.48    inference(flattening,[],[f36])).
% 7.68/1.48  
% 7.68/1.48  fof(f44,plain,(
% 7.68/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.68/1.48    inference(cnf_transformation,[],[f37])).
% 7.68/1.48  
% 7.68/1.48  fof(f42,plain,(
% 7.68/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.68/1.48    inference(cnf_transformation,[],[f37])).
% 7.68/1.48  
% 7.68/1.48  fof(f77,plain,(
% 7.68/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.68/1.48    inference(equality_resolution,[],[f42])).
% 7.68/1.48  
% 7.68/1.48  fof(f65,plain,(
% 7.68/1.48    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 7.68/1.48    inference(cnf_transformation,[],[f40])).
% 7.68/1.48  
% 7.68/1.48  cnf(c_20,negated_conjecture,
% 7.68/1.48      ( v1_relat_1(sK1) ),
% 7.68/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_621,plain,
% 7.68/1.48      ( v1_relat_1(sK1) = iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_15,plain,
% 7.68/1.48      ( ~ v1_relat_1(X0)
% 7.68/1.48      | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
% 7.68/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_626,plain,
% 7.68/1.48      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
% 7.68/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1978,plain,
% 7.68/1.48      ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k1_relat_1(sK1))) = k3_relat_1(sK1) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_621,c_626]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_13,plain,
% 7.68/1.48      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 7.68/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_14,plain,
% 7.68/1.48      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.68/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1238,plain,
% 7.68/1.48      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_13,c_14]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_7,plain,
% 7.68/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.68/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_629,plain,
% 7.68/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_4,plain,
% 7.68/1.48      ( ~ r1_tarski(X0,X1)
% 7.68/1.48      | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 7.68/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_632,plain,
% 7.68/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.68/1.48      | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) = iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_0,plain,
% 7.68/1.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.68/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_9,plain,
% 7.68/1.48      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 7.68/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_10,plain,
% 7.68/1.48      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.68/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_213,plain,
% 7.68/1.48      ( ~ r1_tarski(X0,X1)
% 7.68/1.48      | v1_xboole_0(X0)
% 7.68/1.48      | X2 != X1
% 7.68/1.48      | k4_xboole_0(X3,X2) != X0 ),
% 7.68/1.48      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_214,plain,
% 7.68/1.48      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
% 7.68/1.48      | v1_xboole_0(k4_xboole_0(X0,X1)) ),
% 7.68/1.48      inference(unflattening,[status(thm)],[c_213]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_228,plain,
% 7.68/1.48      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
% 7.68/1.48      | k4_xboole_0(X0,X1) != X2
% 7.68/1.48      | k1_xboole_0 = X2 ),
% 7.68/1.48      inference(resolution_lifted,[status(thm)],[c_0,c_214]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_229,plain,
% 7.68/1.48      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
% 7.68/1.48      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 7.68/1.48      inference(unflattening,[status(thm)],[c_228]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_619,plain,
% 7.68/1.48      ( k1_xboole_0 = k4_xboole_0(X0,X1)
% 7.68/1.48      | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1739,plain,
% 7.68/1.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0
% 7.68/1.48      | r1_tarski(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X2) != iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_632,c_619]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_10147,plain,
% 7.68/1.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_629,c_1739]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_10854,plain,
% 7.68/1.48      ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1238,c_10147]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_10953,plain,
% 7.68/1.48      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 7.68/1.48      inference(light_normalisation,[status(thm)],[c_10854,c_14]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1243,plain,
% 7.68/1.48      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1238,c_14]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_12990,plain,
% 7.68/1.48      ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_10953,c_1243]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_8,plain,
% 7.68/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.68/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_13056,plain,
% 7.68/1.48      ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_12990,c_8]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_14449,plain,
% 7.68/1.48      ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k1_relat_1(sK1))) = k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k1_relat_1(sK1))) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1978,c_13056]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_14521,plain,
% 7.68/1.48      ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k1_relat_1(sK1))) = k3_relat_1(sK1) ),
% 7.68/1.48      inference(light_normalisation,[status(thm)],[c_14449,c_1978]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_21,negated_conjecture,
% 7.68/1.48      ( v1_relat_1(sK0) ),
% 7.68/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_620,plain,
% 7.68/1.48      ( v1_relat_1(sK0) = iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_16,plain,
% 7.68/1.48      ( ~ v1_relat_1(X0)
% 7.68/1.48      | ~ v1_relat_1(X1)
% 7.68/1.48      | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X0))) = k1_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 7.68/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_625,plain,
% 7.68/1.48      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X0))) = k1_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)))
% 7.68/1.48      | v1_relat_1(X0) != iProver_top
% 7.68/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_3225,plain,
% 7.68/1.48      ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) = k1_relat_1(k5_xboole_0(sK1,k4_xboole_0(X0,sK1)))
% 7.68/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_621,c_625]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_3839,plain,
% 7.68/1.48      ( k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) = k1_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_620,c_3225]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_11,plain,
% 7.68/1.48      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 7.68/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_628,plain,
% 7.68/1.48      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1244,plain,
% 7.68/1.48      ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1238,c_628]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1245,plain,
% 7.68/1.48      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_1244,c_14]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_5,plain,
% 7.68/1.48      ( r1_tarski(X0,X1)
% 7.68/1.48      | ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 7.68/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_631,plain,
% 7.68/1.48      ( r1_tarski(X0,X1) = iProver_top
% 7.68/1.48      | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) != iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1571,plain,
% 7.68/1.48      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1))) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1245,c_631]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1592,plain,
% 7.68/1.48      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X0)),X1))) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1238,c_1571]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1596,plain,
% 7.68/1.48      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) = iProver_top ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_1592,c_14]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1719,plain,
% 7.68/1.48      ( r1_tarski(X0,k3_tarski(k2_enumset1(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1)),X2))) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1238,c_1596]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1728,plain,
% 7.68/1.48      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X0,X1))))) = iProver_top ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_1719,c_14]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_3850,plain,
% 7.68/1.48      ( r1_tarski(k1_relat_1(sK0),k5_xboole_0(k1_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(X0,k1_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_3839,c_1728]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_19,negated_conjecture,
% 7.68/1.48      ( r1_tarski(sK0,sK1) ),
% 7.68/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_622,plain,
% 7.68/1.48      ( r1_tarski(sK0,sK1) = iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_6,plain,
% 7.68/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.68/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_630,plain,
% 7.68/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.68/1.48      | r1_tarski(X1,X2) != iProver_top
% 7.68/1.48      | r1_tarski(X0,X2) = iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_3234,plain,
% 7.68/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.68/1.48      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_629,c_630]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1166,plain,
% 7.68/1.48      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_629,c_619]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_10163,plain,
% 7.68/1.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X1))) = k1_xboole_0
% 7.68/1.48      | r1_tarski(k4_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),X1) != iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1166,c_1739]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_10166,plain,
% 7.68/1.48      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.68/1.48      | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_10163,c_8,c_1166]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_20199,plain,
% 7.68/1.48      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.68/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_3234,c_10166]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_20612,plain,
% 7.68/1.48      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_622,c_20199]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_21908,plain,
% 7.68/1.48      ( r1_tarski(k1_relat_1(sK0),k5_xboole_0(k1_relat_1(k5_xboole_0(sK1,k1_xboole_0)),k4_xboole_0(X0,k1_relat_1(k5_xboole_0(sK1,k1_xboole_0))))) = iProver_top ),
% 7.68/1.48      inference(light_normalisation,[status(thm)],[c_3850,c_20612]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_21909,plain,
% 7.68/1.48      ( r1_tarski(k1_relat_1(sK0),k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(X0,k1_relat_1(sK1)))) = iProver_top ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_21908,c_8]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_21918,plain,
% 7.68/1.48      ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_14521,c_21909]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_17,plain,
% 7.68/1.48      ( ~ v1_relat_1(X0)
% 7.68/1.48      | ~ v1_relat_1(X1)
% 7.68/1.48      | k5_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X0))) = k2_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 7.68/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_624,plain,
% 7.68/1.48      ( k5_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X0))) = k2_relat_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)))
% 7.68/1.48      | v1_relat_1(X0) != iProver_top
% 7.68/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1866,plain,
% 7.68/1.48      ( k5_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(X0),k2_relat_1(sK0))) = k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(X0,sK0)))
% 7.68/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_620,c_624]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_2842,plain,
% 7.68/1.48      ( k5_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_621,c_1866]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1725,plain,
% 7.68/1.48      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X2)),X1))) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1596,c_631]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_7467,plain,
% 7.68/1.48      ( r1_tarski(k2_relat_1(sK0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),X1)),X0))) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_2842,c_1725]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1865,plain,
% 7.68/1.48      ( k5_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(X0),k2_relat_1(sK1))) = k2_relat_1(k5_xboole_0(sK1,k4_xboole_0(X0,sK1)))
% 7.68/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_621,c_624]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_2675,plain,
% 7.68/1.48      ( k5_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) = k2_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_620,c_1865]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_2814,plain,
% 7.68/1.48      ( k5_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_2675,c_1243]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_8781,plain,
% 7.68/1.48      ( k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k2_relat_1(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
% 7.68/1.48      inference(light_normalisation,[status(thm)],[c_2814,c_2842]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_20717,plain,
% 7.68/1.48      ( k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k2_relat_1(k5_xboole_0(sK1,k1_xboole_0)) ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_20612,c_8781]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_20718,plain,
% 7.68/1.48      ( k2_relat_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k2_relat_1(sK1) ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_20717,c_8]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_21253,plain,
% 7.68/1.48      ( r1_tarski(k2_relat_1(sK0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k2_relat_1(sK1),X1)),X0))) = iProver_top ),
% 7.68/1.48      inference(light_normalisation,[status(thm)],[c_7467,c_20718]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_21267,plain,
% 7.68/1.48      ( r1_tarski(k2_relat_1(sK0),k5_xboole_0(X0,k4_xboole_0(k3_relat_1(sK1),X0))) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1978,c_21253]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_21497,plain,
% 7.68/1.48      ( r1_tarski(k2_relat_1(sK0),k5_xboole_0(k3_relat_1(sK1),k1_xboole_0)) = iProver_top ),
% 7.68/1.48      inference(superposition,[status(thm)],[c_1166,c_21267]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_21505,plain,
% 7.68/1.48      ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 7.68/1.48      inference(demodulation,[status(thm)],[c_21497,c_8]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_12,plain,
% 7.68/1.48      ( ~ r1_tarski(X0,X1)
% 7.68/1.48      | ~ r1_tarski(X2,X1)
% 7.68/1.48      | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 7.68/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_4384,plain,
% 7.68/1.48      ( r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),X0)
% 7.68/1.48      | ~ r1_tarski(k2_relat_1(sK0),X0)
% 7.68/1.48      | ~ r1_tarski(k1_relat_1(sK0),X0) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_16265,plain,
% 7.68/1.48      ( r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1))
% 7.68/1.48      | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
% 7.68/1.48      | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_4384]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_16270,plain,
% 7.68/1.48      ( r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1)) = iProver_top
% 7.68/1.48      | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) != iProver_top
% 7.68/1.48      | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_16265]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_357,plain,
% 7.68/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.68/1.48      theory(equality) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_665,plain,
% 7.68/1.48      ( ~ r1_tarski(X0,X1)
% 7.68/1.48      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 7.68/1.48      | k3_relat_1(sK1) != X1
% 7.68/1.48      | k3_relat_1(sK0) != X0 ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_357]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_724,plain,
% 7.68/1.48      ( ~ r1_tarski(X0,k3_relat_1(X1))
% 7.68/1.48      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 7.68/1.48      | k3_relat_1(sK1) != k3_relat_1(X1)
% 7.68/1.48      | k3_relat_1(sK0) != X0 ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_665]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_2454,plain,
% 7.68/1.48      ( ~ r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(X0))
% 7.68/1.48      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 7.68/1.48      | k3_relat_1(sK1) != k3_relat_1(X0)
% 7.68/1.48      | k3_relat_1(sK0) != k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_724]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_3720,plain,
% 7.68/1.48      ( ~ r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1))
% 7.68/1.48      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 7.68/1.48      | k3_relat_1(sK1) != k3_relat_1(sK1)
% 7.68/1.48      | k3_relat_1(sK0) != k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_2454]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_3721,plain,
% 7.68/1.48      ( k3_relat_1(sK1) != k3_relat_1(sK1)
% 7.68/1.48      | k3_relat_1(sK0) != k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)))
% 7.68/1.48      | r1_tarski(k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1)) != iProver_top
% 7.68/1.48      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_3720]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_356,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_826,plain,
% 7.68/1.48      ( X0 != X1 | k3_relat_1(sK0) != X1 | k3_relat_1(sK0) = X0 ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_356]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1061,plain,
% 7.68/1.48      ( X0 != k3_relat_1(sK0)
% 7.68/1.48      | k3_relat_1(sK0) = X0
% 7.68/1.48      | k3_relat_1(sK0) != k3_relat_1(sK0) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_826]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1288,plain,
% 7.68/1.48      ( k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))) != k3_relat_1(sK0)
% 7.68/1.48      | k3_relat_1(sK0) = k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)))
% 7.68/1.48      | k3_relat_1(sK0) != k3_relat_1(sK0) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_1061]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_355,plain,( X0 = X0 ),theory(equality) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_773,plain,
% 7.68/1.48      ( k3_relat_1(sK1) = k3_relat_1(sK1) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_355]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_363,plain,
% 7.68/1.48      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 7.68/1.48      theory(equality) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_371,plain,
% 7.68/1.48      ( k3_relat_1(sK0) = k3_relat_1(sK0) | sK0 != sK0 ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_363]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_1,plain,
% 7.68/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.68/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_63,plain,
% 7.68/1.48      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_3,plain,
% 7.68/1.48      ( r1_tarski(X0,X0) ),
% 7.68/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_59,plain,
% 7.68/1.48      ( r1_tarski(sK0,sK0) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_33,plain,
% 7.68/1.48      ( ~ v1_relat_1(sK0)
% 7.68/1.48      | k5_xboole_0(k1_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))) = k3_relat_1(sK0) ),
% 7.68/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_18,negated_conjecture,
% 7.68/1.48      ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
% 7.68/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(c_25,plain,
% 7.68/1.48      ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
% 7.68/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.68/1.48  
% 7.68/1.48  cnf(contradiction,plain,
% 7.68/1.48      ( $false ),
% 7.68/1.48      inference(minisat,
% 7.68/1.48                [status(thm)],
% 7.68/1.48                [c_21918,c_21505,c_16270,c_3721,c_1288,c_773,c_371,c_63,
% 7.68/1.48                 c_59,c_33,c_25,c_21]) ).
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.68/1.48  
% 7.68/1.48  ------                               Statistics
% 7.68/1.48  
% 7.68/1.48  ------ General
% 7.68/1.48  
% 7.68/1.48  abstr_ref_over_cycles:                  0
% 7.68/1.48  abstr_ref_under_cycles:                 0
% 7.68/1.48  gc_basic_clause_elim:                   0
% 7.68/1.48  forced_gc_time:                         0
% 7.68/1.48  parsing_time:                           0.008
% 7.68/1.48  unif_index_cands_time:                  0.
% 7.68/1.48  unif_index_add_time:                    0.
% 7.68/1.48  orderings_time:                         0.
% 7.68/1.48  out_proof_time:                         0.011
% 7.68/1.48  total_time:                             0.644
% 7.68/1.48  num_of_symbols:                         45
% 7.68/1.48  num_of_terms:                           21816
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing
% 7.68/1.48  
% 7.68/1.48  num_of_splits:                          0
% 7.68/1.48  num_of_split_atoms:                     0
% 7.68/1.48  num_of_reused_defs:                     0
% 7.68/1.48  num_eq_ax_congr_red:                    14
% 7.68/1.48  num_of_sem_filtered_clauses:            1
% 7.68/1.48  num_of_subtypes:                        0
% 7.68/1.48  monotx_restored_types:                  0
% 7.68/1.48  sat_num_of_epr_types:                   0
% 7.68/1.48  sat_num_of_non_cyclic_types:            0
% 7.68/1.48  sat_guarded_non_collapsed_types:        0
% 7.68/1.48  num_pure_diseq_elim:                    0
% 7.68/1.48  simp_replaced_by:                       0
% 7.68/1.48  res_preprocessed:                       99
% 7.68/1.48  prep_upred:                             0
% 7.68/1.48  prep_unflattend:                        3
% 7.68/1.48  smt_new_axioms:                         0
% 7.68/1.48  pred_elim_cands:                        2
% 7.68/1.48  pred_elim:                              2
% 7.68/1.48  pred_elim_cl:                           2
% 7.68/1.48  pred_elim_cycles:                       4
% 7.68/1.48  merged_defs:                            0
% 7.68/1.48  merged_defs_ncl:                        0
% 7.68/1.48  bin_hyper_res:                          0
% 7.68/1.48  prep_cycles:                            4
% 7.68/1.48  pred_elim_time:                         0.001
% 7.68/1.48  splitting_time:                         0.
% 7.68/1.48  sem_filter_time:                        0.
% 7.68/1.48  monotx_time:                            0.
% 7.68/1.48  subtype_inf_time:                       0.
% 7.68/1.48  
% 7.68/1.48  ------ Problem properties
% 7.68/1.48  
% 7.68/1.48  clauses:                                19
% 7.68/1.48  conjectures:                            4
% 7.68/1.48  epr:                                    6
% 7.68/1.48  horn:                                   19
% 7.68/1.48  ground:                                 4
% 7.68/1.48  unary:                                  10
% 7.68/1.48  binary:                                 4
% 7.68/1.48  lits:                                   33
% 7.68/1.48  lits_eq:                                8
% 7.68/1.48  fd_pure:                                0
% 7.68/1.48  fd_pseudo:                              0
% 7.68/1.48  fd_cond:                                0
% 7.68/1.48  fd_pseudo_cond:                         1
% 7.68/1.48  ac_symbols:                             0
% 7.68/1.48  
% 7.68/1.48  ------ Propositional Solver
% 7.68/1.48  
% 7.68/1.48  prop_solver_calls:                      35
% 7.68/1.48  prop_fast_solver_calls:                 635
% 7.68/1.48  smt_solver_calls:                       0
% 7.68/1.48  smt_fast_solver_calls:                  0
% 7.68/1.48  prop_num_of_clauses:                    9190
% 7.68/1.48  prop_preprocess_simplified:             17176
% 7.68/1.48  prop_fo_subsumed:                       1
% 7.68/1.48  prop_solver_time:                       0.
% 7.68/1.48  smt_solver_time:                        0.
% 7.68/1.48  smt_fast_solver_time:                   0.
% 7.68/1.48  prop_fast_solver_time:                  0.
% 7.68/1.48  prop_unsat_core_time:                   0.001
% 7.68/1.48  
% 7.68/1.48  ------ QBF
% 7.68/1.48  
% 7.68/1.48  qbf_q_res:                              0
% 7.68/1.48  qbf_num_tautologies:                    0
% 7.68/1.48  qbf_prep_cycles:                        0
% 7.68/1.48  
% 7.68/1.48  ------ BMC1
% 7.68/1.48  
% 7.68/1.48  bmc1_current_bound:                     -1
% 7.68/1.48  bmc1_last_solved_bound:                 -1
% 7.68/1.48  bmc1_unsat_core_size:                   -1
% 7.68/1.48  bmc1_unsat_core_parents_size:           -1
% 7.68/1.48  bmc1_merge_next_fun:                    0
% 7.68/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.68/1.48  
% 7.68/1.48  ------ Instantiation
% 7.68/1.48  
% 7.68/1.48  inst_num_of_clauses:                    2263
% 7.68/1.48  inst_num_in_passive:                    1006
% 7.68/1.48  inst_num_in_active:                     719
% 7.68/1.48  inst_num_in_unprocessed:                538
% 7.68/1.48  inst_num_of_loops:                      820
% 7.68/1.48  inst_num_of_learning_restarts:          0
% 7.68/1.48  inst_num_moves_active_passive:          97
% 7.68/1.48  inst_lit_activity:                      0
% 7.68/1.48  inst_lit_activity_moves:                1
% 7.68/1.48  inst_num_tautologies:                   0
% 7.68/1.48  inst_num_prop_implied:                  0
% 7.68/1.48  inst_num_existing_simplified:           0
% 7.68/1.48  inst_num_eq_res_simplified:             0
% 7.68/1.48  inst_num_child_elim:                    0
% 7.68/1.48  inst_num_of_dismatching_blockings:      1958
% 7.68/1.48  inst_num_of_non_proper_insts:           3192
% 7.68/1.48  inst_num_of_duplicates:                 0
% 7.68/1.48  inst_inst_num_from_inst_to_res:         0
% 7.68/1.48  inst_dismatching_checking_time:         0.
% 7.68/1.48  
% 7.68/1.48  ------ Resolution
% 7.68/1.48  
% 7.68/1.48  res_num_of_clauses:                     0
% 7.68/1.48  res_num_in_passive:                     0
% 7.68/1.48  res_num_in_active:                      0
% 7.68/1.48  res_num_of_loops:                       103
% 7.68/1.48  res_forward_subset_subsumed:            588
% 7.68/1.48  res_backward_subset_subsumed:           4
% 7.68/1.48  res_forward_subsumed:                   0
% 7.68/1.48  res_backward_subsumed:                  0
% 7.68/1.48  res_forward_subsumption_resolution:     0
% 7.68/1.48  res_backward_subsumption_resolution:    0
% 7.68/1.48  res_clause_to_clause_subsumption:       4245
% 7.68/1.48  res_orphan_elimination:                 0
% 7.68/1.48  res_tautology_del:                      147
% 7.68/1.48  res_num_eq_res_simplified:              0
% 7.68/1.49  res_num_sel_changes:                    0
% 7.68/1.49  res_moves_from_active_to_pass:          0
% 7.68/1.49  
% 7.68/1.49  ------ Superposition
% 7.68/1.49  
% 7.68/1.49  sup_time_total:                         0.
% 7.68/1.49  sup_time_generating:                    0.
% 7.68/1.49  sup_time_sim_full:                      0.
% 7.68/1.49  sup_time_sim_immed:                     0.
% 7.68/1.49  
% 7.68/1.49  sup_num_of_clauses:                     587
% 7.68/1.49  sup_num_in_active:                      154
% 7.68/1.49  sup_num_in_passive:                     433
% 7.68/1.49  sup_num_of_loops:                       163
% 7.68/1.49  sup_fw_superposition:                   1253
% 7.68/1.49  sup_bw_superposition:                   908
% 7.68/1.49  sup_immediate_simplified:               608
% 7.68/1.49  sup_given_eliminated:                   0
% 7.68/1.49  comparisons_done:                       0
% 7.68/1.49  comparisons_avoided:                    0
% 7.68/1.49  
% 7.68/1.49  ------ Simplifications
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  sim_fw_subset_subsumed:                 37
% 7.68/1.49  sim_bw_subset_subsumed:                 3
% 7.68/1.49  sim_fw_subsumed:                        122
% 7.68/1.49  sim_bw_subsumed:                        0
% 7.68/1.49  sim_fw_subsumption_res:                 0
% 7.68/1.49  sim_bw_subsumption_res:                 0
% 7.68/1.49  sim_tautology_del:                      48
% 7.68/1.49  sim_eq_tautology_del:                   80
% 7.68/1.49  sim_eq_res_simp:                        0
% 7.68/1.49  sim_fw_demodulated:                     413
% 7.68/1.49  sim_bw_demodulated:                     10
% 7.68/1.49  sim_light_normalised:                   125
% 7.68/1.49  sim_joinable_taut:                      0
% 7.68/1.49  sim_joinable_simp:                      0
% 7.68/1.49  sim_ac_normalised:                      0
% 7.68/1.49  sim_smt_subsumption:                    0
% 7.68/1.49  
%------------------------------------------------------------------------------
