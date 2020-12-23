%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:06 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 282 expanded)
%              Number of clauses        :   50 (  57 expanded)
%              Number of leaves         :   18 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  218 ( 501 expanded)
%              Number of equality atoms :  106 ( 267 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f45,f45,f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f30,f45,f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f23,f22])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f38,f45,f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f29,f36,f45])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f41,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_224,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1484,plain,
    ( X0 != X1
    | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) != X1
    | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) = X0 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_2493,plain,
    ( X0 != k3_tarski(X1)
    | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) = X0
    | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_5272,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) != k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))
    | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))
    | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) ),
    inference(instantiation,[status(thm)],[c_2493])).

cnf(c_38039,plain,
    ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))) != k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0)))
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))))
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_5272])).

cnf(c_667,plain,
    ( X0 != X1
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X1
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = X0 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_849,plain,
    ( X0 != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))))
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = X0
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_27510,plain,
    ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))))
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0)))
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_846,plain,
    ( X0 != X1
    | X0 = k2_relat_1(X2)
    | k2_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_1364,plain,
    ( X0 != k2_relat_1(X1)
    | X0 = k2_relat_1(X2)
    | k2_relat_1(X2) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_1856,plain,
    ( k2_relat_1(X0) != k2_relat_1(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
    | k3_tarski(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X2))) = k2_relat_1(X0)
    | k3_tarski(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X2))) != k2_relat_1(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_13438,plain,
    ( k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0)))) != k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
    | k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) != k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
    | k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0)))) ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_27503,plain,
    ( k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))))
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_13438])).

cnf(c_3,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13837,plain,
    ( k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_230,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_2499,plain,
    ( k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k2_relat_1(X2)
    | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) != X2 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_5283,plain,
    ( k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0)))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
    | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) != k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2499])).

cnf(c_13427,plain,
    ( k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))
    | k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))) != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_5283])).

cnf(c_4308,plain,
    ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))) = k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_225,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_500,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != X0
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X1 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_545,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),X0)
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != k2_relat_1(sK0)
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X0 ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_600,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != k2_relat_1(sK0)
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_3583,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))))
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != k2_relat_1(sK0)
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_5,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
    | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1405,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))))
    | ~ r1_tarski(k6_subset_1(X0,X1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2245,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))))) ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1717,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1039,plain,
    ( v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_471,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_473,plain,
    ( k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_829,plain,
    ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(X0))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_471,c_473])).

cnf(c_835,plain,
    ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_770,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_491,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_236,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_32,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38039,c_27510,c_27503,c_13837,c_13427,c_4308,c_3583,c_2245,c_1717,c_1039,c_835,c_770,c_491,c_236,c_32,c_28,c_8,c_9,c_11,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:48:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.65/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.65/1.99  
% 11.65/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/1.99  
% 11.65/1.99  ------  iProver source info
% 11.65/1.99  
% 11.65/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.65/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/1.99  git: non_committed_changes: false
% 11.65/1.99  git: last_make_outside_of_git: false
% 11.65/1.99  
% 11.65/1.99  ------ 
% 11.65/1.99  
% 11.65/1.99  ------ Input Options
% 11.65/1.99  
% 11.65/1.99  --out_options                           all
% 11.65/1.99  --tptp_safe_out                         true
% 11.65/1.99  --problem_path                          ""
% 11.65/1.99  --include_path                          ""
% 11.65/1.99  --clausifier                            res/vclausify_rel
% 11.65/1.99  --clausifier_options                    ""
% 11.65/1.99  --stdin                                 false
% 11.65/1.99  --stats_out                             all
% 11.65/1.99  
% 11.65/1.99  ------ General Options
% 11.65/1.99  
% 11.65/1.99  --fof                                   false
% 11.65/1.99  --time_out_real                         305.
% 11.65/1.99  --time_out_virtual                      -1.
% 11.65/1.99  --symbol_type_check                     false
% 11.65/1.99  --clausify_out                          false
% 11.65/1.99  --sig_cnt_out                           false
% 11.65/1.99  --trig_cnt_out                          false
% 11.65/1.99  --trig_cnt_out_tolerance                1.
% 11.65/1.99  --trig_cnt_out_sk_spl                   false
% 11.65/1.99  --abstr_cl_out                          false
% 11.65/1.99  
% 11.65/1.99  ------ Global Options
% 11.65/1.99  
% 11.65/1.99  --schedule                              default
% 11.65/1.99  --add_important_lit                     false
% 11.65/1.99  --prop_solver_per_cl                    1000
% 11.65/1.99  --min_unsat_core                        false
% 11.65/1.99  --soft_assumptions                      false
% 11.65/1.99  --soft_lemma_size                       3
% 11.65/1.99  --prop_impl_unit_size                   0
% 11.65/1.99  --prop_impl_unit                        []
% 11.65/1.99  --share_sel_clauses                     true
% 11.65/1.99  --reset_solvers                         false
% 11.65/1.99  --bc_imp_inh                            [conj_cone]
% 11.65/1.99  --conj_cone_tolerance                   3.
% 11.65/1.99  --extra_neg_conj                        none
% 11.65/1.99  --large_theory_mode                     true
% 11.65/1.99  --prolific_symb_bound                   200
% 11.65/1.99  --lt_threshold                          2000
% 11.65/1.99  --clause_weak_htbl                      true
% 11.65/1.99  --gc_record_bc_elim                     false
% 11.65/1.99  
% 11.65/1.99  ------ Preprocessing Options
% 11.65/1.99  
% 11.65/1.99  --preprocessing_flag                    true
% 11.65/1.99  --time_out_prep_mult                    0.1
% 11.65/1.99  --splitting_mode                        input
% 11.65/1.99  --splitting_grd                         true
% 11.65/1.99  --splitting_cvd                         false
% 11.65/1.99  --splitting_cvd_svl                     false
% 11.65/1.99  --splitting_nvd                         32
% 11.65/1.99  --sub_typing                            true
% 11.65/1.99  --prep_gs_sim                           true
% 11.65/1.99  --prep_unflatten                        true
% 11.65/1.99  --prep_res_sim                          true
% 11.65/1.99  --prep_upred                            true
% 11.65/1.99  --prep_sem_filter                       exhaustive
% 11.65/1.99  --prep_sem_filter_out                   false
% 11.65/1.99  --pred_elim                             true
% 11.65/1.99  --res_sim_input                         true
% 11.65/1.99  --eq_ax_congr_red                       true
% 11.65/1.99  --pure_diseq_elim                       true
% 11.65/1.99  --brand_transform                       false
% 11.65/1.99  --non_eq_to_eq                          false
% 11.65/1.99  --prep_def_merge                        true
% 11.65/1.99  --prep_def_merge_prop_impl              false
% 11.65/1.99  --prep_def_merge_mbd                    true
% 11.65/1.99  --prep_def_merge_tr_red                 false
% 11.65/1.99  --prep_def_merge_tr_cl                  false
% 11.65/1.99  --smt_preprocessing                     true
% 11.65/1.99  --smt_ac_axioms                         fast
% 11.65/1.99  --preprocessed_out                      false
% 11.65/1.99  --preprocessed_stats                    false
% 11.65/1.99  
% 11.65/1.99  ------ Abstraction refinement Options
% 11.65/1.99  
% 11.65/1.99  --abstr_ref                             []
% 11.65/1.99  --abstr_ref_prep                        false
% 11.65/1.99  --abstr_ref_until_sat                   false
% 11.65/1.99  --abstr_ref_sig_restrict                funpre
% 11.65/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/1.99  --abstr_ref_under                       []
% 11.65/1.99  
% 11.65/1.99  ------ SAT Options
% 11.65/1.99  
% 11.65/1.99  --sat_mode                              false
% 11.65/1.99  --sat_fm_restart_options                ""
% 11.65/1.99  --sat_gr_def                            false
% 11.65/1.99  --sat_epr_types                         true
% 11.65/1.99  --sat_non_cyclic_types                  false
% 11.65/1.99  --sat_finite_models                     false
% 11.65/1.99  --sat_fm_lemmas                         false
% 11.65/1.99  --sat_fm_prep                           false
% 11.65/1.99  --sat_fm_uc_incr                        true
% 11.65/1.99  --sat_out_model                         small
% 11.65/1.99  --sat_out_clauses                       false
% 11.65/1.99  
% 11.65/1.99  ------ QBF Options
% 11.65/1.99  
% 11.65/1.99  --qbf_mode                              false
% 11.65/1.99  --qbf_elim_univ                         false
% 11.65/1.99  --qbf_dom_inst                          none
% 11.65/1.99  --qbf_dom_pre_inst                      false
% 11.65/1.99  --qbf_sk_in                             false
% 11.65/1.99  --qbf_pred_elim                         true
% 11.65/1.99  --qbf_split                             512
% 11.65/1.99  
% 11.65/1.99  ------ BMC1 Options
% 11.65/1.99  
% 11.65/1.99  --bmc1_incremental                      false
% 11.65/1.99  --bmc1_axioms                           reachable_all
% 11.65/1.99  --bmc1_min_bound                        0
% 11.65/1.99  --bmc1_max_bound                        -1
% 11.65/1.99  --bmc1_max_bound_default                -1
% 11.65/1.99  --bmc1_symbol_reachability              true
% 11.65/1.99  --bmc1_property_lemmas                  false
% 11.65/1.99  --bmc1_k_induction                      false
% 11.65/1.99  --bmc1_non_equiv_states                 false
% 11.65/1.99  --bmc1_deadlock                         false
% 11.65/1.99  --bmc1_ucm                              false
% 11.65/1.99  --bmc1_add_unsat_core                   none
% 11.65/1.99  --bmc1_unsat_core_children              false
% 11.65/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/1.99  --bmc1_out_stat                         full
% 11.65/1.99  --bmc1_ground_init                      false
% 11.65/1.99  --bmc1_pre_inst_next_state              false
% 11.65/1.99  --bmc1_pre_inst_state                   false
% 11.65/1.99  --bmc1_pre_inst_reach_state             false
% 11.65/1.99  --bmc1_out_unsat_core                   false
% 11.65/1.99  --bmc1_aig_witness_out                  false
% 11.65/1.99  --bmc1_verbose                          false
% 11.65/1.99  --bmc1_dump_clauses_tptp                false
% 11.65/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.65/1.99  --bmc1_dump_file                        -
% 11.65/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.65/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.65/1.99  --bmc1_ucm_extend_mode                  1
% 11.65/1.99  --bmc1_ucm_init_mode                    2
% 11.65/1.99  --bmc1_ucm_cone_mode                    none
% 11.65/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.65/1.99  --bmc1_ucm_relax_model                  4
% 11.65/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.65/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/1.99  --bmc1_ucm_layered_model                none
% 11.65/1.99  --bmc1_ucm_max_lemma_size               10
% 11.65/1.99  
% 11.65/1.99  ------ AIG Options
% 11.65/1.99  
% 11.65/1.99  --aig_mode                              false
% 11.65/1.99  
% 11.65/1.99  ------ Instantiation Options
% 11.65/1.99  
% 11.65/1.99  --instantiation_flag                    true
% 11.65/1.99  --inst_sos_flag                         true
% 11.65/1.99  --inst_sos_phase                        true
% 11.65/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/1.99  --inst_lit_sel_side                     num_symb
% 11.65/1.99  --inst_solver_per_active                1400
% 11.65/1.99  --inst_solver_calls_frac                1.
% 11.65/1.99  --inst_passive_queue_type               priority_queues
% 11.65/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/1.99  --inst_passive_queues_freq              [25;2]
% 11.65/1.99  --inst_dismatching                      true
% 11.65/1.99  --inst_eager_unprocessed_to_passive     true
% 11.65/1.99  --inst_prop_sim_given                   true
% 11.65/1.99  --inst_prop_sim_new                     false
% 11.65/1.99  --inst_subs_new                         false
% 11.65/1.99  --inst_eq_res_simp                      false
% 11.65/1.99  --inst_subs_given                       false
% 11.65/1.99  --inst_orphan_elimination               true
% 11.65/1.99  --inst_learning_loop_flag               true
% 11.65/1.99  --inst_learning_start                   3000
% 11.65/1.99  --inst_learning_factor                  2
% 11.65/1.99  --inst_start_prop_sim_after_learn       3
% 11.65/1.99  --inst_sel_renew                        solver
% 11.65/1.99  --inst_lit_activity_flag                true
% 11.65/1.99  --inst_restr_to_given                   false
% 11.65/1.99  --inst_activity_threshold               500
% 11.65/1.99  --inst_out_proof                        true
% 11.65/1.99  
% 11.65/1.99  ------ Resolution Options
% 11.65/1.99  
% 11.65/1.99  --resolution_flag                       true
% 11.65/1.99  --res_lit_sel                           adaptive
% 11.65/1.99  --res_lit_sel_side                      none
% 11.65/1.99  --res_ordering                          kbo
% 11.65/1.99  --res_to_prop_solver                    active
% 11.65/1.99  --res_prop_simpl_new                    false
% 11.65/1.99  --res_prop_simpl_given                  true
% 11.65/1.99  --res_passive_queue_type                priority_queues
% 11.65/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/1.99  --res_passive_queues_freq               [15;5]
% 11.65/1.99  --res_forward_subs                      full
% 11.65/1.99  --res_backward_subs                     full
% 11.65/1.99  --res_forward_subs_resolution           true
% 11.65/1.99  --res_backward_subs_resolution          true
% 11.65/1.99  --res_orphan_elimination                true
% 11.65/1.99  --res_time_limit                        2.
% 11.65/1.99  --res_out_proof                         true
% 11.65/1.99  
% 11.65/1.99  ------ Superposition Options
% 11.65/1.99  
% 11.65/1.99  --superposition_flag                    true
% 11.65/1.99  --sup_passive_queue_type                priority_queues
% 11.65/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.65/1.99  --demod_completeness_check              fast
% 11.65/1.99  --demod_use_ground                      true
% 11.65/1.99  --sup_to_prop_solver                    passive
% 11.65/1.99  --sup_prop_simpl_new                    true
% 11.65/1.99  --sup_prop_simpl_given                  true
% 11.65/1.99  --sup_fun_splitting                     true
% 11.65/1.99  --sup_smt_interval                      50000
% 11.65/1.99  
% 11.65/1.99  ------ Superposition Simplification Setup
% 11.65/1.99  
% 11.65/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/1.99  --sup_immed_triv                        [TrivRules]
% 11.65/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.99  --sup_immed_bw_main                     []
% 11.65/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.99  --sup_input_bw                          []
% 11.65/1.99  
% 11.65/1.99  ------ Combination Options
% 11.65/1.99  
% 11.65/1.99  --comb_res_mult                         3
% 11.65/1.99  --comb_sup_mult                         2
% 11.65/1.99  --comb_inst_mult                        10
% 11.65/1.99  
% 11.65/1.99  ------ Debug Options
% 11.65/1.99  
% 11.65/1.99  --dbg_backtrace                         false
% 11.65/1.99  --dbg_dump_prop_clauses                 false
% 11.65/1.99  --dbg_dump_prop_clauses_file            -
% 11.65/1.99  --dbg_out_stat                          false
% 11.65/1.99  ------ Parsing...
% 11.65/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/1.99  
% 11.65/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.65/1.99  
% 11.65/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/1.99  
% 11.65/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/1.99  ------ Proving...
% 11.65/1.99  ------ Problem Properties 
% 11.65/1.99  
% 11.65/1.99  
% 11.65/1.99  clauses                                 10
% 11.65/1.99  conjectures                             3
% 11.65/1.99  EPR                                     4
% 11.65/1.99  Horn                                    10
% 11.65/1.99  unary                                   5
% 11.65/1.99  binary                                  3
% 11.65/1.99  lits                                    17
% 11.65/1.99  lits eq                                 3
% 11.65/1.99  fd_pure                                 0
% 11.65/1.99  fd_pseudo                               0
% 11.65/1.99  fd_cond                                 0
% 11.65/1.99  fd_pseudo_cond                          1
% 11.65/1.99  AC symbols                              0
% 11.65/1.99  
% 11.65/1.99  ------ Schedule dynamic 5 is on 
% 11.65/1.99  
% 11.65/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.65/1.99  
% 11.65/1.99  
% 11.65/1.99  ------ 
% 11.65/1.99  Current options:
% 11.65/1.99  ------ 
% 11.65/1.99  
% 11.65/1.99  ------ Input Options
% 11.65/1.99  
% 11.65/1.99  --out_options                           all
% 11.65/1.99  --tptp_safe_out                         true
% 11.65/1.99  --problem_path                          ""
% 11.65/1.99  --include_path                          ""
% 11.65/1.99  --clausifier                            res/vclausify_rel
% 11.65/1.99  --clausifier_options                    ""
% 11.65/1.99  --stdin                                 false
% 11.65/1.99  --stats_out                             all
% 11.65/1.99  
% 11.65/1.99  ------ General Options
% 11.65/1.99  
% 11.65/1.99  --fof                                   false
% 11.65/1.99  --time_out_real                         305.
% 11.65/1.99  --time_out_virtual                      -1.
% 11.65/1.99  --symbol_type_check                     false
% 11.65/1.99  --clausify_out                          false
% 11.65/1.99  --sig_cnt_out                           false
% 11.65/1.99  --trig_cnt_out                          false
% 11.65/1.99  --trig_cnt_out_tolerance                1.
% 11.65/1.99  --trig_cnt_out_sk_spl                   false
% 11.65/1.99  --abstr_cl_out                          false
% 11.65/1.99  
% 11.65/1.99  ------ Global Options
% 11.65/1.99  
% 11.65/1.99  --schedule                              default
% 11.65/1.99  --add_important_lit                     false
% 11.65/1.99  --prop_solver_per_cl                    1000
% 11.65/1.99  --min_unsat_core                        false
% 11.65/1.99  --soft_assumptions                      false
% 11.65/1.99  --soft_lemma_size                       3
% 11.65/1.99  --prop_impl_unit_size                   0
% 11.65/1.99  --prop_impl_unit                        []
% 11.65/1.99  --share_sel_clauses                     true
% 11.65/1.99  --reset_solvers                         false
% 11.65/1.99  --bc_imp_inh                            [conj_cone]
% 11.65/1.99  --conj_cone_tolerance                   3.
% 11.65/1.99  --extra_neg_conj                        none
% 11.65/1.99  --large_theory_mode                     true
% 11.65/1.99  --prolific_symb_bound                   200
% 11.65/1.99  --lt_threshold                          2000
% 11.65/1.99  --clause_weak_htbl                      true
% 11.65/1.99  --gc_record_bc_elim                     false
% 11.65/1.99  
% 11.65/1.99  ------ Preprocessing Options
% 11.65/1.99  
% 11.65/1.99  --preprocessing_flag                    true
% 11.65/1.99  --time_out_prep_mult                    0.1
% 11.65/1.99  --splitting_mode                        input
% 11.65/1.99  --splitting_grd                         true
% 11.65/1.99  --splitting_cvd                         false
% 11.65/1.99  --splitting_cvd_svl                     false
% 11.65/1.99  --splitting_nvd                         32
% 11.65/1.99  --sub_typing                            true
% 11.65/1.99  --prep_gs_sim                           true
% 11.65/1.99  --prep_unflatten                        true
% 11.65/1.99  --prep_res_sim                          true
% 11.65/1.99  --prep_upred                            true
% 11.65/1.99  --prep_sem_filter                       exhaustive
% 11.65/1.99  --prep_sem_filter_out                   false
% 11.65/1.99  --pred_elim                             true
% 11.65/1.99  --res_sim_input                         true
% 11.65/1.99  --eq_ax_congr_red                       true
% 11.65/1.99  --pure_diseq_elim                       true
% 11.65/1.99  --brand_transform                       false
% 11.65/1.99  --non_eq_to_eq                          false
% 11.65/1.99  --prep_def_merge                        true
% 11.65/1.99  --prep_def_merge_prop_impl              false
% 11.65/1.99  --prep_def_merge_mbd                    true
% 11.65/1.99  --prep_def_merge_tr_red                 false
% 11.65/1.99  --prep_def_merge_tr_cl                  false
% 11.65/1.99  --smt_preprocessing                     true
% 11.65/1.99  --smt_ac_axioms                         fast
% 11.65/1.99  --preprocessed_out                      false
% 11.65/1.99  --preprocessed_stats                    false
% 11.65/1.99  
% 11.65/1.99  ------ Abstraction refinement Options
% 11.65/1.99  
% 11.65/1.99  --abstr_ref                             []
% 11.65/1.99  --abstr_ref_prep                        false
% 11.65/1.99  --abstr_ref_until_sat                   false
% 11.65/1.99  --abstr_ref_sig_restrict                funpre
% 11.65/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/1.99  --abstr_ref_under                       []
% 11.65/1.99  
% 11.65/1.99  ------ SAT Options
% 11.65/1.99  
% 11.65/1.99  --sat_mode                              false
% 11.65/1.99  --sat_fm_restart_options                ""
% 11.65/1.99  --sat_gr_def                            false
% 11.65/1.99  --sat_epr_types                         true
% 11.65/1.99  --sat_non_cyclic_types                  false
% 11.65/1.99  --sat_finite_models                     false
% 11.65/1.99  --sat_fm_lemmas                         false
% 11.65/1.99  --sat_fm_prep                           false
% 11.65/1.99  --sat_fm_uc_incr                        true
% 11.65/1.99  --sat_out_model                         small
% 11.65/1.99  --sat_out_clauses                       false
% 11.65/1.99  
% 11.65/1.99  ------ QBF Options
% 11.65/1.99  
% 11.65/1.99  --qbf_mode                              false
% 11.65/1.99  --qbf_elim_univ                         false
% 11.65/1.99  --qbf_dom_inst                          none
% 11.65/1.99  --qbf_dom_pre_inst                      false
% 11.65/1.99  --qbf_sk_in                             false
% 11.65/1.99  --qbf_pred_elim                         true
% 11.65/1.99  --qbf_split                             512
% 11.65/1.99  
% 11.65/1.99  ------ BMC1 Options
% 11.65/1.99  
% 11.65/1.99  --bmc1_incremental                      false
% 11.65/1.99  --bmc1_axioms                           reachable_all
% 11.65/1.99  --bmc1_min_bound                        0
% 11.65/1.99  --bmc1_max_bound                        -1
% 11.65/1.99  --bmc1_max_bound_default                -1
% 11.65/1.99  --bmc1_symbol_reachability              true
% 11.65/1.99  --bmc1_property_lemmas                  false
% 11.65/1.99  --bmc1_k_induction                      false
% 11.65/1.99  --bmc1_non_equiv_states                 false
% 11.65/1.99  --bmc1_deadlock                         false
% 11.65/1.99  --bmc1_ucm                              false
% 11.65/1.99  --bmc1_add_unsat_core                   none
% 11.65/1.99  --bmc1_unsat_core_children              false
% 11.65/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/1.99  --bmc1_out_stat                         full
% 11.65/1.99  --bmc1_ground_init                      false
% 11.65/1.99  --bmc1_pre_inst_next_state              false
% 11.65/1.99  --bmc1_pre_inst_state                   false
% 11.65/1.99  --bmc1_pre_inst_reach_state             false
% 11.65/1.99  --bmc1_out_unsat_core                   false
% 11.65/1.99  --bmc1_aig_witness_out                  false
% 11.65/1.99  --bmc1_verbose                          false
% 11.65/1.99  --bmc1_dump_clauses_tptp                false
% 11.65/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.65/1.99  --bmc1_dump_file                        -
% 11.65/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.65/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.65/1.99  --bmc1_ucm_extend_mode                  1
% 11.65/1.99  --bmc1_ucm_init_mode                    2
% 11.65/1.99  --bmc1_ucm_cone_mode                    none
% 11.65/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.65/1.99  --bmc1_ucm_relax_model                  4
% 11.65/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.65/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/1.99  --bmc1_ucm_layered_model                none
% 11.65/1.99  --bmc1_ucm_max_lemma_size               10
% 11.65/1.99  
% 11.65/1.99  ------ AIG Options
% 11.65/1.99  
% 11.65/1.99  --aig_mode                              false
% 11.65/1.99  
% 11.65/1.99  ------ Instantiation Options
% 11.65/1.99  
% 11.65/1.99  --instantiation_flag                    true
% 11.65/1.99  --inst_sos_flag                         true
% 11.65/1.99  --inst_sos_phase                        true
% 11.65/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/1.99  --inst_lit_sel_side                     none
% 11.65/1.99  --inst_solver_per_active                1400
% 11.65/1.99  --inst_solver_calls_frac                1.
% 11.65/1.99  --inst_passive_queue_type               priority_queues
% 11.65/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/1.99  --inst_passive_queues_freq              [25;2]
% 11.65/1.99  --inst_dismatching                      true
% 11.65/1.99  --inst_eager_unprocessed_to_passive     true
% 11.65/1.99  --inst_prop_sim_given                   true
% 11.65/1.99  --inst_prop_sim_new                     false
% 11.65/1.99  --inst_subs_new                         false
% 11.65/1.99  --inst_eq_res_simp                      false
% 11.65/1.99  --inst_subs_given                       false
% 11.65/1.99  --inst_orphan_elimination               true
% 11.65/1.99  --inst_learning_loop_flag               true
% 11.65/1.99  --inst_learning_start                   3000
% 11.65/1.99  --inst_learning_factor                  2
% 11.65/1.99  --inst_start_prop_sim_after_learn       3
% 11.65/1.99  --inst_sel_renew                        solver
% 11.65/1.99  --inst_lit_activity_flag                true
% 11.65/1.99  --inst_restr_to_given                   false
% 11.65/1.99  --inst_activity_threshold               500
% 11.65/1.99  --inst_out_proof                        true
% 11.65/1.99  
% 11.65/1.99  ------ Resolution Options
% 11.65/1.99  
% 11.65/1.99  --resolution_flag                       false
% 11.65/1.99  --res_lit_sel                           adaptive
% 11.65/1.99  --res_lit_sel_side                      none
% 11.65/1.99  --res_ordering                          kbo
% 11.65/1.99  --res_to_prop_solver                    active
% 11.65/1.99  --res_prop_simpl_new                    false
% 11.65/1.99  --res_prop_simpl_given                  true
% 11.65/1.99  --res_passive_queue_type                priority_queues
% 11.65/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/1.99  --res_passive_queues_freq               [15;5]
% 11.65/1.99  --res_forward_subs                      full
% 11.65/1.99  --res_backward_subs                     full
% 11.65/1.99  --res_forward_subs_resolution           true
% 11.65/1.99  --res_backward_subs_resolution          true
% 11.65/1.99  --res_orphan_elimination                true
% 11.65/1.99  --res_time_limit                        2.
% 11.65/1.99  --res_out_proof                         true
% 11.65/1.99  
% 11.65/1.99  ------ Superposition Options
% 11.65/1.99  
% 11.65/1.99  --superposition_flag                    true
% 11.65/1.99  --sup_passive_queue_type                priority_queues
% 11.65/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.65/1.99  --demod_completeness_check              fast
% 11.65/1.99  --demod_use_ground                      true
% 11.65/1.99  --sup_to_prop_solver                    passive
% 11.65/1.99  --sup_prop_simpl_new                    true
% 11.65/1.99  --sup_prop_simpl_given                  true
% 11.65/1.99  --sup_fun_splitting                     true
% 11.65/1.99  --sup_smt_interval                      50000
% 11.65/1.99  
% 11.65/1.99  ------ Superposition Simplification Setup
% 11.65/1.99  
% 11.65/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/1.99  --sup_immed_triv                        [TrivRules]
% 11.65/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.99  --sup_immed_bw_main                     []
% 11.65/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.99  --sup_input_bw                          []
% 11.65/1.99  
% 11.65/1.99  ------ Combination Options
% 11.65/1.99  
% 11.65/1.99  --comb_res_mult                         3
% 11.65/1.99  --comb_sup_mult                         2
% 11.65/1.99  --comb_inst_mult                        10
% 11.65/1.99  
% 11.65/1.99  ------ Debug Options
% 11.65/1.99  
% 11.65/1.99  --dbg_backtrace                         false
% 11.65/1.99  --dbg_dump_prop_clauses                 false
% 11.65/1.99  --dbg_dump_prop_clauses_file            -
% 11.65/1.99  --dbg_out_stat                          false
% 11.65/1.99  
% 11.65/1.99  
% 11.65/1.99  
% 11.65/1.99  
% 11.65/1.99  ------ Proving...
% 11.65/1.99  
% 11.65/1.99  
% 11.65/1.99  % SZS status Theorem for theBenchmark.p
% 11.65/1.99  
% 11.65/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/1.99  
% 11.65/1.99  fof(f2,axiom,(
% 11.65/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.65/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.99  
% 11.65/1.99  fof(f28,plain,(
% 11.65/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.65/1.99    inference(cnf_transformation,[],[f2])).
% 11.65/1.99  
% 11.65/1.99  fof(f9,axiom,(
% 11.65/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.65/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.99  
% 11.65/1.99  fof(f35,plain,(
% 11.65/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.65/1.99    inference(cnf_transformation,[],[f9])).
% 11.65/1.99  
% 11.65/1.99  fof(f5,axiom,(
% 11.65/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.65/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.99  
% 11.65/1.99  fof(f31,plain,(
% 11.65/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.65/1.99    inference(cnf_transformation,[],[f5])).
% 11.65/1.99  
% 11.65/1.99  fof(f6,axiom,(
% 11.65/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.65/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.99  
% 11.65/1.99  fof(f32,plain,(
% 11.65/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.65/1.99    inference(cnf_transformation,[],[f6])).
% 11.65/1.99  
% 11.65/1.99  fof(f7,axiom,(
% 11.65/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.65/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.99  
% 11.65/1.99  fof(f33,plain,(
% 11.65/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.65/1.99    inference(cnf_transformation,[],[f7])).
% 11.65/1.99  
% 11.65/1.99  fof(f8,axiom,(
% 11.65/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.65/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.99  
% 11.65/1.99  fof(f34,plain,(
% 11.65/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.65/1.99    inference(cnf_transformation,[],[f8])).
% 11.65/1.99  
% 11.65/1.99  fof(f42,plain,(
% 11.65/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 11.65/1.99    inference(definition_unfolding,[],[f33,f34])).
% 11.65/1.99  
% 11.65/1.99  fof(f43,plain,(
% 11.65/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 11.65/1.99    inference(definition_unfolding,[],[f32,f42])).
% 11.65/1.99  
% 11.65/1.99  fof(f44,plain,(
% 11.65/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 11.65/1.99    inference(definition_unfolding,[],[f31,f43])).
% 11.65/1.99  
% 11.65/1.99  fof(f45,plain,(
% 11.65/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 11.65/1.99    inference(definition_unfolding,[],[f35,f44])).
% 11.65/1.99  
% 11.65/1.99  fof(f10,axiom,(
% 11.65/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f36,plain,(
% 11.65/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f10])).
% 11.65/2.00  
% 11.65/2.00  fof(f46,plain,(
% 11.65/2.00    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0)))) )),
% 11.65/2.00    inference(definition_unfolding,[],[f28,f45,f45,f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f4,axiom,(
% 11.65/2.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f16,plain,(
% 11.65/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.65/2.00    inference(ennf_transformation,[],[f4])).
% 11.65/2.00  
% 11.65/2.00  fof(f30,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f16])).
% 11.65/2.00  
% 11.65/2.00  fof(f48,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 11.65/2.00    inference(definition_unfolding,[],[f30,f45,f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f1,axiom,(
% 11.65/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f20,plain,(
% 11.65/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.00    inference(nnf_transformation,[],[f1])).
% 11.65/2.00  
% 11.65/2.00  fof(f21,plain,(
% 11.65/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.00    inference(flattening,[],[f20])).
% 11.65/2.00  
% 11.65/2.00  fof(f26,plain,(
% 11.65/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.65/2.00    inference(cnf_transformation,[],[f21])).
% 11.65/2.00  
% 11.65/2.00  fof(f51,plain,(
% 11.65/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.65/2.00    inference(equality_resolution,[],[f26])).
% 11.65/2.00  
% 11.65/2.00  fof(f11,axiom,(
% 11.65/2.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f17,plain,(
% 11.65/2.00    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 11.65/2.00    inference(ennf_transformation,[],[f11])).
% 11.65/2.00  
% 11.65/2.00  fof(f37,plain,(
% 11.65/2.00    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f17])).
% 11.65/2.00  
% 11.65/2.00  fof(f49,plain,(
% 11.65/2.00    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.65/2.00    inference(definition_unfolding,[],[f37,f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f13,conjecture,(
% 11.65/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f14,negated_conjecture,(
% 11.65/2.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 11.65/2.00    inference(negated_conjecture,[],[f13])).
% 11.65/2.00  
% 11.65/2.00  fof(f19,plain,(
% 11.65/2.00    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 11.65/2.00    inference(ennf_transformation,[],[f14])).
% 11.65/2.00  
% 11.65/2.00  fof(f23,plain,(
% 11.65/2.00    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f22,plain,(
% 11.65/2.00    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f24,plain,(
% 11.65/2.00    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 11.65/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f23,f22])).
% 11.65/2.00  
% 11.65/2.00  fof(f40,plain,(
% 11.65/2.00    v1_relat_1(sK1)),
% 11.65/2.00    inference(cnf_transformation,[],[f24])).
% 11.65/2.00  
% 11.65/2.00  fof(f12,axiom,(
% 11.65/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f18,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.65/2.00    inference(ennf_transformation,[],[f12])).
% 11.65/2.00  
% 11.65/2.00  fof(f38,plain,(
% 11.65/2.00    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f18])).
% 11.65/2.00  
% 11.65/2.00  fof(f50,plain,(
% 11.65/2.00    ( ! [X0,X1] : (k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.65/2.00    inference(definition_unfolding,[],[f38,f45,f45])).
% 11.65/2.00  
% 11.65/2.00  fof(f3,axiom,(
% 11.65/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f15,plain,(
% 11.65/2.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.65/2.00    inference(ennf_transformation,[],[f3])).
% 11.65/2.00  
% 11.65/2.00  fof(f29,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.65/2.00    inference(cnf_transformation,[],[f15])).
% 11.65/2.00  
% 11.65/2.00  fof(f47,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))) )),
% 11.65/2.00    inference(definition_unfolding,[],[f29,f36,f45])).
% 11.65/2.00  
% 11.65/2.00  fof(f27,plain,(
% 11.65/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f21])).
% 11.65/2.00  
% 11.65/2.00  fof(f25,plain,(
% 11.65/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.65/2.00    inference(cnf_transformation,[],[f21])).
% 11.65/2.00  
% 11.65/2.00  fof(f52,plain,(
% 11.65/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.65/2.00    inference(equality_resolution,[],[f25])).
% 11.65/2.00  
% 11.65/2.00  fof(f41,plain,(
% 11.65/2.00    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 11.65/2.00    inference(cnf_transformation,[],[f24])).
% 11.65/2.00  
% 11.65/2.00  fof(f39,plain,(
% 11.65/2.00    v1_relat_1(sK0)),
% 11.65/2.00    inference(cnf_transformation,[],[f24])).
% 11.65/2.00  
% 11.65/2.00  cnf(c_224,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1484,plain,
% 11.65/2.00      ( X0 != X1
% 11.65/2.00      | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) != X1
% 11.65/2.00      | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) = X0 ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_224]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2493,plain,
% 11.65/2.00      ( X0 != k3_tarski(X1)
% 11.65/2.00      | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) = X0
% 11.65/2.00      | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(X1) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_1484]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_5272,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) != k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))
% 11.65/2.00      | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))
% 11.65/2.00      | k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k2_relat_1(k6_subset_1(sK0,sK1)))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_2493]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_38039,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))) != k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0)))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_5272]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_667,plain,
% 11.65/2.00      ( X0 != X1
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X1
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = X0 ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_224]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_849,plain,
% 11.65/2.00      ( X0 != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = X0
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_667]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_27510,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0)))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_849]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_846,plain,
% 11.65/2.00      ( X0 != X1 | X0 = k2_relat_1(X2) | k2_relat_1(X2) != X1 ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_224]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1364,plain,
% 11.65/2.00      ( X0 != k2_relat_1(X1)
% 11.65/2.00      | X0 = k2_relat_1(X2)
% 11.65/2.00      | k2_relat_1(X2) != k2_relat_1(X1) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_846]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1856,plain,
% 11.65/2.00      ( k2_relat_1(X0) != k2_relat_1(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X2))) = k2_relat_1(X0)
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X2))) != k2_relat_1(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_1364]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_13438,plain,
% 11.65/2.00      ( k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0)))) != k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) != k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0)))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_1856]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_27503,plain,
% 11.65/2.00      ( k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))))
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) != k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_13438]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_13837,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_230,plain,
% 11.65/2.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 11.65/2.00      theory(equality) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2499,plain,
% 11.65/2.00      ( k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k2_relat_1(X2)
% 11.65/2.00      | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) != X2 ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_230]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_5283,plain,
% 11.65/2.00      ( k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0)))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
% 11.65/2.00      | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k6_subset_1(X1,X0))) != k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_2499]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_13427,plain,
% 11.65/2.00      ( k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))
% 11.65/2.00      | k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1))) != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_5283]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_4308,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))) = k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_225,plain,
% 11.65/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.65/2.00      theory(equality) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_500,plain,
% 11.65/2.00      ( ~ r1_tarski(X0,X1)
% 11.65/2.00      | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 11.65/2.00      | k2_relat_1(sK0) != X0
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X1 ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_225]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_545,plain,
% 11.65/2.00      ( ~ r1_tarski(k2_relat_1(sK0),X0)
% 11.65/2.00      | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 11.65/2.00      | k2_relat_1(sK0) != k2_relat_1(sK0)
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X0 ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_500]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_600,plain,
% 11.65/2.00      ( ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
% 11.65/2.00      | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 11.65/2.00      | k2_relat_1(sK0) != k2_relat_1(sK0)
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_545]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3583,plain,
% 11.65/2.00      ( ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))))
% 11.65/2.00      | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 11.65/2.00      | k2_relat_1(sK0) != k2_relat_1(sK0)
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_600]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_5,plain,
% 11.65/2.00      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
% 11.65/2.00      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
% 11.65/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1405,plain,
% 11.65/2.00      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))))
% 11.65/2.00      | ~ r1_tarski(k6_subset_1(X0,X1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2245,plain,
% 11.65/2.00      ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))
% 11.65/2.00      | r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_1405]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1,plain,
% 11.65/2.00      ( r1_tarski(X0,X0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1717,plain,
% 11.65/2.00      ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_6,plain,
% 11.65/2.00      ( ~ v1_relat_1(X0) | v1_relat_1(k6_subset_1(X0,X1)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1039,plain,
% 11.65/2.00      ( v1_relat_1(k6_subset_1(sK0,sK1)) | ~ v1_relat_1(sK0) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_9,negated_conjecture,
% 11.65/2.00      ( v1_relat_1(sK1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_471,plain,
% 11.65/2.00      ( v1_relat_1(sK1) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_7,plain,
% 11.65/2.00      ( ~ v1_relat_1(X0)
% 11.65/2.00      | ~ v1_relat_1(X1)
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 11.65/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_473,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
% 11.65/2.00      | v1_relat_1(X0) != iProver_top
% 11.65/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_829,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(X0))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,X0)))
% 11.65/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.00      inference(superposition,[status(thm)],[c_471,c_473]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_835,plain,
% 11.65/2.00      ( k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))
% 11.65/2.00      | v1_relat_1(sK0) != iProver_top ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_829]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_770,plain,
% 11.65/2.00      ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
% 11.65/2.00      | ~ v1_relat_1(sK1)
% 11.65/2.00      | k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k6_subset_1(sK0,sK1)))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_4,plain,
% 11.65/2.00      ( ~ r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
% 11.65/2.00      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 11.65/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_491,plain,
% 11.65/2.00      ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
% 11.65/2.00      | ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k4_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_236,plain,
% 11.65/2.00      ( k2_relat_1(sK0) = k2_relat_1(sK0) | sK0 != sK0 ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_230]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_0,plain,
% 11.65/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.65/2.00      inference(cnf_transformation,[],[f27]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_32,plain,
% 11.65/2.00      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2,plain,
% 11.65/2.00      ( r1_tarski(X0,X0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_28,plain,
% 11.65/2.00      ( r1_tarski(sK0,sK0) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_8,negated_conjecture,
% 11.65/2.00      ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
% 11.65/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_10,negated_conjecture,
% 11.65/2.00      ( v1_relat_1(sK0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_11,plain,
% 11.65/2.00      ( v1_relat_1(sK0) = iProver_top ),
% 11.65/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(contradiction,plain,
% 11.65/2.00      ( $false ),
% 11.65/2.00      inference(minisat,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_38039,c_27510,c_27503,c_13837,c_13427,c_4308,c_3583,
% 11.65/2.00                 c_2245,c_1717,c_1039,c_835,c_770,c_491,c_236,c_32,c_28,
% 11.65/2.00                 c_8,c_9,c_11,c_10]) ).
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  ------                               Statistics
% 11.65/2.00  
% 11.65/2.00  ------ General
% 11.65/2.00  
% 11.65/2.00  abstr_ref_over_cycles:                  0
% 11.65/2.00  abstr_ref_under_cycles:                 0
% 11.65/2.00  gc_basic_clause_elim:                   0
% 11.65/2.00  forced_gc_time:                         0
% 11.65/2.00  parsing_time:                           0.007
% 11.65/2.00  unif_index_cands_time:                  0.
% 11.65/2.00  unif_index_add_time:                    0.
% 11.65/2.00  orderings_time:                         0.
% 11.65/2.00  out_proof_time:                         0.008
% 11.65/2.00  total_time:                             1.282
% 11.65/2.00  num_of_symbols:                         39
% 11.65/2.00  num_of_terms:                           34981
% 11.65/2.00  
% 11.65/2.00  ------ Preprocessing
% 11.65/2.00  
% 11.65/2.00  num_of_splits:                          0
% 11.65/2.00  num_of_split_atoms:                     0
% 11.65/2.00  num_of_reused_defs:                     0
% 11.65/2.00  num_eq_ax_congr_red:                    0
% 11.65/2.00  num_of_sem_filtered_clauses:            1
% 11.65/2.00  num_of_subtypes:                        0
% 11.65/2.00  monotx_restored_types:                  0
% 11.65/2.00  sat_num_of_epr_types:                   0
% 11.65/2.00  sat_num_of_non_cyclic_types:            0
% 11.65/2.00  sat_guarded_non_collapsed_types:        0
% 11.65/2.00  num_pure_diseq_elim:                    0
% 11.65/2.00  simp_replaced_by:                       0
% 11.65/2.00  res_preprocessed:                       57
% 11.65/2.00  prep_upred:                             0
% 11.65/2.00  prep_unflattend:                        0
% 11.65/2.00  smt_new_axioms:                         0
% 11.65/2.00  pred_elim_cands:                        2
% 11.65/2.00  pred_elim:                              0
% 11.65/2.00  pred_elim_cl:                           0
% 11.65/2.00  pred_elim_cycles:                       2
% 11.65/2.00  merged_defs:                            8
% 11.65/2.00  merged_defs_ncl:                        0
% 11.65/2.00  bin_hyper_res:                          8
% 11.65/2.00  prep_cycles:                            4
% 11.65/2.00  pred_elim_time:                         0.
% 11.65/2.00  splitting_time:                         0.
% 11.65/2.00  sem_filter_time:                        0.
% 11.65/2.00  monotx_time:                            0.
% 11.65/2.00  subtype_inf_time:                       0.
% 11.65/2.00  
% 11.65/2.00  ------ Problem properties
% 11.65/2.00  
% 11.65/2.00  clauses:                                10
% 11.65/2.00  conjectures:                            3
% 11.65/2.00  epr:                                    4
% 11.65/2.00  horn:                                   10
% 11.65/2.00  ground:                                 3
% 11.65/2.00  unary:                                  5
% 11.65/2.00  binary:                                 3
% 11.65/2.00  lits:                                   17
% 11.65/2.00  lits_eq:                                3
% 11.65/2.00  fd_pure:                                0
% 11.65/2.00  fd_pseudo:                              0
% 11.65/2.00  fd_cond:                                0
% 11.65/2.00  fd_pseudo_cond:                         1
% 11.65/2.00  ac_symbols:                             0
% 11.65/2.00  
% 11.65/2.00  ------ Propositional Solver
% 11.65/2.00  
% 11.65/2.00  prop_solver_calls:                      37
% 11.65/2.00  prop_fast_solver_calls:                 708
% 11.65/2.00  smt_solver_calls:                       0
% 11.65/2.00  smt_fast_solver_calls:                  0
% 11.65/2.00  prop_num_of_clauses:                    14200
% 11.65/2.00  prop_preprocess_simplified:             21830
% 11.65/2.00  prop_fo_subsumed:                       0
% 11.65/2.00  prop_solver_time:                       0.
% 11.65/2.00  smt_solver_time:                        0.
% 11.65/2.00  smt_fast_solver_time:                   0.
% 11.65/2.00  prop_fast_solver_time:                  0.
% 11.65/2.00  prop_unsat_core_time:                   0.001
% 11.65/2.00  
% 11.65/2.00  ------ QBF
% 11.65/2.00  
% 11.65/2.00  qbf_q_res:                              0
% 11.65/2.00  qbf_num_tautologies:                    0
% 11.65/2.00  qbf_prep_cycles:                        0
% 11.65/2.00  
% 11.65/2.00  ------ BMC1
% 11.65/2.00  
% 11.65/2.00  bmc1_current_bound:                     -1
% 11.65/2.00  bmc1_last_solved_bound:                 -1
% 11.65/2.00  bmc1_unsat_core_size:                   -1
% 11.65/2.00  bmc1_unsat_core_parents_size:           -1
% 11.65/2.00  bmc1_merge_next_fun:                    0
% 11.65/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.65/2.00  
% 11.65/2.00  ------ Instantiation
% 11.65/2.00  
% 11.65/2.00  inst_num_of_clauses:                    3330
% 11.65/2.00  inst_num_in_passive:                    1610
% 11.65/2.00  inst_num_in_active:                     1599
% 11.65/2.00  inst_num_in_unprocessed:                121
% 11.65/2.00  inst_num_of_loops:                      1668
% 11.65/2.00  inst_num_of_learning_restarts:          0
% 11.65/2.00  inst_num_moves_active_passive:          62
% 11.65/2.00  inst_lit_activity:                      0
% 11.65/2.00  inst_lit_activity_moves:                0
% 11.65/2.00  inst_num_tautologies:                   0
% 11.65/2.00  inst_num_prop_implied:                  0
% 11.65/2.00  inst_num_existing_simplified:           0
% 11.65/2.00  inst_num_eq_res_simplified:             0
% 11.65/2.00  inst_num_child_elim:                    0
% 11.65/2.00  inst_num_of_dismatching_blockings:      6191
% 11.65/2.00  inst_num_of_non_proper_insts:           8168
% 11.65/2.00  inst_num_of_duplicates:                 0
% 11.65/2.00  inst_inst_num_from_inst_to_res:         0
% 11.65/2.00  inst_dismatching_checking_time:         0.
% 11.65/2.00  
% 11.65/2.00  ------ Resolution
% 11.65/2.00  
% 11.65/2.00  res_num_of_clauses:                     0
% 11.65/2.00  res_num_in_passive:                     0
% 11.65/2.00  res_num_in_active:                      0
% 11.65/2.00  res_num_of_loops:                       61
% 11.65/2.00  res_forward_subset_subsumed:            1032
% 11.65/2.00  res_backward_subset_subsumed:           10
% 11.65/2.00  res_forward_subsumed:                   0
% 11.65/2.00  res_backward_subsumed:                  0
% 11.65/2.00  res_forward_subsumption_resolution:     0
% 11.65/2.00  res_backward_subsumption_resolution:    0
% 11.65/2.00  res_clause_to_clause_subsumption:       5026
% 11.65/2.00  res_orphan_elimination:                 0
% 11.65/2.00  res_tautology_del:                      1011
% 11.65/2.00  res_num_eq_res_simplified:              0
% 11.65/2.00  res_num_sel_changes:                    0
% 11.65/2.00  res_moves_from_active_to_pass:          0
% 11.65/2.00  
% 11.65/2.00  ------ Superposition
% 11.65/2.00  
% 11.65/2.00  sup_time_total:                         0.
% 11.65/2.00  sup_time_generating:                    0.
% 11.65/2.00  sup_time_sim_full:                      0.
% 11.65/2.00  sup_time_sim_immed:                     0.
% 11.65/2.00  
% 11.65/2.00  sup_num_of_clauses:                     1618
% 11.65/2.00  sup_num_in_active:                      332
% 11.65/2.00  sup_num_in_passive:                     1286
% 11.65/2.00  sup_num_of_loops:                       332
% 11.65/2.00  sup_fw_superposition:                   964
% 11.65/2.00  sup_bw_superposition:                   1189
% 11.65/2.00  sup_immediate_simplified:               257
% 11.65/2.00  sup_given_eliminated:                   0
% 11.65/2.00  comparisons_done:                       0
% 11.65/2.00  comparisons_avoided:                    0
% 11.65/2.00  
% 11.65/2.00  ------ Simplifications
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  sim_fw_subset_subsumed:                 10
% 11.65/2.00  sim_bw_subset_subsumed:                 0
% 11.65/2.00  sim_fw_subsumed:                        80
% 11.65/2.00  sim_bw_subsumed:                        0
% 11.65/2.00  sim_fw_subsumption_res:                 0
% 11.65/2.00  sim_bw_subsumption_res:                 0
% 11.65/2.00  sim_tautology_del:                      51
% 11.65/2.00  sim_eq_tautology_del:                   62
% 11.65/2.00  sim_eq_res_simp:                        0
% 11.65/2.00  sim_fw_demodulated:                     266
% 11.65/2.00  sim_bw_demodulated:                     0
% 11.65/2.00  sim_light_normalised:                   50
% 11.65/2.00  sim_joinable_taut:                      0
% 11.65/2.00  sim_joinable_simp:                      0
% 11.65/2.00  sim_ac_normalised:                      0
% 11.65/2.00  sim_smt_subsumption:                    0
% 11.65/2.00  
%------------------------------------------------------------------------------
