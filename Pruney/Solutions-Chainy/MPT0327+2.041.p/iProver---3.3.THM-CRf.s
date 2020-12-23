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
% DateTime   : Thu Dec  3 11:38:04 EST 2020

% Result     : Theorem 19.29s
% Output     : CNFRefutation 19.29s
% Verified   : 
% Statistics : Number of formulae       :  122 (7809 expanded)
%              Number of clauses        :   73 (3129 expanded)
%              Number of leaves         :   16 (1380 expanded)
%              Depth                    :   34
%              Number of atoms          :  163 (16065 expanded)
%              Number of equality atoms :  119 (8438 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f30])).

fof(f53,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f41,f46,f46,f38])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(definition_unfolding,[],[f54,f46,f38,f57,f57])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_510,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_511,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_515,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1504,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_511,c_515])).

cnf(c_65661,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_510,c_1504])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_518,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_517,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3416,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_518,c_517])).

cnf(c_1502,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_518,c_515])).

cnf(c_3424,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3416,c_1502])).

cnf(c_3448,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3424,c_12])).

cnf(c_3447,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_3424,c_12])).

cnf(c_3747,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3424,c_3447])).

cnf(c_3805,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3747,c_9])).

cnf(c_3810,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_3805,c_3447])).

cnf(c_4476,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3448,c_3810])).

cnf(c_4502,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4476,c_9])).

cnf(c_4520,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4502,c_3810])).

cnf(c_4529,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_4520])).

cnf(c_7073,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_9,c_4529])).

cnf(c_4518,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_3810,c_4502])).

cnf(c_4860,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_4518,c_12])).

cnf(c_9459,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_7073,c_4860])).

cnf(c_9580,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_9459,c_9])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1034,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_12])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1030,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_4515,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_12,c_4502])).

cnf(c_6078,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_4520,c_4515])).

cnf(c_28199,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))),X1) ),
    inference(superposition,[status(thm)],[c_1030,c_6078])).

cnf(c_7242,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_7073,c_12])).

cnf(c_7297,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_7242,c_12])).

cnf(c_28331,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X0),X3)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_6078,c_7297])).

cnf(c_4530,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_4520])).

cnf(c_7483,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7073,c_4530])).

cnf(c_7653,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7483,c_12])).

cnf(c_28521,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X0),X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(demodulation,[status(thm)],[c_28331,c_7653])).

cnf(c_28626,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) ),
    inference(demodulation,[status(thm)],[c_28199,c_28521])).

cnf(c_28628,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_28626,c_9,c_3424])).

cnf(c_33104,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_28628])).

cnf(c_4528,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_12,c_4520])).

cnf(c_5676,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_4528,c_4502])).

cnf(c_34660,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_33104,c_5676])).

cnf(c_7078,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_3810,c_4529])).

cnf(c_35135,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34660,c_3424,c_7078])).

cnf(c_39997,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1034,c_35135])).

cnf(c_4527,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_4502,c_4502])).

cnf(c_7231,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_7073,c_4527])).

cnf(c_39998,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_39997,c_7231])).

cnf(c_17168,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_7297,c_9580])).

cnf(c_17172,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
    inference(light_normalisation,[status(thm)],[c_17168,c_12,c_7297])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_691,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_0,c_15])).

cnf(c_890,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_12,c_691])).

cnf(c_6018,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_4520,c_890])).

cnf(c_6102,plain,
    ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(superposition,[status(thm)],[c_4520,c_6018])).

cnf(c_7044,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_4529,c_6102])).

cnf(c_36259,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k1_xboole_0)) != sK1 ),
    inference(demodulation,[status(thm)],[c_35135,c_7044])).

cnf(c_36269,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) != sK1 ),
    inference(demodulation,[status(thm)],[c_36259,c_9])).

cnf(c_36906,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(superposition,[status(thm)],[c_17172,c_36269])).

cnf(c_40003,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_39998,c_36906])).

cnf(c_43074,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != sK1 ),
    inference(superposition,[status(thm)],[c_9580,c_40003])).

cnf(c_72046,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_65661,c_43074])).

cnf(c_72048,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_72046,c_9,c_3424])).

cnf(c_72049,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_72048])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:18:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 19.29/2.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.29/2.97  
% 19.29/2.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.29/2.97  
% 19.29/2.97  ------  iProver source info
% 19.29/2.97  
% 19.29/2.97  git: date: 2020-06-30 10:37:57 +0100
% 19.29/2.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.29/2.97  git: non_committed_changes: false
% 19.29/2.97  git: last_make_outside_of_git: false
% 19.29/2.97  
% 19.29/2.97  ------ 
% 19.29/2.97  ------ Parsing...
% 19.29/2.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.29/2.97  
% 19.29/2.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.29/2.97  
% 19.29/2.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.29/2.97  
% 19.29/2.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.29/2.97  ------ Proving...
% 19.29/2.97  ------ Problem Properties 
% 19.29/2.97  
% 19.29/2.97  
% 19.29/2.97  clauses                                 16
% 19.29/2.97  conjectures                             2
% 19.29/2.97  EPR                                     4
% 19.29/2.97  Horn                                    16
% 19.29/2.97  unary                                   10
% 19.29/2.97  binary                                  5
% 19.29/2.97  lits                                    23
% 19.29/2.97  lits eq                                 11
% 19.29/2.97  fd_pure                                 0
% 19.29/2.97  fd_pseudo                               0
% 19.29/2.97  fd_cond                                 0
% 19.29/2.97  fd_pseudo_cond                          1
% 19.29/2.97  AC symbols                              0
% 19.29/2.97  
% 19.29/2.97  ------ Input Options Time Limit: Unbounded
% 19.29/2.97  
% 19.29/2.97  
% 19.29/2.97  ------ 
% 19.29/2.97  Current options:
% 19.29/2.97  ------ 
% 19.29/2.97  
% 19.29/2.97  
% 19.29/2.97  
% 19.29/2.97  
% 19.29/2.97  ------ Proving...
% 19.29/2.97  
% 19.29/2.97  
% 19.29/2.97  % SZS status Theorem for theBenchmark.p
% 19.29/2.97  
% 19.29/2.97   Resolution empty clause
% 19.29/2.97  
% 19.29/2.97  % SZS output start CNFRefutation for theBenchmark.p
% 19.29/2.97  
% 19.29/2.97  fof(f19,conjecture,(
% 19.29/2.97    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f20,negated_conjecture,(
% 19.29/2.97    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 19.29/2.97    inference(negated_conjecture,[],[f19])).
% 19.29/2.97  
% 19.29/2.97  fof(f26,plain,(
% 19.29/2.97    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 19.29/2.97    inference(ennf_transformation,[],[f20])).
% 19.29/2.97  
% 19.29/2.97  fof(f30,plain,(
% 19.29/2.97    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 19.29/2.97    introduced(choice_axiom,[])).
% 19.29/2.97  
% 19.29/2.97  fof(f31,plain,(
% 19.29/2.97    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 19.29/2.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f30])).
% 19.29/2.97  
% 19.29/2.97  fof(f53,plain,(
% 19.29/2.97    r2_hidden(sK0,sK1)),
% 19.29/2.97    inference(cnf_transformation,[],[f31])).
% 19.29/2.97  
% 19.29/2.97  fof(f17,axiom,(
% 19.29/2.97    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f21,plain,(
% 19.29/2.97    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 19.29/2.97    inference(unused_predicate_definition_removal,[],[f17])).
% 19.29/2.97  
% 19.29/2.97  fof(f25,plain,(
% 19.29/2.97    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 19.29/2.97    inference(ennf_transformation,[],[f21])).
% 19.29/2.97  
% 19.29/2.97  fof(f51,plain,(
% 19.29/2.97    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f25])).
% 19.29/2.97  
% 19.29/2.97  fof(f13,axiom,(
% 19.29/2.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f47,plain,(
% 19.29/2.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f13])).
% 19.29/2.97  
% 19.29/2.97  fof(f14,axiom,(
% 19.29/2.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f48,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f14])).
% 19.29/2.97  
% 19.29/2.97  fof(f15,axiom,(
% 19.29/2.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f49,plain,(
% 19.29/2.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f15])).
% 19.29/2.97  
% 19.29/2.97  fof(f16,axiom,(
% 19.29/2.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f50,plain,(
% 19.29/2.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f16])).
% 19.29/2.97  
% 19.29/2.97  fof(f55,plain,(
% 19.29/2.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 19.29/2.97    inference(definition_unfolding,[],[f49,f50])).
% 19.29/2.97  
% 19.29/2.97  fof(f56,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 19.29/2.97    inference(definition_unfolding,[],[f48,f55])).
% 19.29/2.97  
% 19.29/2.97  fof(f57,plain,(
% 19.29/2.97    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 19.29/2.97    inference(definition_unfolding,[],[f47,f56])).
% 19.29/2.97  
% 19.29/2.97  fof(f63,plain,(
% 19.29/2.97    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 19.29/2.97    inference(definition_unfolding,[],[f51,f57])).
% 19.29/2.97  
% 19.29/2.97  fof(f5,axiom,(
% 19.29/2.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f23,plain,(
% 19.29/2.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.29/2.97    inference(ennf_transformation,[],[f5])).
% 19.29/2.97  
% 19.29/2.97  fof(f39,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f23])).
% 19.29/2.97  
% 19.29/2.97  fof(f8,axiom,(
% 19.29/2.97    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f42,plain,(
% 19.29/2.97    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.29/2.97    inference(cnf_transformation,[],[f8])).
% 19.29/2.97  
% 19.29/2.97  fof(f11,axiom,(
% 19.29/2.97    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f45,plain,(
% 19.29/2.97    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f11])).
% 19.29/2.97  
% 19.29/2.97  fof(f2,axiom,(
% 19.29/2.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f27,plain,(
% 19.29/2.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.29/2.97    inference(nnf_transformation,[],[f2])).
% 19.29/2.97  
% 19.29/2.97  fof(f28,plain,(
% 19.29/2.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.29/2.97    inference(flattening,[],[f27])).
% 19.29/2.97  
% 19.29/2.97  fof(f33,plain,(
% 19.29/2.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.29/2.97    inference(cnf_transformation,[],[f28])).
% 19.29/2.97  
% 19.29/2.97  fof(f67,plain,(
% 19.29/2.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.29/2.97    inference(equality_resolution,[],[f33])).
% 19.29/2.97  
% 19.29/2.97  fof(f3,axiom,(
% 19.29/2.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f29,plain,(
% 19.29/2.97    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.29/2.97    inference(nnf_transformation,[],[f3])).
% 19.29/2.97  
% 19.29/2.97  fof(f37,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f29])).
% 19.29/2.97  
% 19.29/2.97  fof(f4,axiom,(
% 19.29/2.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f38,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.29/2.97    inference(cnf_transformation,[],[f4])).
% 19.29/2.97  
% 19.29/2.97  fof(f58,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 19.29/2.97    inference(definition_unfolding,[],[f37,f38])).
% 19.29/2.97  
% 19.29/2.97  fof(f7,axiom,(
% 19.29/2.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f41,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.29/2.97    inference(cnf_transformation,[],[f7])).
% 19.29/2.97  
% 19.29/2.97  fof(f12,axiom,(
% 19.29/2.97    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f46,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f12])).
% 19.29/2.97  
% 19.29/2.97  fof(f60,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 19.29/2.97    inference(definition_unfolding,[],[f41,f46,f46,f38])).
% 19.29/2.97  
% 19.29/2.97  fof(f1,axiom,(
% 19.29/2.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.29/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.97  
% 19.29/2.97  fof(f32,plain,(
% 19.29/2.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.29/2.97    inference(cnf_transformation,[],[f1])).
% 19.29/2.97  
% 19.29/2.97  fof(f54,plain,(
% 19.29/2.97    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 19.29/2.97    inference(cnf_transformation,[],[f31])).
% 19.29/2.97  
% 19.29/2.97  fof(f65,plain,(
% 19.29/2.97    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1),
% 19.29/2.97    inference(definition_unfolding,[],[f54,f46,f38,f57,f57])).
% 19.29/2.97  
% 19.29/2.97  cnf(c_16,negated_conjecture,
% 19.29/2.97      ( r2_hidden(sK0,sK1) ),
% 19.29/2.97      inference(cnf_transformation,[],[f53]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_510,plain,
% 19.29/2.97      ( r2_hidden(sK0,sK1) = iProver_top ),
% 19.29/2.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_13,plain,
% 19.29/2.97      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 19.29/2.97      inference(cnf_transformation,[],[f63]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_511,plain,
% 19.29/2.97      ( r2_hidden(X0,X1) != iProver_top
% 19.29/2.97      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 19.29/2.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_6,plain,
% 19.29/2.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 19.29/2.97      inference(cnf_transformation,[],[f39]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_515,plain,
% 19.29/2.97      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 19.29/2.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_1504,plain,
% 19.29/2.97      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 19.29/2.97      | r2_hidden(X0,X1) != iProver_top ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_511,c_515]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_65661,plain,
% 19.29/2.97      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_510,c_1504]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_9,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.29/2.97      inference(cnf_transformation,[],[f42]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_12,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.29/2.97      inference(cnf_transformation,[],[f45]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f67]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_518,plain,
% 19.29/2.97      ( r1_tarski(X0,X0) = iProver_top ),
% 19.29/2.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4,plain,
% 19.29/2.97      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.29/2.97      inference(cnf_transformation,[],[f58]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_517,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 19.29/2.97      | r1_tarski(X0,X1) != iProver_top ),
% 19.29/2.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_3416,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_518,c_517]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_1502,plain,
% 19.29/2.97      ( k3_xboole_0(X0,X0) = X0 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_518,c_515]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_3424,plain,
% 19.29/2.97      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.29/2.97      inference(light_normalisation,[status(thm)],[c_3416,c_1502]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_3448,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_3424,c_12]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_3447,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_3424,c_12]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_3747,plain,
% 19.29/2.97      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_3424,c_3447]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_3805,plain,
% 19.29/2.97      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.29/2.97      inference(light_normalisation,[status(thm)],[c_3747,c_9]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_3810,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_3805,c_3447]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4476,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_3448,c_3810]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4502,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_4476,c_9]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4520,plain,
% 19.29/2.97      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_4502,c_3810]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4529,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_12,c_4520]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_7073,plain,
% 19.29/2.97      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_9,c_4529]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4518,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_3810,c_4502]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4860,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_4518,c_12]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_9459,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_7073,c_4860]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_9580,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 19.29/2.97      inference(light_normalisation,[status(thm)],[c_9459,c_9]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_8,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 19.29/2.97      inference(cnf_transformation,[],[f60]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_1034,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_8,c_12]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_0,plain,
% 19.29/2.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.29/2.97      inference(cnf_transformation,[],[f32]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_1030,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4515,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_12,c_4502]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_6078,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_4520,c_4515]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_28199,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))),X1) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_1030,c_6078]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_7242,plain,
% 19.29/2.97      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_7073,c_12]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_7297,plain,
% 19.29/2.97      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 19.29/2.97      inference(light_normalisation,[status(thm)],[c_7242,c_12]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_28331,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X0),X3)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_6078,c_7297]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4530,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_12,c_4520]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_7483,plain,
% 19.29/2.97      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_7073,c_4530]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_7653,plain,
% 19.29/2.97      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 19.29/2.97      inference(light_normalisation,[status(thm)],[c_7483,c_12]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_28521,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X0),X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_28331,c_7653]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_28626,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_28199,c_28521]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_28628,plain,
% 19.29/2.97      ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_28626,c_9,c_3424]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_33104,plain,
% 19.29/2.97      ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X0) = X0 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_0,c_28628]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4528,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_12,c_4520]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_5676,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_4528,c_4502]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_34660,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_33104,c_5676]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_7078,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_3810,c_4529]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_35135,plain,
% 19.29/2.97      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_34660,c_3424,c_7078]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_39997,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 19.29/2.97      inference(light_normalisation,[status(thm)],[c_1034,c_35135]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_4527,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_4502,c_4502]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_7231,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_7073,c_4527]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_39998,plain,
% 19.29/2.97      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_39997,c_7231]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_17168,plain,
% 19.29/2.97      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_7297,c_9580]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_17172,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
% 19.29/2.97      inference(light_normalisation,[status(thm)],[c_17168,c_12,c_7297]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_15,negated_conjecture,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 19.29/2.97      inference(cnf_transformation,[],[f65]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_691,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_0,c_15]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_890,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_12,c_691]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_6018,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_4520,c_890]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_6102,plain,
% 19.29/2.97      ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_4520,c_6018]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_7044,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_4529,c_6102]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_36259,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k1_xboole_0)) != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_35135,c_7044]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_36269,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_36259,c_9]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_36906,plain,
% 19.29/2.97      ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_17172,c_36269]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_40003,plain,
% 19.29/2.97      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_39998,c_36906]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_43074,plain,
% 19.29/2.97      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != sK1 ),
% 19.29/2.97      inference(superposition,[status(thm)],[c_9580,c_40003]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_72046,plain,
% 19.29/2.97      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_65661,c_43074]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_72048,plain,
% 19.29/2.97      ( sK1 != sK1 ),
% 19.29/2.97      inference(demodulation,[status(thm)],[c_72046,c_9,c_3424]) ).
% 19.29/2.97  
% 19.29/2.97  cnf(c_72049,plain,
% 19.29/2.97      ( $false ),
% 19.29/2.97      inference(equality_resolution_simp,[status(thm)],[c_72048]) ).
% 19.29/2.97  
% 19.29/2.97  
% 19.29/2.97  % SZS output end CNFRefutation for theBenchmark.p
% 19.29/2.97  
% 19.29/2.97  ------                               Statistics
% 19.29/2.97  
% 19.29/2.97  ------ Selected
% 19.29/2.97  
% 19.29/2.97  total_time:                             2.088
% 19.29/2.97  
%------------------------------------------------------------------------------
