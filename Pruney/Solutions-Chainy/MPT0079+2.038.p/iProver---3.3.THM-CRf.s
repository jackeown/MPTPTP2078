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
% DateTime   : Thu Dec  3 11:23:51 EST 2020

% Result     : Theorem 43.45s
% Output     : CNFRefutation 43.45s
% Verified   : 
% Statistics : Number of formulae       :  402 (92003 expanded)
%              Number of clauses        :  365 (36991 expanded)
%              Number of leaves         :   15 (23877 expanded)
%              Depth                    :   45
%              Number of atoms          :  445 (134954 expanded)
%              Number of equality atoms :  412 (107463 expanded)
%              Maximal formula depth    :    9 (   1 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f18])).

fof(f32,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f34,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_100,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_10,c_9,c_0])).

cnf(c_473,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_100])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1147,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_473,c_4])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_99,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_9,c_0])).

cnf(c_574,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_99,c_9])).

cnf(c_693,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_574,c_9])).

cnf(c_1215,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1147,c_693])).

cnf(c_1218,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1215,c_99])).

cnf(c_1300,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK3,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_1218])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1432,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) ),
    inference(superposition,[status(thm)],[c_1300,c_6])).

cnf(c_274,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_3270,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1218,c_274])).

cnf(c_4394,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_1147,c_3270])).

cnf(c_1303,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_1218,c_6])).

cnf(c_2255,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(sK1,k2_xboole_0(sK0,sK3))) = k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1303,c_4])).

cnf(c_2356,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,sK3),sK1) ),
    inference(demodulation,[status(thm)],[c_2255,c_4])).

cnf(c_4422,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_4394,c_1218,c_2356])).

cnf(c_4472,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_4422])).

cnf(c_690,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_574,c_0])).

cnf(c_826,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_690,c_6])).

cnf(c_79842,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k2_xboole_0(sK3,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK0))) ),
    inference(superposition,[status(thm)],[c_4472,c_826])).

cnf(c_413,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_99,c_6])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_647,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_413,c_7])).

cnf(c_652,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_647,c_7])).

cnf(c_2247,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_0,c_1303])).

cnf(c_2259,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_2247,c_1432])).

cnf(c_2264,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) ),
    inference(demodulation,[status(thm)],[c_2259,c_1303])).

cnf(c_275,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_4662,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1147,c_275])).

cnf(c_80077,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) ),
    inference(demodulation,[status(thm)],[c_79842,c_652,c_2264,c_4662])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_264,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_267,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1652,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_264,c_267])).

cnf(c_2118,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1652,c_4])).

cnf(c_415,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_416,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_415,c_5])).

cnf(c_476,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_100,c_4])).

cnf(c_2119,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_2118,c_416,c_476])).

cnf(c_641,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_416,c_0])).

cnf(c_1134,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_641,c_6])).

cnf(c_1234,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_476,c_416])).

cnf(c_1716,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1134,c_1234])).

cnf(c_1729,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1716,c_7])).

cnf(c_1730,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1729,c_4])).

cnf(c_1868,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_99,c_1730])).

cnf(c_490,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_10626,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1868,c_490])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_265,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1651,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_265,c_267])).

cnf(c_2057,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1651,c_4])).

cnf(c_2059,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_2057,c_416,c_476])).

cnf(c_10829,plain,
    ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10626,c_2059])).

cnf(c_10830,plain,
    ( k2_xboole_0(sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_10829,c_416])).

cnf(c_80078,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_80077,c_2119,c_10830])).

cnf(c_1230,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_476,c_9])).

cnf(c_1232,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_476,c_0])).

cnf(c_1746,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1232,c_9])).

cnf(c_698,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_693])).

cnf(c_9341,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1746,c_698])).

cnf(c_9362,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_9341,c_99])).

cnf(c_276,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_9552,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_9362,c_276])).

cnf(c_1741,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_1232])).

cnf(c_8095,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1741])).

cnf(c_29467,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X1)),X0),sK1)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X1)),X0),sK1) ),
    inference(superposition,[status(thm)],[c_9552,c_8095])).

cnf(c_1213,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1147,c_9])).

cnf(c_484,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_496,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_484,c_7])).

cnf(c_15213,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1213,c_496])).

cnf(c_5964,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_276,c_1730])).

cnf(c_15556,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15213,c_9,c_5964])).

cnf(c_29523,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X0),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_15556,c_8095])).

cnf(c_5876,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1213,c_276])).

cnf(c_6050,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5876,c_9])).

cnf(c_29705,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X0),k1_xboole_0) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_29523,c_6050])).

cnf(c_414,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_417,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_414,c_4])).

cnf(c_3478,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1213,c_417])).

cnf(c_3488,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3478,c_1147])).

cnf(c_8127,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1213,c_1741])).

cnf(c_1725,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1716,c_7])).

cnf(c_1733,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1725,c_1234])).

cnf(c_8263,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_8127,c_1733,c_4662])).

cnf(c_29706,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_29705,c_3488,c_8263])).

cnf(c_29838,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(X1,sK0)),sK1),X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK2,X0)))) ),
    inference(demodulation,[status(thm)],[c_29467,c_29706])).

cnf(c_29839,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(X1,sK0)),sK1),X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_29838,c_9362])).

cnf(c_89053,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK0),sK1),sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1230,c_29839])).

cnf(c_2550,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_417,c_690])).

cnf(c_2558,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_2550,c_99])).

cnf(c_1302,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,sK3),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_1218,c_9])).

cnf(c_1441,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK0,sK3)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_690,c_1302])).

cnf(c_818,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_416,c_690])).

cnf(c_831,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_818,c_99])).

cnf(c_838,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_831,c_9])).

cnf(c_893,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_690,c_838])).

cnf(c_650,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_413,c_4])).

cnf(c_651,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_650,c_4])).

cnf(c_896,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_893,c_651])).

cnf(c_688,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK3,X0)),X1) ),
    inference(superposition,[status(thm)],[c_574,c_9])).

cnf(c_702,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_693,c_9])).

cnf(c_709,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_688,c_693,c_702])).

cnf(c_897,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_896,c_641,c_693,c_709])).

cnf(c_1446,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK0,sK3)))) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1441,c_897])).

cnf(c_1447,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK3))) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_1446,c_693,c_1213])).

cnf(c_1448,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_1447,c_1213,c_1218])).

cnf(c_1556,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_1448])).

cnf(c_410,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_3514,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK0),sK1) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1556,c_410])).

cnf(c_3522,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK0),sK1) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3514,c_410])).

cnf(c_89356,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_89053,c_2558,c_3522])).

cnf(c_7586,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_1230])).

cnf(c_89492,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_89356,c_7586])).

cnf(c_24634,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_410,c_7586])).

cnf(c_7597,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k2_xboole_0(X3,X2)) ),
    inference(superposition,[status(thm)],[c_275,c_1230])).

cnf(c_24966,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_24634,c_7597])).

cnf(c_1750,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1232,c_693])).

cnf(c_1753,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1750,c_99])).

cnf(c_2043,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X1) ),
    inference(superposition,[status(thm)],[c_1753,c_9])).

cnf(c_2651,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK3)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_651,c_690])).

cnf(c_2652,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_2651,c_99,c_693,c_1147])).

cnf(c_2657,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_2652,c_9])).

cnf(c_2465,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_99,c_410])).

cnf(c_2836,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2465,c_4])).

cnf(c_2837,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_2836,c_2558])).

cnf(c_3091,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK3,sK2),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_2837,c_9])).

cnf(c_3097,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK3,sK2),X0)) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3091,c_2657])).

cnf(c_573,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_4,c_9])).

cnf(c_580,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_573,c_9])).

cnf(c_3098,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_3097,c_580,c_693])).

cnf(c_5885,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1753,c_276])).

cnf(c_6469,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X1)) ),
    inference(demodulation,[status(thm)],[c_2043,c_2657,c_3098,c_5885])).

cnf(c_24734,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),sK1) ),
    inference(superposition,[status(thm)],[c_6469,c_7586])).

cnf(c_24971,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),sK1) ),
    inference(demodulation,[status(thm)],[c_24966,c_24734])).

cnf(c_25010,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(X1,k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK3,X0),sK1))) ),
    inference(demodulation,[status(thm)],[c_24971,c_24966])).

cnf(c_816,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_0,c_690])).

cnf(c_6288,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_816,c_276])).

cnf(c_6315,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6288,c_698])).

cnf(c_25011,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(X1,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0)))) ),
    inference(demodulation,[status(thm)],[c_25010,c_6315])).

cnf(c_25012,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_25011,c_1753])).

cnf(c_85939,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X3),X1),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1746,c_25012])).

cnf(c_86125,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),X1),k2_xboole_0(sK1,sK0)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_85939,c_25012])).

cnf(c_24733,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),sK1) ),
    inference(superposition,[status(thm)],[c_5885,c_7586])).

cnf(c_24970,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),sK1) ),
    inference(demodulation,[status(thm)],[c_24966,c_24733])).

cnf(c_25013,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X1,k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK3,X0),sK1))) ),
    inference(demodulation,[status(thm)],[c_24970,c_24966])).

cnf(c_25014,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X1,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0)))) ),
    inference(demodulation,[status(thm)],[c_25013,c_6315])).

cnf(c_25015,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_25014,c_1753])).

cnf(c_88544,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,k4_xboole_0(X1,X2))),X3),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,sK0)),k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,sK0)),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_490,c_25015])).

cnf(c_10717,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X3,X2)) = k2_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_490,c_276])).

cnf(c_88840,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_88544,c_10717,c_25012])).

cnf(c_89505,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_89492,c_2558,c_86125,c_88840])).

cnf(c_89881,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_89505,c_0])).

cnf(c_89912,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X1),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_89505,c_7586])).

cnf(c_90001,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0)) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_89912])).

cnf(c_90027,plain,
    ( k2_xboole_0(sK1,sK0) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_89881,c_90001])).

cnf(c_489,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_100])).

cnf(c_493,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_489,c_7,c_490])).

cnf(c_13640,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_493,c_6])).

cnf(c_13665,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13640,c_4,c_7,c_1730])).

cnf(c_47336,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_13665])).

cnf(c_86779,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1868,c_47336])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_550,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_564,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_550,c_6])).

cnf(c_412,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_7331,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_410,c_412])).

cnf(c_7388,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_7331,c_410,c_4662])).

cnf(c_22083,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_564,c_564,c_7388])).

cnf(c_88074,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK0)),k4_xboole_0(k4_xboole_0(sK3,sK0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK0)) ),
    inference(superposition,[status(thm)],[c_86779,c_22083])).

cnf(c_88108,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK0)),k4_xboole_0(k4_xboole_0(sK3,sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_88074,c_86779])).

cnf(c_88109,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK0,k4_xboole_0(sK3,k2_xboole_0(sK0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_88108,c_7,c_412,c_641])).

cnf(c_10637,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_490])).

cnf(c_88110,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK0,k4_xboole_0(sK3,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_88109,c_10637])).

cnf(c_88111,plain,
    ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_88110,c_5,c_10830])).

cnf(c_91270,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK3),k1_xboole_0) = k2_xboole_0(sK3,sK0) ),
    inference(superposition,[status(thm)],[c_88111,c_8095])).

cnf(c_91304,plain,
    ( k2_xboole_0(sK3,sK0) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_91270,c_10830])).

cnf(c_91305,plain,
    ( k2_xboole_0(sK3,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_91304,c_416])).

cnf(c_155771,plain,
    ( k4_xboole_0(sP0_iProver_split,sK0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1432,c_1432,c_80078,c_90027,c_91305])).

cnf(c_15190,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_476,c_496])).

cnf(c_15575,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15190,c_7,c_1733])).

cnf(c_10644,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_99,c_490])).

cnf(c_16303,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,X0),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_15575,c_10644])).

cnf(c_16304,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_16303,c_7,c_416])).

cnf(c_577,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_4])).

cnf(c_578,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_577,c_9])).

cnf(c_579,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_578,c_490])).

cnf(c_38307,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),k2_xboole_0(sK3,sK1)) = k2_xboole_0(k2_xboole_0(X0,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_16304,c_579])).

cnf(c_24643,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1868,c_7586])).

cnf(c_25576,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,sK3),X1)) = k2_xboole_0(k2_xboole_0(sK3,X0),X1) ),
    inference(superposition,[status(thm)],[c_24643,c_9])).

cnf(c_4660,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_416,c_275])).

cnf(c_12304,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_10644,c_275])).

cnf(c_15004,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK3,k4_xboole_0(sK0,sK2))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1730,c_12304])).

cnf(c_12279,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1730,c_10644])).

cnf(c_12339,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK0,sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_12279,c_416])).

cnf(c_15133,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_15004,c_12339])).

cnf(c_25632,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),sK3) = k2_xboole_0(X0,k2_xboole_0(sK3,X1)) ),
    inference(demodulation,[status(thm)],[c_25576,c_4660,c_15133,c_24966])).

cnf(c_38821,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),k2_xboole_0(sK3,sK1)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_38307,c_2652,c_25632,c_29706])).

cnf(c_40499,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK1)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1147,c_38821])).

cnf(c_40613,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_40499,c_2558])).

cnf(c_40996,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK1),sK2) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_40613,c_410])).

cnf(c_41054,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK1),sK2) = k4_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_40996,c_2465])).

cnf(c_12295,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1)) = k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1) ),
    inference(superposition,[status(thm)],[c_10644,c_9])).

cnf(c_14417,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK3) = k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_12295,c_417])).

cnf(c_14423,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK3) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_14417,c_10644])).

cnf(c_22175,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),k4_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK3))) = k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK3) ),
    inference(superposition,[status(thm)],[c_14423,c_22083])).

cnf(c_2484,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_410,c_8])).

cnf(c_2494,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2484,c_410])).

cnf(c_2495,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2494,c_412])).

cnf(c_22375,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) = k4_xboole_0(k4_xboole_0(X0,sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_22175,c_7,c_410,c_2495])).

cnf(c_22376,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),sK3) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_22375,c_99])).

cnf(c_41101,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK1),k2_xboole_0(sK1,sK0)) = k4_xboole_0(k4_xboole_0(sK3,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_41054,c_22376])).

cnf(c_9964,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),X1),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_1232,c_9552])).

cnf(c_10011,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),X1),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_9964,c_9362])).

cnf(c_15373,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(X0,sK1),sK2)) = k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_496,c_10644])).

cnf(c_15381,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(X0,sK1),sK2)) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_15373,c_10644])).

cnf(c_1866,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_1730])).

cnf(c_3777,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1866,c_7])).

cnf(c_3785,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3777,c_7,c_1234])).

cnf(c_16403,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK1),sK2),sK3),k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15381,c_3785])).

cnf(c_16437,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16403,c_7])).

cnf(c_2486,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_410,c_100])).

cnf(c_2492,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2486,c_4,c_412])).

cnf(c_12303,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1)) = k2_xboole_0(X1,k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_10644,c_276])).

cnf(c_14696,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) ),
    inference(superposition,[status(thm)],[c_2492,c_12303])).

cnf(c_14786,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_14696,c_2657])).

cnf(c_2653,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_2652,c_651])).

cnf(c_4666,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2653,c_275])).

cnf(c_14787,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_14786,c_2652,c_4666,c_6050])).

cnf(c_14857,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1) ),
    inference(superposition,[status(thm)],[c_14787,c_9])).

cnf(c_7224,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2)) = k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(sK1,sK0)),X2) ),
    inference(superposition,[status(thm)],[c_5885,c_9])).

cnf(c_6503,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2)) = k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_6469,c_9])).

cnf(c_6183,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X0,sK3),X1)) = k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_698,c_9])).

cnf(c_6524,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2)) = k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X1,sK3),X2)) ),
    inference(demodulation,[status(thm)],[c_6503,c_6183])).

cnf(c_7247,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1) = k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X0,sK3),X1)) ),
    inference(light_normalisation,[status(thm)],[c_7224,c_6524])).

cnf(c_14887,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1)) = k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X0,sK3),X1)) ),
    inference(light_normalisation,[status(thm)],[c_14857,c_7247])).

cnf(c_16438,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X0,sK3),X1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16437,c_99,c_14887])).

cnf(c_16549,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,sK3),sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_275,c_16438])).

cnf(c_17382,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK1),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1147,c_16549])).

cnf(c_17420,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK1),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17382,c_2652])).

cnf(c_18728,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK1),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10011,c_17420])).

cnf(c_41112,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK2),sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_41101,c_18728])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_266,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1017,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_264,c_266])).

cnf(c_1654,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1017,c_267])).

cnf(c_10650,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_2652,c_490])).

cnf(c_16302,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X0),sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_15575,c_10650])).

cnf(c_16305,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_16302,c_7,c_416])).

cnf(c_18312,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sK2 ),
    inference(superposition,[status(thm)],[c_9,c_16305])).

cnf(c_9553,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),k2_xboole_0(sK1,X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_9362,c_275])).

cnf(c_3260,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2652,c_274])).

cnf(c_4058,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_0,c_3260])).

cnf(c_29446,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k2_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
    inference(superposition,[status(thm)],[c_4058,c_8095])).

cnf(c_29875,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_29446,c_29706])).

cnf(c_29876,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_29875,c_2652])).

cnf(c_45917,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))),sK3)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_9553,c_29876])).

cnf(c_4680,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1753,c_275])).

cnf(c_9560,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X1)),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_9362,c_4680])).

cnf(c_4669,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1218,c_275])).

cnf(c_5413,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1753,c_4669])).

cnf(c_5449,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_5413,c_4669])).

cnf(c_2541,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),sK1) ),
    inference(superposition,[status(thm)],[c_1753,c_417])).

cnf(c_4729,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_275,c_690])).

cnf(c_3306,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_274,c_690])).

cnf(c_4744,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_4729,c_3306])).

cnf(c_5450,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_5449,c_1147,c_2541,c_4744])).

cnf(c_1440,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_1147,c_1302])).

cnf(c_1449,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1440,c_1218])).

cnf(c_1562,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_1449])).

cnf(c_7781,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK0),k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1562,c_275])).

cnf(c_7795,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK0),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_7781,c_2657])).

cnf(c_4671,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1213,c_275])).

cnf(c_4673,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK0),k2_xboole_0(sK1,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1300,c_275])).

cnf(c_7796,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_7795,c_3098,c_4671,c_4673])).

cnf(c_9561,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_9560,c_5450,c_7796])).

cnf(c_46079,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))),sK3)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_45917,c_9561])).

cnf(c_7660,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1230,c_276])).

cnf(c_46080,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(k2_xboole_0(sK2,sK0),sK3))) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_46079,c_4744,c_6183,c_7247,c_7660])).

cnf(c_692,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_574,c_4])).

cnf(c_5769,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0)))) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_692,c_692,c_2657,c_3098])).

cnf(c_12272,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_10644,c_5769])).

cnf(c_29473,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2)) = k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2) ),
    inference(superposition,[status(thm)],[c_12272,c_8095])).

cnf(c_29824,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2)) = k2_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_29473,c_29706])).

cnf(c_4683,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2558,c_275])).

cnf(c_5496,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_4683])).

cnf(c_5550,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK1,sK0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_5496,c_4683])).

cnf(c_12658,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2) = k4_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),sK2) ),
    inference(superposition,[status(thm)],[c_12272,c_410])).

cnf(c_6182,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),sK2) = k4_xboole_0(k2_xboole_0(X0,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_698,c_410])).

cnf(c_12683,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2) = k4_xboole_0(k2_xboole_0(X0,sK3),sK2) ),
    inference(light_normalisation,[status(thm)],[c_12658,c_6182])).

cnf(c_29825,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),k4_xboole_0(k2_xboole_0(X0,sK3),sK2)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_29824,c_99,c_5550,c_12683])).

cnf(c_31332,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK3),sK3),sK2)) = k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_3270,c_29825])).

cnf(c_31526,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)),k4_xboole_0(sK0,sK2)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_31332,c_4422,c_10830])).

cnf(c_7656,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1230,c_0])).

cnf(c_25231,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK3),X1)) = k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_4669,c_7656])).

cnf(c_25465,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(sK0,X1)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_25231,c_4669,c_10830])).

cnf(c_31527,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2))) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_31526,c_4744,c_6183,c_25465])).

cnf(c_31528,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_31527,c_10830])).

cnf(c_3256,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_274])).

cnf(c_31529,plain,
    ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_31528,c_1232,c_3256])).

cnf(c_46081,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,sK3))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_46080,c_413,c_10830,c_31529])).

cnf(c_46163,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,sK3)),sK2) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_46081,c_410])).

cnf(c_46221,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,sK3)),sK2) = k4_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_46163,c_2465])).

cnf(c_46296,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,sK3)),k2_xboole_0(sK2,X0)) = k4_xboole_0(k4_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_46221,c_7])).

cnf(c_24808,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_7586,c_496])).

cnf(c_24876,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_24808,c_7586])).

cnf(c_46347,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_46296,c_7,c_24876])).

cnf(c_81677,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(X1,sK3))))) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_18312,c_46347])).

cnf(c_81772,plain,
    ( k4_xboole_0(sK3,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_81677,c_18312])).

cnf(c_153521,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1654,c_1654,c_81772])).

cnf(c_153548,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK3,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_153521,c_4])).

cnf(c_10674,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k4_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k4_xboole_0(X1,sK1)) ),
    inference(superposition,[status(thm)],[c_1753,c_490])).

cnf(c_84380,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k4_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(k4_xboole_0(X1,sK1),sK0)) ),
    inference(demodulation,[status(thm)],[c_10674,c_29706])).

cnf(c_84409,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(k4_xboole_0(sK3,sK1),sK0)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1868,c_84380])).

cnf(c_85598,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK3,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_84409,c_2059])).

cnf(c_4672,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1232,c_275])).

cnf(c_85599,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,X0),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_85598,c_4672,c_8263,c_10830])).

cnf(c_153564,plain,
    ( k4_xboole_0(sK3,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_153548,c_416,c_85599])).

cnf(c_155248,plain,
    ( k4_xboole_0(sK0,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_41112,c_41112,c_153564])).

cnf(c_155291,plain,
    ( k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_155248,c_4])).

cnf(c_155314,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_155291,c_91305])).

cnf(c_155315,plain,
    ( sK0 = sK3 ),
    inference(demodulation,[status(thm)],[c_155314,c_416])).

cnf(c_155772,plain,
    ( k4_xboole_0(sP0_iProver_split,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_155771,c_155315])).

cnf(c_700,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_693])).

cnf(c_706,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_700,c_693])).

cnf(c_155823,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sP0_iProver_split)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_155772,c_706])).

cnf(c_89965,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_89505,c_12303])).

cnf(c_90425,plain,
    ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK2))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_89965,c_2653,c_90027])).

cnf(c_90426,plain,
    ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK0,sK1),sK2))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_90425,c_6])).

cnf(c_12280,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1866,c_10644])).

cnf(c_12338,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_12280,c_7,c_416])).

cnf(c_90427,plain,
    ( k2_xboole_0(sP0_iProver_split,sK3) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_90426,c_7,c_12338])).

cnf(c_91389,plain,
    ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_90427,c_816])).

cnf(c_91395,plain,
    ( k2_xboole_0(sK2,sP0_iProver_split) = k2_xboole_0(sP0_iProver_split,sP0_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_91389,c_90027])).

cnf(c_91396,plain,
    ( k2_xboole_0(sK2,sP0_iProver_split) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_91395,c_1147])).

cnf(c_91390,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sP0_iProver_split)) = k2_xboole_0(sK2,sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_90427,c_698])).

cnf(c_91397,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sP0_iProver_split)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_91396,c_91390])).

cnf(c_155839,plain,
    ( k2_xboole_0(sK1,sK3) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_155823,c_1448,c_91397,c_155315])).

cnf(c_157156,plain,
    ( k4_xboole_0(sP0_iProver_split,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_155839,c_6])).

cnf(c_1016,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_265,c_266])).

cnf(c_1653,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1016,c_267])).

cnf(c_151792,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK3),sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1653,c_412])).

cnf(c_151805,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),k2_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK1,sK3),k2_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1653,c_579])).

cnf(c_151809,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),k2_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK1,sK3),X0) ),
    inference(light_normalisation,[status(thm)],[c_151805,c_416])).

cnf(c_151810,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),X0) = k2_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_151809,c_7586])).

cnf(c_151815,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_151792,c_1653,c_151810])).

cnf(c_151816,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_151815,c_5,c_7,c_416,c_1147])).

cnf(c_157275,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_157156,c_151816,c_155772])).

cnf(c_103,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_337,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_404,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_26362,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_102,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_402,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_11,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_157275,c_26362,c_402,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 43.45/6.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.45/6.00  
% 43.45/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.45/6.00  
% 43.45/6.00  ------  iProver source info
% 43.45/6.00  
% 43.45/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.45/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.45/6.00  git: non_committed_changes: false
% 43.45/6.00  git: last_make_outside_of_git: false
% 43.45/6.00  
% 43.45/6.00  ------ 
% 43.45/6.00  
% 43.45/6.00  ------ Input Options
% 43.45/6.00  
% 43.45/6.00  --out_options                           all
% 43.45/6.00  --tptp_safe_out                         true
% 43.45/6.00  --problem_path                          ""
% 43.45/6.00  --include_path                          ""
% 43.45/6.00  --clausifier                            res/vclausify_rel
% 43.45/6.00  --clausifier_options                    ""
% 43.45/6.00  --stdin                                 false
% 43.45/6.00  --stats_out                             all
% 43.45/6.00  
% 43.45/6.00  ------ General Options
% 43.45/6.00  
% 43.45/6.00  --fof                                   false
% 43.45/6.00  --time_out_real                         305.
% 43.45/6.00  --time_out_virtual                      -1.
% 43.45/6.00  --symbol_type_check                     false
% 43.45/6.00  --clausify_out                          false
% 43.45/6.00  --sig_cnt_out                           false
% 43.45/6.00  --trig_cnt_out                          false
% 43.45/6.00  --trig_cnt_out_tolerance                1.
% 43.45/6.00  --trig_cnt_out_sk_spl                   false
% 43.45/6.00  --abstr_cl_out                          false
% 43.45/6.00  
% 43.45/6.00  ------ Global Options
% 43.45/6.00  
% 43.45/6.00  --schedule                              default
% 43.45/6.00  --add_important_lit                     false
% 43.45/6.00  --prop_solver_per_cl                    1000
% 43.45/6.00  --min_unsat_core                        false
% 43.45/6.00  --soft_assumptions                      false
% 43.45/6.00  --soft_lemma_size                       3
% 43.45/6.00  --prop_impl_unit_size                   0
% 43.45/6.00  --prop_impl_unit                        []
% 43.45/6.00  --share_sel_clauses                     true
% 43.45/6.00  --reset_solvers                         false
% 43.45/6.00  --bc_imp_inh                            [conj_cone]
% 43.45/6.00  --conj_cone_tolerance                   3.
% 43.45/6.00  --extra_neg_conj                        none
% 43.45/6.00  --large_theory_mode                     true
% 43.45/6.00  --prolific_symb_bound                   200
% 43.45/6.00  --lt_threshold                          2000
% 43.45/6.00  --clause_weak_htbl                      true
% 43.45/6.00  --gc_record_bc_elim                     false
% 43.45/6.00  
% 43.45/6.00  ------ Preprocessing Options
% 43.45/6.00  
% 43.45/6.00  --preprocessing_flag                    true
% 43.45/6.00  --time_out_prep_mult                    0.1
% 43.45/6.00  --splitting_mode                        input
% 43.45/6.00  --splitting_grd                         true
% 43.45/6.00  --splitting_cvd                         false
% 43.45/6.00  --splitting_cvd_svl                     false
% 43.45/6.00  --splitting_nvd                         32
% 43.45/6.00  --sub_typing                            true
% 43.45/6.00  --prep_gs_sim                           true
% 43.45/6.00  --prep_unflatten                        true
% 43.45/6.00  --prep_res_sim                          true
% 43.45/6.00  --prep_upred                            true
% 43.45/6.00  --prep_sem_filter                       exhaustive
% 43.45/6.00  --prep_sem_filter_out                   false
% 43.45/6.00  --pred_elim                             true
% 43.45/6.00  --res_sim_input                         true
% 43.45/6.00  --eq_ax_congr_red                       true
% 43.45/6.00  --pure_diseq_elim                       true
% 43.45/6.00  --brand_transform                       false
% 43.45/6.00  --non_eq_to_eq                          false
% 43.45/6.00  --prep_def_merge                        true
% 43.45/6.00  --prep_def_merge_prop_impl              false
% 43.45/6.00  --prep_def_merge_mbd                    true
% 43.45/6.00  --prep_def_merge_tr_red                 false
% 43.45/6.00  --prep_def_merge_tr_cl                  false
% 43.45/6.00  --smt_preprocessing                     true
% 43.45/6.00  --smt_ac_axioms                         fast
% 43.45/6.00  --preprocessed_out                      false
% 43.45/6.00  --preprocessed_stats                    false
% 43.45/6.00  
% 43.45/6.00  ------ Abstraction refinement Options
% 43.45/6.00  
% 43.45/6.00  --abstr_ref                             []
% 43.45/6.00  --abstr_ref_prep                        false
% 43.45/6.00  --abstr_ref_until_sat                   false
% 43.45/6.00  --abstr_ref_sig_restrict                funpre
% 43.45/6.00  --abstr_ref_af_restrict_to_split_sk     false
% 43.45/6.00  --abstr_ref_under                       []
% 43.45/6.00  
% 43.45/6.00  ------ SAT Options
% 43.45/6.00  
% 43.45/6.00  --sat_mode                              false
% 43.45/6.00  --sat_fm_restart_options                ""
% 43.45/6.00  --sat_gr_def                            false
% 43.45/6.00  --sat_epr_types                         true
% 43.45/6.00  --sat_non_cyclic_types                  false
% 43.45/6.00  --sat_finite_models                     false
% 43.45/6.00  --sat_fm_lemmas                         false
% 43.45/6.00  --sat_fm_prep                           false
% 43.45/6.00  --sat_fm_uc_incr                        true
% 43.45/6.00  --sat_out_model                         small
% 43.45/6.00  --sat_out_clauses                       false
% 43.45/6.00  
% 43.45/6.00  ------ QBF Options
% 43.45/6.00  
% 43.45/6.00  --qbf_mode                              false
% 43.45/6.00  --qbf_elim_univ                         false
% 43.45/6.00  --qbf_dom_inst                          none
% 43.45/6.00  --qbf_dom_pre_inst                      false
% 43.45/6.00  --qbf_sk_in                             false
% 43.45/6.00  --qbf_pred_elim                         true
% 43.45/6.00  --qbf_split                             512
% 43.45/6.00  
% 43.45/6.00  ------ BMC1 Options
% 43.45/6.00  
% 43.45/6.00  --bmc1_incremental                      false
% 43.45/6.00  --bmc1_axioms                           reachable_all
% 43.45/6.00  --bmc1_min_bound                        0
% 43.45/6.00  --bmc1_max_bound                        -1
% 43.45/6.00  --bmc1_max_bound_default                -1
% 43.45/6.00  --bmc1_symbol_reachability              true
% 43.45/6.00  --bmc1_property_lemmas                  false
% 43.45/6.00  --bmc1_k_induction                      false
% 43.45/6.00  --bmc1_non_equiv_states                 false
% 43.45/6.00  --bmc1_deadlock                         false
% 43.45/6.00  --bmc1_ucm                              false
% 43.45/6.00  --bmc1_add_unsat_core                   none
% 43.45/6.00  --bmc1_unsat_core_children              false
% 43.45/6.00  --bmc1_unsat_core_extrapolate_axioms    false
% 43.45/6.00  --bmc1_out_stat                         full
% 43.45/6.00  --bmc1_ground_init                      false
% 43.45/6.00  --bmc1_pre_inst_next_state              false
% 43.45/6.00  --bmc1_pre_inst_state                   false
% 43.45/6.00  --bmc1_pre_inst_reach_state             false
% 43.45/6.00  --bmc1_out_unsat_core                   false
% 43.45/6.00  --bmc1_aig_witness_out                  false
% 43.45/6.00  --bmc1_verbose                          false
% 43.45/6.00  --bmc1_dump_clauses_tptp                false
% 43.45/6.00  --bmc1_dump_unsat_core_tptp             false
% 43.45/6.00  --bmc1_dump_file                        -
% 43.45/6.00  --bmc1_ucm_expand_uc_limit              128
% 43.45/6.00  --bmc1_ucm_n_expand_iterations          6
% 43.45/6.00  --bmc1_ucm_extend_mode                  1
% 43.45/6.00  --bmc1_ucm_init_mode                    2
% 43.45/6.00  --bmc1_ucm_cone_mode                    none
% 43.45/6.00  --bmc1_ucm_reduced_relation_type        0
% 43.45/6.00  --bmc1_ucm_relax_model                  4
% 43.45/6.00  --bmc1_ucm_full_tr_after_sat            true
% 43.45/6.00  --bmc1_ucm_expand_neg_assumptions       false
% 43.45/6.00  --bmc1_ucm_layered_model                none
% 43.45/6.00  --bmc1_ucm_max_lemma_size               10
% 43.45/6.00  
% 43.45/6.00  ------ AIG Options
% 43.45/6.00  
% 43.45/6.00  --aig_mode                              false
% 43.45/6.00  
% 43.45/6.00  ------ Instantiation Options
% 43.45/6.00  
% 43.45/6.00  --instantiation_flag                    true
% 43.45/6.00  --inst_sos_flag                         true
% 43.45/6.00  --inst_sos_phase                        true
% 43.45/6.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.45/6.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.45/6.00  --inst_lit_sel_side                     num_symb
% 43.45/6.00  --inst_solver_per_active                1400
% 43.45/6.00  --inst_solver_calls_frac                1.
% 43.45/6.00  --inst_passive_queue_type               priority_queues
% 43.45/6.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.45/6.00  --inst_passive_queues_freq              [25;2]
% 43.45/6.00  --inst_dismatching                      true
% 43.45/6.00  --inst_eager_unprocessed_to_passive     true
% 43.45/6.00  --inst_prop_sim_given                   true
% 43.45/6.00  --inst_prop_sim_new                     false
% 43.45/6.00  --inst_subs_new                         false
% 43.45/6.00  --inst_eq_res_simp                      false
% 43.45/6.00  --inst_subs_given                       false
% 43.45/6.00  --inst_orphan_elimination               true
% 43.45/6.00  --inst_learning_loop_flag               true
% 43.45/6.00  --inst_learning_start                   3000
% 43.45/6.00  --inst_learning_factor                  2
% 43.45/6.00  --inst_start_prop_sim_after_learn       3
% 43.45/6.00  --inst_sel_renew                        solver
% 43.45/6.00  --inst_lit_activity_flag                true
% 43.45/6.00  --inst_restr_to_given                   false
% 43.45/6.00  --inst_activity_threshold               500
% 43.45/6.00  --inst_out_proof                        true
% 43.45/6.00  
% 43.45/6.00  ------ Resolution Options
% 43.45/6.00  
% 43.45/6.00  --resolution_flag                       true
% 43.45/6.00  --res_lit_sel                           adaptive
% 43.45/6.00  --res_lit_sel_side                      none
% 43.45/6.00  --res_ordering                          kbo
% 43.45/6.00  --res_to_prop_solver                    active
% 43.45/6.00  --res_prop_simpl_new                    false
% 43.45/6.00  --res_prop_simpl_given                  true
% 43.45/6.00  --res_passive_queue_type                priority_queues
% 43.45/6.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.45/6.00  --res_passive_queues_freq               [15;5]
% 43.45/6.00  --res_forward_subs                      full
% 43.45/6.00  --res_backward_subs                     full
% 43.45/6.00  --res_forward_subs_resolution           true
% 43.45/6.00  --res_backward_subs_resolution          true
% 43.45/6.00  --res_orphan_elimination                true
% 43.45/6.00  --res_time_limit                        2.
% 43.45/6.00  --res_out_proof                         true
% 43.45/6.00  
% 43.45/6.00  ------ Superposition Options
% 43.45/6.00  
% 43.45/6.00  --superposition_flag                    true
% 43.45/6.00  --sup_passive_queue_type                priority_queues
% 43.45/6.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.45/6.00  --sup_passive_queues_freq               [8;1;4]
% 43.45/6.00  --demod_completeness_check              fast
% 43.45/6.00  --demod_use_ground                      true
% 43.45/6.00  --sup_to_prop_solver                    passive
% 43.45/6.00  --sup_prop_simpl_new                    true
% 43.45/6.00  --sup_prop_simpl_given                  true
% 43.45/6.00  --sup_fun_splitting                     true
% 43.45/6.00  --sup_smt_interval                      50000
% 43.45/6.00  
% 43.45/6.00  ------ Superposition Simplification Setup
% 43.45/6.00  
% 43.45/6.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.45/6.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.45/6.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.45/6.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.45/6.00  --sup_full_triv                         [TrivRules;PropSubs]
% 43.45/6.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.45/6.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.45/6.00  --sup_immed_triv                        [TrivRules]
% 43.45/6.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.00  --sup_immed_bw_main                     []
% 43.45/6.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.45/6.00  --sup_input_triv                        [Unflattening;TrivRules]
% 43.45/6.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.00  --sup_input_bw                          []
% 43.45/6.00  
% 43.45/6.00  ------ Combination Options
% 43.45/6.00  
% 43.45/6.00  --comb_res_mult                         3
% 43.45/6.00  --comb_sup_mult                         2
% 43.45/6.00  --comb_inst_mult                        10
% 43.45/6.00  
% 43.45/6.00  ------ Debug Options
% 43.45/6.00  
% 43.45/6.00  --dbg_backtrace                         false
% 43.45/6.00  --dbg_dump_prop_clauses                 false
% 43.45/6.00  --dbg_dump_prop_clauses_file            -
% 43.45/6.00  --dbg_out_stat                          false
% 43.45/6.00  ------ Parsing...
% 43.45/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.45/6.00  
% 43.45/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.45/6.00  
% 43.45/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.45/6.00  
% 43.45/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.45/6.00  ------ Proving...
% 43.45/6.00  ------ Problem Properties 
% 43.45/6.00  
% 43.45/6.00  
% 43.45/6.00  clauses                                 15
% 43.45/6.00  conjectures                             4
% 43.45/6.00  EPR                                     4
% 43.45/6.00  Horn                                    15
% 43.45/6.00  unary                                   12
% 43.45/6.00  binary                                  3
% 43.45/6.00  lits                                    18
% 43.45/6.00  lits eq                                 12
% 43.45/6.00  fd_pure                                 0
% 43.45/6.00  fd_pseudo                               0
% 43.45/6.00  fd_cond                                 0
% 43.45/6.00  fd_pseudo_cond                          0
% 43.45/6.00  AC symbols                              1
% 43.45/6.00  
% 43.45/6.00  ------ Schedule dynamic 5 is on 
% 43.45/6.00  
% 43.45/6.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.45/6.00  
% 43.45/6.00  
% 43.45/6.00  ------ 
% 43.45/6.00  Current options:
% 43.45/6.00  ------ 
% 43.45/6.00  
% 43.45/6.00  ------ Input Options
% 43.45/6.00  
% 43.45/6.00  --out_options                           all
% 43.45/6.00  --tptp_safe_out                         true
% 43.45/6.00  --problem_path                          ""
% 43.45/6.00  --include_path                          ""
% 43.45/6.00  --clausifier                            res/vclausify_rel
% 43.45/6.00  --clausifier_options                    ""
% 43.45/6.00  --stdin                                 false
% 43.45/6.00  --stats_out                             all
% 43.45/6.00  
% 43.45/6.00  ------ General Options
% 43.45/6.00  
% 43.45/6.00  --fof                                   false
% 43.45/6.00  --time_out_real                         305.
% 43.45/6.00  --time_out_virtual                      -1.
% 43.45/6.00  --symbol_type_check                     false
% 43.45/6.00  --clausify_out                          false
% 43.45/6.00  --sig_cnt_out                           false
% 43.45/6.00  --trig_cnt_out                          false
% 43.45/6.00  --trig_cnt_out_tolerance                1.
% 43.45/6.00  --trig_cnt_out_sk_spl                   false
% 43.45/6.00  --abstr_cl_out                          false
% 43.45/6.00  
% 43.45/6.00  ------ Global Options
% 43.45/6.00  
% 43.45/6.00  --schedule                              default
% 43.45/6.00  --add_important_lit                     false
% 43.45/6.00  --prop_solver_per_cl                    1000
% 43.45/6.00  --min_unsat_core                        false
% 43.45/6.00  --soft_assumptions                      false
% 43.45/6.00  --soft_lemma_size                       3
% 43.45/6.00  --prop_impl_unit_size                   0
% 43.45/6.00  --prop_impl_unit                        []
% 43.45/6.00  --share_sel_clauses                     true
% 43.45/6.00  --reset_solvers                         false
% 43.45/6.00  --bc_imp_inh                            [conj_cone]
% 43.45/6.00  --conj_cone_tolerance                   3.
% 43.45/6.00  --extra_neg_conj                        none
% 43.45/6.00  --large_theory_mode                     true
% 43.45/6.00  --prolific_symb_bound                   200
% 43.45/6.00  --lt_threshold                          2000
% 43.45/6.00  --clause_weak_htbl                      true
% 43.45/6.00  --gc_record_bc_elim                     false
% 43.45/6.00  
% 43.45/6.00  ------ Preprocessing Options
% 43.45/6.00  
% 43.45/6.00  --preprocessing_flag                    true
% 43.45/6.00  --time_out_prep_mult                    0.1
% 43.45/6.00  --splitting_mode                        input
% 43.45/6.00  --splitting_grd                         true
% 43.45/6.00  --splitting_cvd                         false
% 43.45/6.00  --splitting_cvd_svl                     false
% 43.45/6.00  --splitting_nvd                         32
% 43.45/6.00  --sub_typing                            true
% 43.45/6.00  --prep_gs_sim                           true
% 43.45/6.00  --prep_unflatten                        true
% 43.45/6.00  --prep_res_sim                          true
% 43.45/6.00  --prep_upred                            true
% 43.45/6.00  --prep_sem_filter                       exhaustive
% 43.45/6.00  --prep_sem_filter_out                   false
% 43.45/6.00  --pred_elim                             true
% 43.45/6.00  --res_sim_input                         true
% 43.45/6.00  --eq_ax_congr_red                       true
% 43.45/6.00  --pure_diseq_elim                       true
% 43.45/6.00  --brand_transform                       false
% 43.45/6.00  --non_eq_to_eq                          false
% 43.45/6.00  --prep_def_merge                        true
% 43.45/6.00  --prep_def_merge_prop_impl              false
% 43.45/6.00  --prep_def_merge_mbd                    true
% 43.45/6.00  --prep_def_merge_tr_red                 false
% 43.45/6.00  --prep_def_merge_tr_cl                  false
% 43.45/6.00  --smt_preprocessing                     true
% 43.45/6.00  --smt_ac_axioms                         fast
% 43.45/6.00  --preprocessed_out                      false
% 43.45/6.00  --preprocessed_stats                    false
% 43.45/6.00  
% 43.45/6.00  ------ Abstraction refinement Options
% 43.45/6.00  
% 43.45/6.00  --abstr_ref                             []
% 43.45/6.00  --abstr_ref_prep                        false
% 43.45/6.00  --abstr_ref_until_sat                   false
% 43.45/6.00  --abstr_ref_sig_restrict                funpre
% 43.45/6.00  --abstr_ref_af_restrict_to_split_sk     false
% 43.45/6.00  --abstr_ref_under                       []
% 43.45/6.00  
% 43.45/6.00  ------ SAT Options
% 43.45/6.00  
% 43.45/6.00  --sat_mode                              false
% 43.45/6.00  --sat_fm_restart_options                ""
% 43.45/6.00  --sat_gr_def                            false
% 43.45/6.00  --sat_epr_types                         true
% 43.45/6.00  --sat_non_cyclic_types                  false
% 43.45/6.00  --sat_finite_models                     false
% 43.45/6.00  --sat_fm_lemmas                         false
% 43.45/6.00  --sat_fm_prep                           false
% 43.45/6.00  --sat_fm_uc_incr                        true
% 43.45/6.00  --sat_out_model                         small
% 43.45/6.00  --sat_out_clauses                       false
% 43.45/6.00  
% 43.45/6.00  ------ QBF Options
% 43.45/6.00  
% 43.45/6.00  --qbf_mode                              false
% 43.45/6.00  --qbf_elim_univ                         false
% 43.45/6.00  --qbf_dom_inst                          none
% 43.45/6.00  --qbf_dom_pre_inst                      false
% 43.45/6.00  --qbf_sk_in                             false
% 43.45/6.00  --qbf_pred_elim                         true
% 43.45/6.00  --qbf_split                             512
% 43.45/6.00  
% 43.45/6.00  ------ BMC1 Options
% 43.45/6.00  
% 43.45/6.00  --bmc1_incremental                      false
% 43.45/6.00  --bmc1_axioms                           reachable_all
% 43.45/6.00  --bmc1_min_bound                        0
% 43.45/6.00  --bmc1_max_bound                        -1
% 43.45/6.00  --bmc1_max_bound_default                -1
% 43.45/6.00  --bmc1_symbol_reachability              true
% 43.45/6.00  --bmc1_property_lemmas                  false
% 43.45/6.00  --bmc1_k_induction                      false
% 43.45/6.00  --bmc1_non_equiv_states                 false
% 43.45/6.00  --bmc1_deadlock                         false
% 43.45/6.00  --bmc1_ucm                              false
% 43.45/6.00  --bmc1_add_unsat_core                   none
% 43.45/6.00  --bmc1_unsat_core_children              false
% 43.45/6.00  --bmc1_unsat_core_extrapolate_axioms    false
% 43.45/6.00  --bmc1_out_stat                         full
% 43.45/6.00  --bmc1_ground_init                      false
% 43.45/6.00  --bmc1_pre_inst_next_state              false
% 43.45/6.00  --bmc1_pre_inst_state                   false
% 43.45/6.00  --bmc1_pre_inst_reach_state             false
% 43.45/6.00  --bmc1_out_unsat_core                   false
% 43.45/6.00  --bmc1_aig_witness_out                  false
% 43.45/6.00  --bmc1_verbose                          false
% 43.45/6.00  --bmc1_dump_clauses_tptp                false
% 43.45/6.00  --bmc1_dump_unsat_core_tptp             false
% 43.45/6.00  --bmc1_dump_file                        -
% 43.45/6.00  --bmc1_ucm_expand_uc_limit              128
% 43.45/6.00  --bmc1_ucm_n_expand_iterations          6
% 43.45/6.00  --bmc1_ucm_extend_mode                  1
% 43.45/6.00  --bmc1_ucm_init_mode                    2
% 43.45/6.00  --bmc1_ucm_cone_mode                    none
% 43.45/6.00  --bmc1_ucm_reduced_relation_type        0
% 43.45/6.00  --bmc1_ucm_relax_model                  4
% 43.45/6.00  --bmc1_ucm_full_tr_after_sat            true
% 43.45/6.00  --bmc1_ucm_expand_neg_assumptions       false
% 43.45/6.00  --bmc1_ucm_layered_model                none
% 43.45/6.00  --bmc1_ucm_max_lemma_size               10
% 43.45/6.00  
% 43.45/6.00  ------ AIG Options
% 43.45/6.00  
% 43.45/6.00  --aig_mode                              false
% 43.45/6.00  
% 43.45/6.00  ------ Instantiation Options
% 43.45/6.00  
% 43.45/6.00  --instantiation_flag                    true
% 43.45/6.00  --inst_sos_flag                         true
% 43.45/6.00  --inst_sos_phase                        true
% 43.45/6.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.45/6.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.45/6.00  --inst_lit_sel_side                     none
% 43.45/6.00  --inst_solver_per_active                1400
% 43.45/6.00  --inst_solver_calls_frac                1.
% 43.45/6.00  --inst_passive_queue_type               priority_queues
% 43.45/6.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.45/6.00  --inst_passive_queues_freq              [25;2]
% 43.45/6.00  --inst_dismatching                      true
% 43.45/6.00  --inst_eager_unprocessed_to_passive     true
% 43.45/6.00  --inst_prop_sim_given                   true
% 43.45/6.00  --inst_prop_sim_new                     false
% 43.45/6.00  --inst_subs_new                         false
% 43.45/6.00  --inst_eq_res_simp                      false
% 43.45/6.00  --inst_subs_given                       false
% 43.45/6.00  --inst_orphan_elimination               true
% 43.45/6.00  --inst_learning_loop_flag               true
% 43.45/6.00  --inst_learning_start                   3000
% 43.45/6.00  --inst_learning_factor                  2
% 43.45/6.00  --inst_start_prop_sim_after_learn       3
% 43.45/6.00  --inst_sel_renew                        solver
% 43.45/6.00  --inst_lit_activity_flag                true
% 43.45/6.00  --inst_restr_to_given                   false
% 43.45/6.00  --inst_activity_threshold               500
% 43.45/6.00  --inst_out_proof                        true
% 43.45/6.00  
% 43.45/6.00  ------ Resolution Options
% 43.45/6.00  
% 43.45/6.00  --resolution_flag                       false
% 43.45/6.00  --res_lit_sel                           adaptive
% 43.45/6.00  --res_lit_sel_side                      none
% 43.45/6.00  --res_ordering                          kbo
% 43.45/6.00  --res_to_prop_solver                    active
% 43.45/6.00  --res_prop_simpl_new                    false
% 43.45/6.00  --res_prop_simpl_given                  true
% 43.45/6.00  --res_passive_queue_type                priority_queues
% 43.45/6.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.45/6.00  --res_passive_queues_freq               [15;5]
% 43.45/6.00  --res_forward_subs                      full
% 43.45/6.00  --res_backward_subs                     full
% 43.45/6.00  --res_forward_subs_resolution           true
% 43.45/6.00  --res_backward_subs_resolution          true
% 43.45/6.00  --res_orphan_elimination                true
% 43.45/6.00  --res_time_limit                        2.
% 43.45/6.00  --res_out_proof                         true
% 43.45/6.00  
% 43.45/6.00  ------ Superposition Options
% 43.45/6.00  
% 43.45/6.00  --superposition_flag                    true
% 43.45/6.00  --sup_passive_queue_type                priority_queues
% 43.45/6.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.45/6.00  --sup_passive_queues_freq               [8;1;4]
% 43.45/6.00  --demod_completeness_check              fast
% 43.45/6.00  --demod_use_ground                      true
% 43.45/6.00  --sup_to_prop_solver                    passive
% 43.45/6.00  --sup_prop_simpl_new                    true
% 43.45/6.00  --sup_prop_simpl_given                  true
% 43.45/6.00  --sup_fun_splitting                     true
% 43.45/6.00  --sup_smt_interval                      50000
% 43.45/6.00  
% 43.45/6.00  ------ Superposition Simplification Setup
% 43.45/6.00  
% 43.45/6.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.45/6.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.45/6.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.45/6.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.45/6.00  --sup_full_triv                         [TrivRules;PropSubs]
% 43.45/6.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.45/6.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.45/6.00  --sup_immed_triv                        [TrivRules]
% 43.45/6.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.00  --sup_immed_bw_main                     []
% 43.45/6.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.45/6.00  --sup_input_triv                        [Unflattening;TrivRules]
% 43.45/6.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.00  --sup_input_bw                          []
% 43.45/6.00  
% 43.45/6.00  ------ Combination Options
% 43.45/6.00  
% 43.45/6.00  --comb_res_mult                         3
% 43.45/6.00  --comb_sup_mult                         2
% 43.45/6.00  --comb_inst_mult                        10
% 43.45/6.00  
% 43.45/6.00  ------ Debug Options
% 43.45/6.00  
% 43.45/6.00  --dbg_backtrace                         false
% 43.45/6.00  --dbg_dump_prop_clauses                 false
% 43.45/6.00  --dbg_dump_prop_clauses_file            -
% 43.45/6.00  --dbg_out_stat                          false
% 43.45/6.00  
% 43.45/6.00  
% 43.45/6.00  
% 43.45/6.00  
% 43.45/6.00  ------ Proving...
% 43.45/6.00  
% 43.45/6.00  
% 43.45/6.00  % SZS status Theorem for theBenchmark.p
% 43.45/6.00  
% 43.45/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.45/6.00  
% 43.45/6.00  fof(f1,axiom,(
% 43.45/6.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f20,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 43.45/6.00    inference(cnf_transformation,[],[f1])).
% 43.45/6.00  
% 43.45/6.00  fof(f5,axiom,(
% 43.45/6.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f25,plain,(
% 43.45/6.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.45/6.00    inference(cnf_transformation,[],[f5])).
% 43.45/6.00  
% 43.45/6.00  fof(f11,axiom,(
% 43.45/6.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f31,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 43.45/6.00    inference(cnf_transformation,[],[f11])).
% 43.45/6.00  
% 43.45/6.00  fof(f9,axiom,(
% 43.45/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f29,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.45/6.00    inference(cnf_transformation,[],[f9])).
% 43.45/6.00  
% 43.45/6.00  fof(f39,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 43.45/6.00    inference(definition_unfolding,[],[f31,f29])).
% 43.45/6.00  
% 43.45/6.00  fof(f10,axiom,(
% 43.45/6.00    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f30,plain,(
% 43.45/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 43.45/6.00    inference(cnf_transformation,[],[f10])).
% 43.45/6.00  
% 43.45/6.00  fof(f4,axiom,(
% 43.45/6.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f24,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 43.45/6.00    inference(cnf_transformation,[],[f4])).
% 43.45/6.00  
% 43.45/6.00  fof(f12,conjecture,(
% 43.45/6.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f13,negated_conjecture,(
% 43.45/6.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 43.45/6.00    inference(negated_conjecture,[],[f12])).
% 43.45/6.00  
% 43.45/6.00  fof(f15,plain,(
% 43.45/6.00    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 43.45/6.00    inference(ennf_transformation,[],[f13])).
% 43.45/6.00  
% 43.45/6.00  fof(f16,plain,(
% 43.45/6.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 43.45/6.00    inference(flattening,[],[f15])).
% 43.45/6.00  
% 43.45/6.00  fof(f18,plain,(
% 43.45/6.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 43.45/6.00    introduced(choice_axiom,[])).
% 43.45/6.00  
% 43.45/6.00  fof(f19,plain,(
% 43.45/6.00    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 43.45/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f18])).
% 43.45/6.00  
% 43.45/6.00  fof(f32,plain,(
% 43.45/6.00    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 43.45/6.00    inference(cnf_transformation,[],[f19])).
% 43.45/6.00  
% 43.45/6.00  fof(f6,axiom,(
% 43.45/6.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f26,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 43.45/6.00    inference(cnf_transformation,[],[f6])).
% 43.45/6.00  
% 43.45/6.00  fof(f7,axiom,(
% 43.45/6.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f27,plain,(
% 43.45/6.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 43.45/6.00    inference(cnf_transformation,[],[f7])).
% 43.45/6.00  
% 43.45/6.00  fof(f33,plain,(
% 43.45/6.00    r1_xboole_0(sK2,sK0)),
% 43.45/6.00    inference(cnf_transformation,[],[f19])).
% 43.45/6.00  
% 43.45/6.00  fof(f2,axiom,(
% 43.45/6.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f17,plain,(
% 43.45/6.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 43.45/6.00    inference(nnf_transformation,[],[f2])).
% 43.45/6.00  
% 43.45/6.00  fof(f21,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 43.45/6.00    inference(cnf_transformation,[],[f17])).
% 43.45/6.00  
% 43.45/6.00  fof(f37,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 43.45/6.00    inference(definition_unfolding,[],[f21,f29])).
% 43.45/6.00  
% 43.45/6.00  fof(f34,plain,(
% 43.45/6.00    r1_xboole_0(sK3,sK1)),
% 43.45/6.00    inference(cnf_transformation,[],[f19])).
% 43.45/6.00  
% 43.45/6.00  fof(f8,axiom,(
% 43.45/6.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f28,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.45/6.00    inference(cnf_transformation,[],[f8])).
% 43.45/6.00  
% 43.45/6.00  fof(f38,plain,(
% 43.45/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 43.45/6.00    inference(definition_unfolding,[],[f28,f29])).
% 43.45/6.00  
% 43.45/6.00  fof(f3,axiom,(
% 43.45/6.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 43.45/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.00  
% 43.45/6.00  fof(f14,plain,(
% 43.45/6.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 43.45/6.00    inference(ennf_transformation,[],[f3])).
% 43.45/6.00  
% 43.45/6.00  fof(f23,plain,(
% 43.45/6.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 43.45/6.00    inference(cnf_transformation,[],[f14])).
% 43.45/6.00  
% 43.45/6.00  fof(f35,plain,(
% 43.45/6.00    sK1 != sK2),
% 43.45/6.00    inference(cnf_transformation,[],[f19])).
% 43.45/6.00  
% 43.45/6.00  cnf(c_0,plain,
% 43.45/6.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 43.45/6.00      inference(cnf_transformation,[],[f20]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_5,plain,
% 43.45/6.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.45/6.00      inference(cnf_transformation,[],[f25]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_10,plain,
% 43.45/6.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 43.45/6.00      inference(cnf_transformation,[],[f39]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_9,plain,
% 43.45/6.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.45/6.00      inference(cnf_transformation,[],[f30]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_100,plain,
% 43.45/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 43.45/6.00      inference(theory_normalisation,[status(thm)],[c_10,c_9,c_0]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_473,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_5,c_100]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_4,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 43.45/6.00      inference(cnf_transformation,[],[f24]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1147,plain,
% 43.45/6.00      ( k2_xboole_0(X0,X0) = X0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_473,c_4]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_14,negated_conjecture,
% 43.45/6.00      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 43.45/6.00      inference(cnf_transformation,[],[f32]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_99,negated_conjecture,
% 43.45/6.00      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 43.45/6.00      inference(theory_normalisation,[status(thm)],[c_14,c_9,c_0]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_574,plain,
% 43.45/6.00      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_99,c_9]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_693,plain,
% 43.45/6.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_574,c_9]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1215,plain,
% 43.45/6.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK2,sK3) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1147,c_693]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1218,plain,
% 43.45/6.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.00      inference(light_normalisation,[status(thm)],[c_1215,c_99]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1300,plain,
% 43.45/6.00      ( k2_xboole_0(sK1,k2_xboole_0(sK3,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_0,c_1218]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_6,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 43.45/6.00      inference(cnf_transformation,[],[f26]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1432,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1300,c_6]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_274,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_3270,plain,
% 43.45/6.00      ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1218,c_274]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_4394,plain,
% 43.45/6.00      ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1147,c_3270]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1303,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1218,c_6]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2255,plain,
% 43.45/6.00      ( k2_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(sK1,k2_xboole_0(sK0,sK3))) = k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1303,c_4]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2356,plain,
% 43.45/6.00      ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,sK3),sK1) ),
% 43.45/6.00      inference(demodulation,[status(thm)],[c_2255,c_4]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_4422,plain,
% 43.45/6.00      ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.00      inference(light_normalisation,[status(thm)],[c_4394,c_1218,c_2356]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_4472,plain,
% 43.45/6.00      ( k2_xboole_0(k2_xboole_0(sK3,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_0,c_4422]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_690,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_574,c_0]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_826,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_690,c_6]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_79842,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k2_xboole_0(sK3,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK0))) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_4472,c_826]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_413,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_99,c_6]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_7,plain,
% 43.45/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.45/6.00      inference(cnf_transformation,[],[f27]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_647,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_413,c_7]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_652,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 43.45/6.00      inference(demodulation,[status(thm)],[c_647,c_7]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2247,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_0,c_1303]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2259,plain,
% 43.45/6.00      ( k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
% 43.45/6.00      inference(light_normalisation,[status(thm)],[c_2247,c_1432]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2264,plain,
% 43.45/6.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) ),
% 43.45/6.00      inference(demodulation,[status(thm)],[c_2259,c_1303]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_275,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_4662,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1147,c_275]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_80077,plain,
% 43.45/6.00      ( k4_xboole_0(sK2,k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) ),
% 43.45/6.00      inference(demodulation,[status(thm)],[c_79842,c_652,c_2264,c_4662]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_13,negated_conjecture,
% 43.45/6.00      ( r1_xboole_0(sK2,sK0) ),
% 43.45/6.00      inference(cnf_transformation,[],[f33]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_264,plain,
% 43.45/6.00      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 43.45/6.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2,plain,
% 43.45/6.00      ( ~ r1_xboole_0(X0,X1)
% 43.45/6.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.45/6.00      inference(cnf_transformation,[],[f37]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_267,plain,
% 43.45/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 43.45/6.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 43.45/6.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1652,plain,
% 43.45/6.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_264,c_267]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2118,plain,
% 43.45/6.00      ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1652,c_4]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_415,plain,
% 43.45/6.00      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_416,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.45/6.00      inference(light_normalisation,[status(thm)],[c_415,c_5]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_476,plain,
% 43.45/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_100,c_4]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2119,plain,
% 43.45/6.00      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 43.45/6.00      inference(demodulation,[status(thm)],[c_2118,c_416,c_476]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_641,plain,
% 43.45/6.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_416,c_0]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1134,plain,
% 43.45/6.00      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_641,c_6]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1234,plain,
% 43.45/6.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_476,c_416]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1716,plain,
% 43.45/6.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 43.45/6.00      inference(light_normalisation,[status(thm)],[c_1134,c_1234]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1729,plain,
% 43.45/6.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1716,c_7]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1730,plain,
% 43.45/6.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 43.45/6.00      inference(demodulation,[status(thm)],[c_1729,c_4]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1868,plain,
% 43.45/6.00      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_99,c_1730]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_490,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_10626,plain,
% 43.45/6.00      ( k2_xboole_0(sK0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1868,c_490]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_12,negated_conjecture,
% 43.45/6.00      ( r1_xboole_0(sK3,sK1) ),
% 43.45/6.00      inference(cnf_transformation,[],[f34]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_265,plain,
% 43.45/6.00      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 43.45/6.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1651,plain,
% 43.45/6.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_265,c_267]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2057,plain,
% 43.45/6.00      ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1651,c_4]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_2059,plain,
% 43.45/6.00      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 43.45/6.00      inference(demodulation,[status(thm)],[c_2057,c_416,c_476]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_10829,plain,
% 43.45/6.00      ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
% 43.45/6.00      inference(light_normalisation,[status(thm)],[c_10626,c_2059]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_10830,plain,
% 43.45/6.00      ( k2_xboole_0(sK0,sK3) = sK0 ),
% 43.45/6.00      inference(demodulation,[status(thm)],[c_10829,c_416]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_80078,plain,
% 43.45/6.00      ( k4_xboole_0(sK1,k2_xboole_0(sK3,sK0)) = sK2 ),
% 43.45/6.00      inference(light_normalisation,
% 43.45/6.00                [status(thm)],
% 43.45/6.00                [c_80077,c_2119,c_10830]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1230,plain,
% 43.45/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_476,c_9]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1232,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_476,c_0]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_1746,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1232,c_9]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_698,plain,
% 43.45/6.00      ( k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_0,c_693]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_9341,plain,
% 43.45/6.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k2_xboole_0(sK2,sK3) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_1746,c_698]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_9362,plain,
% 43.45/6.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.00      inference(light_normalisation,[status(thm)],[c_9341,c_99]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_276,plain,
% 43.45/6.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 43.45/6.00  
% 43.45/6.00  cnf(c_9552,plain,
% 43.45/6.00      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.00      inference(superposition,[status(thm)],[c_9362,c_276]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1741,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_6,c_1232]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_8095,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_1741]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29467,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X1)),X0),sK1)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X1)),X0),sK1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_9552,c_8095]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1213,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1147,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_484,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_496,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_484,c_7]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15213,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1213,c_496]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5964,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_276,c_1730]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15556,plain,
% 43.45/6.01      ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_15213,c_9,c_5964]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29523,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X0),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_15556,c_8095]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5876,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1213,c_276]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6050,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_5876,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29705,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X0),k1_xboole_0) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_29523,c_6050]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_414,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_417,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_414,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3478,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1213,c_417]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3488,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_3478,c_1147]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_8127,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1213,c_1741]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1725,plain,
% 43.45/6.01      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1716,c_7]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1733,plain,
% 43.45/6.01      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_1725,c_1234]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_8263,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_8127,c_1733,c_4662]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29706,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_29705,c_3488,c_8263]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29838,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(X1,sK0)),sK1),X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK2,X0)))) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_29467,c_29706]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29839,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(X1,sK0)),sK1),X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_29838,c_9362]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_89053,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK0),sK1),sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1230,c_29839]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2550,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sK3) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_417,c_690]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2558,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_2550,c_99]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1302,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,sK3),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1218,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1441,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK0,sK3)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_690,c_1302]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_818,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sK3) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_416,c_690]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_831,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_818,c_99]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_838,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_831,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_893,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_690,c_838]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_650,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_413,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_651,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,sK2) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_650,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_896,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK2,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_893,c_651]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_688,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK3,X0)),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_574,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_702,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_693,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_709,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,X1)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_688,c_693,c_702]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_897,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_896,c_641,c_693,c_709]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1446,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK0,sK3)))) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_1441,c_897]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1447,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK3))) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_1446,c_693,c_1213]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1448,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_1447,c_1213,c_1218]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1556,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_1448]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_410,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3514,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK2,sK0),sK1) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1556,c_410]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3522,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK2,sK0),sK1) = k4_xboole_0(sK0,sK1) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_3514,c_410]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_89356,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_89053,c_2558,c_3522]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7586,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_1230]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_89492,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_89356,c_7586]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24634,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_410,c_7586]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7597,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k2_xboole_0(X3,X2)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_275,c_1230]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24966,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_24634,c_7597]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1750,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK2,sK3) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1232,c_693]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1753,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_1750,c_99]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2043,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1753,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2651,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK3)) = k2_xboole_0(sK3,sK2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_651,c_690]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2652,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_2651,c_99,c_693,c_1147]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2657,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_2652,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2465,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) = k4_xboole_0(sK3,sK2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_99,c_410]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2836,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_2465,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2837,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_2836,c_2558]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3091,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK3,sK2),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_2837,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3097,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK3,sK2),X0)) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_3091,c_2657]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_573,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_4,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_580,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_573,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3098,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_3097,c_580,c_693]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5885,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1753,c_276]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6469,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X1)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_2043,c_2657,c_3098,c_5885]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24734,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),sK1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_6469,c_7586]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24971,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),sK1) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_24966,c_24734]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25010,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(X1,k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK3,X0),sK1))) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_24971,c_24966]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_816,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_690]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6288,plain,
% 43.45/6.01      ( k2_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_816,c_276]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6315,plain,
% 43.45/6.01      ( k2_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_6288,c_698]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25011,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(X1,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0)))) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_25010,c_6315]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25012,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_25011,c_1753]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_85939,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X3),X1),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1746,c_25012]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_86125,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X0),X1),k2_xboole_0(sK1,sK0)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_85939,c_25012]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24733,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),sK1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_5885,c_7586]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24970,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),sK1) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_24966,c_24733]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25013,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X1,k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK3,X0),sK1))) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_24970,c_24966]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25014,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X1,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0)))) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_25013,c_6315]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25015,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,X1)),X2),k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_25014,c_1753]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_88544,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK0,k4_xboole_0(X1,X2))),X3),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,sK0)),k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,sK0)),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_490,c_25015]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_10717,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X3,X2)) = k2_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_490,c_276]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_88840,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_88544,c_10717,c_25012]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_89505,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_89492,c_2558,c_86125,c_88840]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_89881,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_89505,c_0]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_89912,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X1),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_89505,c_7586]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_90001,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X0)) = sP0_iProver_split ),
% 43.45/6.01      inference(splitting,
% 43.45/6.01                [splitting(split),new_symbols(definition,[])],
% 43.45/6.01                [c_89912]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_90027,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,sK0) = sP0_iProver_split ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_89881,c_90001]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_489,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(X0,X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_7,c_100]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_493,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_489,c_7,c_490]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_13640,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_493,c_6]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_13665,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_13640,c_4,c_7,c_1730]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_47336,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_13665]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_86779,plain,
% 43.45/6.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK0)) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1868,c_47336]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_8,plain,
% 43.45/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.45/6.01      inference(cnf_transformation,[],[f38]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_550,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_564,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_550,c_6]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_412,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7331,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_410,c_412]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7388,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_7331,c_410,c_4662]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_22083,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_564,c_564,c_7388]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_88074,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK0)),k4_xboole_0(k4_xboole_0(sK3,sK0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_86779,c_22083]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_88108,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK0)),k4_xboole_0(k4_xboole_0(sK3,sK0),k1_xboole_0)) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_88074,c_86779]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_88109,plain,
% 43.45/6.01      ( k4_xboole_0(sK3,k2_xboole_0(sK0,k4_xboole_0(sK3,k2_xboole_0(sK0,k1_xboole_0)))) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_88108,c_7,c_412,c_641]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_10637,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_490]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_88110,plain,
% 43.45/6.01      ( k4_xboole_0(sK3,k2_xboole_0(sK0,k4_xboole_0(sK3,k1_xboole_0))) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_88109,c_10637]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_88111,plain,
% 43.45/6.01      ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_88110,c_5,c_10830]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_91270,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,sK3),k1_xboole_0) = k2_xboole_0(sK3,sK0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_88111,c_8095]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_91304,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,sK0) = k2_xboole_0(sK0,k1_xboole_0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_91270,c_10830]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_91305,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,sK0) = sK0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_91304,c_416]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_155771,plain,
% 43.45/6.01      ( k4_xboole_0(sP0_iProver_split,sK0) = sK2 ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_1432,c_1432,c_80078,c_90027,c_91305]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15190,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X0,X2)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_476,c_496]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15575,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_15190,c_7,c_1733]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_10644,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_99,c_490]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16303,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,X0),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_15575,c_10644]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16304,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) = sK3 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_16303,c_7,c_416]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_577,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_9,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_578,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_577,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_579,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_578,c_490]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_38307,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,sK2),k2_xboole_0(sK3,sK1)) = k2_xboole_0(k2_xboole_0(X0,sK2),sK3) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_16304,c_579]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24643,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1868,c_7586]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25576,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,sK3),X1)) = k2_xboole_0(k2_xboole_0(sK3,X0),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_24643,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4660,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_416,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12304,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_10644,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15004,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(sK3,k4_xboole_0(sK0,sK2))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1730,c_12304]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12279,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1730,c_10644]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12339,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(sK0,sK2)) = sK3 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_12279,c_416]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15133,plain,
% 43.45/6.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,sK3) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_15004,c_12339]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25632,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),sK3) = k2_xboole_0(X0,k2_xboole_0(sK3,X1)) ),
% 43.45/6.01      inference(demodulation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_25576,c_4660,c_15133,c_24966]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_38821,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,sK2),k2_xboole_0(sK3,sK1)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(demodulation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_38307,c_2652,c_25632,c_29706]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_40499,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK1)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1147,c_38821]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_40613,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK1)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_40499,c_2558]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_40996,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,sK1),sK2) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_40613,c_410]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_41054,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,sK1),sK2) = k4_xboole_0(sK3,sK2) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_40996,c_2465]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12295,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1)) = k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_10644,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_14417,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK3) = k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_12295,c_417]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_14423,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK3) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_14417,c_10644]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_22175,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),k4_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK3))) = k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK3) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_14423,c_22083]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2484,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_410,c_8]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2494,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_2484,c_410]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2495,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_2494,c_412]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_22375,plain,
% 43.45/6.01      ( k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) = k4_xboole_0(k4_xboole_0(X0,sK2),sK3) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_22175,c_7,c_410,c_2495]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_22376,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,sK2),sK3) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_22375,c_99]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_41101,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,sK1),k2_xboole_0(sK1,sK0)) = k4_xboole_0(k4_xboole_0(sK3,sK2),sK3) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_41054,c_22376]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_9964,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),X1),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1232,c_9552]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_10011,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),X1),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_9964,c_9362]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15373,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(X0,sK1),sK2)) = k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_496,c_10644]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15381,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(X0,sK1),sK2)) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_15373,c_10644]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1866,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_4,c_1730]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3777,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1866,c_7]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3785,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_3777,c_7,c_1234]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16403,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK1),sK2),sK3),k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1)) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_15381,c_3785]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16437,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1))) = k1_xboole_0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_16403,c_7]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2486,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_410,c_100]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2492,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_2486,c_4,c_412]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12303,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1)) = k2_xboole_0(X1,k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_10644,c_276]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_14696,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_2492,c_12303]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_14786,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_14696,c_2657]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2653,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_2652,c_651]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4666,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_2653,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_14787,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(demodulation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_14786,c_2652,c_4666,c_6050]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_14857,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_14787,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7224,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2)) = k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(sK1,sK0)),X2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_5885,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6503,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2)) = k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X1)),X2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_6469,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6183,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X0,sK3),X1)) = k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_698,c_9]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6524,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),X1),X2)) = k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X1,sK3),X2)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_6503,c_6183]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7247,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1) = k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X0,sK3),X1)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_7224,c_6524]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_14887,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),X1)) = k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X0,sK3),X1)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_14857,c_7247]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16438,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(X0,sK3),X1))) = k1_xboole_0 ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_16437,c_99,c_14887]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16549,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,sK3),sK2))) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_275,c_16438]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_17382,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,sK1),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1147,c_16549]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_17420,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,sK1),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k1_xboole_0 ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_17382,c_2652]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_18728,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,sK1),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_10011,c_17420]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_41112,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(sK3,sK2),sK3) = k1_xboole_0 ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_41101,c_18728]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3,plain,
% 43.45/6.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 43.45/6.01      inference(cnf_transformation,[],[f23]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_266,plain,
% 43.45/6.01      ( r1_xboole_0(X0,X1) != iProver_top
% 43.45/6.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1017,plain,
% 43.45/6.01      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_264,c_266]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1654,plain,
% 43.45/6.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1017,c_267]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_10650,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_2652,c_490]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16302,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X0),sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_15575,c_10650]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16305,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,sK3))) = sK2 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_16302,c_7,c_416]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_18312,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sK2 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_9,c_16305]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_9553,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),k2_xboole_0(sK1,X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_9362,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3260,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_2652,c_274]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4058,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_3260]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29446,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k2_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_4058,c_8095]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29875,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_29446,c_29706]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29876,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_29875,c_2652]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_45917,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))),sK3)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_9553,c_29876]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4680,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1753,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_9560,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X1)),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_9362,c_4680]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4669,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1218,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5413,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1753,c_4669]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5449,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_5413,c_4669]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2541,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),sK1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1753,c_417]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4729,plain,
% 43.45/6.01      ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_275,c_690]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3306,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_274,c_690]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4744,plain,
% 43.45/6.01      ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_4729,c_3306]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5450,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_5449,c_1147,c_2541,c_4744]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1440,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1147,c_1302]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1449,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_1440,c_1218]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1562,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_0,c_1449]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7781,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK3,sK0),k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1562,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7795,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK3,sK0),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_7781,c_2657]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4671,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1213,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4673,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK3,sK0),k2_xboole_0(sK1,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1300,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7796,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_7795,c_3098,c_4671,c_4673]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_9561,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_9560,c_5450,c_7796]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_46079,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,X0))),sK3)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_45917,c_9561]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7660,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1230,c_276]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_46080,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(k2_xboole_0(sK2,sK0),sK3))) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_46079,c_4744,c_6183,c_7247,c_7660]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_692,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_574,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5769,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0)))) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_692,c_692,c_2657,c_3098]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12272,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_10644,c_5769]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29473,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2)) = k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_12272,c_8095]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29824,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2)) = k2_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK2,sK3)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_29473,c_29706]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4683,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_2558,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5496,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_4,c_4683]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_5550,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK1,sK0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_5496,c_4683]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12658,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2) = k4_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),sK2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_12272,c_410]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6182,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),sK2) = k4_xboole_0(k2_xboole_0(X0,sK3),sK2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_698,c_410]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12683,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,sK2)),sK2) = k4_xboole_0(k2_xboole_0(X0,sK3),sK2) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_12658,c_6182]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_29825,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK0,X0)),k4_xboole_0(k2_xboole_0(X0,sK3),sK2)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_29824,c_99,c_5550,c_12683]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_31332,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK3),sK3),sK2)) = k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_3270,c_29825]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_31526,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)),k4_xboole_0(sK0,sK2)) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_31332,c_4422,c_10830]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_7656,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1230,c_0]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25231,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK3),X1)) = k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_4669,c_7656]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_25465,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(sK0,X1)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_25231,c_4669,c_10830]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_31527,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2))) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_31526,c_4744,c_6183,c_25465]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_31528,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_31527,c_10830]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3256,plain,
% 43.45/6.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_4,c_274]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_31529,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_31528,c_1232,c_3256]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_46081,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,sK3))) = k2_xboole_0(sK1,sK0) ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_46080,c_413,c_10830,c_31529]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_46163,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,sK3)),sK2) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_46081,c_410]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_46221,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,sK3)),sK2) = k4_xboole_0(sK3,sK2) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_46163,c_2465]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_46296,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK2,sK3)),k2_xboole_0(sK2,X0)) = k4_xboole_0(k4_xboole_0(sK3,sK2),X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_46221,c_7]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24808,plain,
% 43.45/6.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_7586,c_496]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24876,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_24808,c_7586]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_46347,plain,
% 43.45/6.01      ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_46296,c_7,c_24876]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_81677,plain,
% 43.45/6.01      ( k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(X1,sK3))))) = k4_xboole_0(sK0,sK2) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_18312,c_46347]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_81772,plain,
% 43.45/6.01      ( k4_xboole_0(sK3,sK2) = k4_xboole_0(sK0,sK2) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_81677,c_18312]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_153521,plain,
% 43.45/6.01      ( k4_xboole_0(sK0,k4_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_1654,c_1654,c_81772]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_153548,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(sK3,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK3,sK2),k1_xboole_0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_153521,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_10674,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k4_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k4_xboole_0(X1,sK1)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1753,c_490]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_84380,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k4_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(k4_xboole_0(X1,sK1),sK0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_10674,c_29706]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_84409,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(k4_xboole_0(sK3,sK1),sK0)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k1_xboole_0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1868,c_84380]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_85598,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK3,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k1_xboole_0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_84409,c_2059]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4672,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1232,c_275]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_85599,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(sK3,X0),sK0) = sK0 ),
% 43.45/6.01      inference(demodulation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_85598,c_4672,c_8263,c_10830]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_153564,plain,
% 43.45/6.01      ( k4_xboole_0(sK3,sK2) = sK0 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_153548,c_416,c_85599]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_155248,plain,
% 43.45/6.01      ( k4_xboole_0(sK0,sK3) = k1_xboole_0 ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_41112,c_41112,c_153564]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_155291,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_155248,c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_155314,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k1_xboole_0) = sK0 ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_155291,c_91305]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_155315,plain,
% 43.45/6.01      ( sK0 = sK3 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_155314,c_416]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_155772,plain,
% 43.45/6.01      ( k4_xboole_0(sP0_iProver_split,sK3) = sK2 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_155771,c_155315]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_700,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_4,c_693]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_706,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_700,c_693]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_155823,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sP0_iProver_split)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_155772,c_706]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_89965,plain,
% 43.45/6.01      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_89505,c_12303]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_90425,plain,
% 43.45/6.01      ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK2))) = sP0_iProver_split ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_89965,c_2653,c_90027]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_90426,plain,
% 43.45/6.01      ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK0,sK1),sK2))) = sP0_iProver_split ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_90425,c_6]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12280,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1866,c_10644]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12338,plain,
% 43.45/6.01      ( k2_xboole_0(sK3,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = sK3 ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_12280,c_7,c_416]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_90427,plain,
% 43.45/6.01      ( k2_xboole_0(sP0_iProver_split,sK3) = sP0_iProver_split ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_90426,c_7,c_12338]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_91389,plain,
% 43.45/6.01      ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sP0_iProver_split) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_90427,c_816]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_91395,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,sP0_iProver_split) = k2_xboole_0(sP0_iProver_split,sP0_iProver_split) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_91389,c_90027]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_91396,plain,
% 43.45/6.01      ( k2_xboole_0(sK2,sP0_iProver_split) = sP0_iProver_split ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_91395,c_1147]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_91390,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sP0_iProver_split)) = k2_xboole_0(sK2,sP0_iProver_split) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_90427,c_698]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_91397,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sP0_iProver_split)) = sP0_iProver_split ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_91396,c_91390]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_155839,plain,
% 43.45/6.01      ( k2_xboole_0(sK1,sK3) = sP0_iProver_split ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_155823,c_1448,c_91397,c_155315]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_157156,plain,
% 43.45/6.01      ( k4_xboole_0(sP0_iProver_split,sK3) = k4_xboole_0(sK1,sK3) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_155839,c_6]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1016,plain,
% 43.45/6.01      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_265,c_266]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1653,plain,
% 43.45/6.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1016,c_267]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_151792,plain,
% 43.45/6.01      ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK3),sK1),k1_xboole_0) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1653,c_412]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_151805,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(sK1,sK3),k2_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK1,sK3),k2_xboole_0(X0,k1_xboole_0)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1653,c_579]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_151809,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(sK1,sK3),k2_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK1,sK3),X0) ),
% 43.45/6.01      inference(light_normalisation,[status(thm)],[c_151805,c_416]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_151810,plain,
% 43.45/6.01      ( k2_xboole_0(k4_xboole_0(sK1,sK3),X0) = k2_xboole_0(sK1,X0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_151809,c_7586]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_151815,plain,
% 43.45/6.01      ( k4_xboole_0(k2_xboole_0(sK1,sK1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
% 43.45/6.01      inference(demodulation,[status(thm)],[c_151792,c_1653,c_151810]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_151816,plain,
% 43.45/6.01      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 43.45/6.01      inference(demodulation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_151815,c_5,c_7,c_416,c_1147]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_157275,plain,
% 43.45/6.01      ( sK2 = sK1 ),
% 43.45/6.01      inference(light_normalisation,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_157156,c_151816,c_155772]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_103,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_337,plain,
% 43.45/6.01      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 43.45/6.01      inference(instantiation,[status(thm)],[c_103]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_404,plain,
% 43.45/6.01      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 43.45/6.01      inference(instantiation,[status(thm)],[c_337]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_26362,plain,
% 43.45/6.01      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 43.45/6.01      inference(instantiation,[status(thm)],[c_404]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_102,plain,( X0 = X0 ),theory(equality) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_402,plain,
% 43.45/6.01      ( sK1 = sK1 ),
% 43.45/6.01      inference(instantiation,[status(thm)],[c_102]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_11,negated_conjecture,
% 43.45/6.01      ( sK1 != sK2 ),
% 43.45/6.01      inference(cnf_transformation,[],[f35]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(contradiction,plain,
% 43.45/6.01      ( $false ),
% 43.45/6.01      inference(minisat,[status(thm)],[c_157275,c_26362,c_402,c_11]) ).
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.45/6.01  
% 43.45/6.01  ------                               Statistics
% 43.45/6.01  
% 43.45/6.01  ------ General
% 43.45/6.01  
% 43.45/6.01  abstr_ref_over_cycles:                  0
% 43.45/6.01  abstr_ref_under_cycles:                 0
% 43.45/6.01  gc_basic_clause_elim:                   0
% 43.45/6.01  forced_gc_time:                         0
% 43.45/6.01  parsing_time:                           0.015
% 43.45/6.01  unif_index_cands_time:                  0.
% 43.45/6.01  unif_index_add_time:                    0.
% 43.45/6.01  orderings_time:                         0.
% 43.45/6.01  out_proof_time:                         0.019
% 43.45/6.01  total_time:                             5.281
% 43.45/6.01  num_of_symbols:                         46
% 43.45/6.01  num_of_terms:                           259479
% 43.45/6.01  
% 43.45/6.01  ------ Preprocessing
% 43.45/6.01  
% 43.45/6.01  num_of_splits:                          0
% 43.45/6.01  num_of_split_atoms:                     7
% 43.45/6.01  num_of_reused_defs:                     0
% 43.45/6.01  num_eq_ax_congr_red:                    0
% 43.45/6.01  num_of_sem_filtered_clauses:            1
% 43.45/6.01  num_of_subtypes:                        0
% 43.45/6.01  monotx_restored_types:                  0
% 43.45/6.01  sat_num_of_epr_types:                   0
% 43.45/6.01  sat_num_of_non_cyclic_types:            0
% 43.45/6.01  sat_guarded_non_collapsed_types:        0
% 43.45/6.01  num_pure_diseq_elim:                    0
% 43.45/6.01  simp_replaced_by:                       0
% 43.45/6.01  res_preprocessed:                       56
% 43.45/6.01  prep_upred:                             0
% 43.45/6.01  prep_unflattend:                        0
% 43.45/6.01  smt_new_axioms:                         0
% 43.45/6.01  pred_elim_cands:                        1
% 43.45/6.01  pred_elim:                              0
% 43.45/6.01  pred_elim_cl:                           0
% 43.45/6.01  pred_elim_cycles:                       1
% 43.45/6.01  merged_defs:                            6
% 43.45/6.01  merged_defs_ncl:                        0
% 43.45/6.01  bin_hyper_res:                          6
% 43.45/6.01  prep_cycles:                            3
% 43.45/6.01  pred_elim_time:                         0.
% 43.45/6.01  splitting_time:                         0.
% 43.45/6.01  sem_filter_time:                        0.
% 43.45/6.01  monotx_time:                            0.
% 43.45/6.01  subtype_inf_time:                       0.
% 43.45/6.01  
% 43.45/6.01  ------ Problem properties
% 43.45/6.01  
% 43.45/6.01  clauses:                                15
% 43.45/6.01  conjectures:                            4
% 43.45/6.01  epr:                                    4
% 43.45/6.01  horn:                                   15
% 43.45/6.01  ground:                                 4
% 43.45/6.01  unary:                                  12
% 43.45/6.01  binary:                                 3
% 43.45/6.01  lits:                                   18
% 43.45/6.01  lits_eq:                                12
% 43.45/6.01  fd_pure:                                0
% 43.45/6.01  fd_pseudo:                              0
% 43.45/6.01  fd_cond:                                0
% 43.45/6.01  fd_pseudo_cond:                         0
% 43.45/6.01  ac_symbols:                             1
% 43.45/6.01  
% 43.45/6.01  ------ Propositional Solver
% 43.45/6.01  
% 43.45/6.01  prop_solver_calls:                      37
% 43.45/6.01  prop_fast_solver_calls:                 888
% 43.45/6.01  smt_solver_calls:                       0
% 43.45/6.01  smt_fast_solver_calls:                  0
% 43.45/6.01  prop_num_of_clauses:                    35096
% 43.45/6.01  prop_preprocess_simplified:             34267
% 43.45/6.01  prop_fo_subsumed:                       0
% 43.45/6.01  prop_solver_time:                       0.
% 43.45/6.01  smt_solver_time:                        0.
% 43.45/6.01  smt_fast_solver_time:                   0.
% 43.45/6.01  prop_fast_solver_time:                  0.
% 43.45/6.01  prop_unsat_core_time:                   0.003
% 43.45/6.01  
% 43.45/6.01  ------ QBF
% 43.45/6.01  
% 43.45/6.01  qbf_q_res:                              0
% 43.45/6.01  qbf_num_tautologies:                    0
% 43.45/6.01  qbf_prep_cycles:                        0
% 43.45/6.01  
% 43.45/6.01  ------ BMC1
% 43.45/6.01  
% 43.45/6.01  bmc1_current_bound:                     -1
% 43.45/6.01  bmc1_last_solved_bound:                 -1
% 43.45/6.01  bmc1_unsat_core_size:                   -1
% 43.45/6.01  bmc1_unsat_core_parents_size:           -1
% 43.45/6.01  bmc1_merge_next_fun:                    0
% 43.45/6.01  bmc1_unsat_core_clauses_time:           0.
% 43.45/6.01  
% 43.45/6.01  ------ Instantiation
% 43.45/6.01  
% 43.45/6.01  inst_num_of_clauses:                    8713
% 43.45/6.01  inst_num_in_passive:                    6416
% 43.45/6.01  inst_num_in_active:                     1575
% 43.45/6.01  inst_num_in_unprocessed:                722
% 43.45/6.01  inst_num_of_loops:                      2600
% 43.45/6.01  inst_num_of_learning_restarts:          0
% 43.45/6.01  inst_num_moves_active_passive:          1017
% 43.45/6.01  inst_lit_activity:                      0
% 43.45/6.01  inst_lit_activity_moves:                2
% 43.45/6.01  inst_num_tautologies:                   0
% 43.45/6.01  inst_num_prop_implied:                  0
% 43.45/6.01  inst_num_existing_simplified:           0
% 43.45/6.01  inst_num_eq_res_simplified:             0
% 43.45/6.01  inst_num_child_elim:                    0
% 43.45/6.01  inst_num_of_dismatching_blockings:      11021
% 43.45/6.01  inst_num_of_non_proper_insts:           7797
% 43.45/6.01  inst_num_of_duplicates:                 0
% 43.45/6.01  inst_inst_num_from_inst_to_res:         0
% 43.45/6.01  inst_dismatching_checking_time:         0.
% 43.45/6.01  
% 43.45/6.01  ------ Resolution
% 43.45/6.01  
% 43.45/6.01  res_num_of_clauses:                     0
% 43.45/6.01  res_num_in_passive:                     0
% 43.45/6.01  res_num_in_active:                      0
% 43.45/6.01  res_num_of_loops:                       59
% 43.45/6.01  res_forward_subset_subsumed:            3908
% 43.45/6.01  res_backward_subset_subsumed:           0
% 43.45/6.01  res_forward_subsumed:                   0
% 43.45/6.01  res_backward_subsumed:                  0
% 43.45/6.01  res_forward_subsumption_resolution:     0
% 43.45/6.01  res_backward_subsumption_resolution:    0
% 43.45/6.01  res_clause_to_clause_subsumption:       154286
% 43.45/6.01  res_orphan_elimination:                 0
% 43.45/6.01  res_tautology_del:                      549
% 43.45/6.01  res_num_eq_res_simplified:              0
% 43.45/6.01  res_num_sel_changes:                    0
% 43.45/6.01  res_moves_from_active_to_pass:          0
% 43.45/6.01  
% 43.45/6.01  ------ Superposition
% 43.45/6.01  
% 43.45/6.01  sup_time_total:                         0.
% 43.45/6.01  sup_time_generating:                    0.
% 43.45/6.01  sup_time_sim_full:                      0.
% 43.45/6.01  sup_time_sim_immed:                     0.
% 43.45/6.01  
% 43.45/6.01  sup_num_of_clauses:                     11184
% 43.45/6.01  sup_num_in_active:                      409
% 43.45/6.01  sup_num_in_passive:                     10775
% 43.45/6.01  sup_num_of_loops:                       519
% 43.45/6.01  sup_fw_superposition:                   24966
% 43.45/6.01  sup_bw_superposition:                   20598
% 43.45/6.01  sup_immediate_simplified:               31875
% 43.45/6.01  sup_given_eliminated:                   22
% 43.45/6.01  comparisons_done:                       0
% 43.45/6.01  comparisons_avoided:                    0
% 43.45/6.01  
% 43.45/6.01  ------ Simplifications
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  sim_fw_subset_subsumed:                 1
% 43.45/6.01  sim_bw_subset_subsumed:                 0
% 43.45/6.01  sim_fw_subsumed:                        3680
% 43.45/6.01  sim_bw_subsumed:                        241
% 43.45/6.01  sim_fw_subsumption_res:                 0
% 43.45/6.01  sim_bw_subsumption_res:                 0
% 43.45/6.01  sim_tautology_del:                      0
% 43.45/6.01  sim_eq_tautology_del:                   10259
% 43.45/6.01  sim_eq_res_simp:                        18
% 43.45/6.01  sim_fw_demodulated:                     29033
% 43.45/6.01  sim_bw_demodulated:                     706
% 43.45/6.01  sim_light_normalised:                   16981
% 43.45/6.01  sim_joinable_taut:                      323
% 43.45/6.01  sim_joinable_simp:                      0
% 43.45/6.01  sim_ac_normalised:                      0
% 43.45/6.01  sim_smt_subsumption:                    0
% 43.45/6.01  
%------------------------------------------------------------------------------
