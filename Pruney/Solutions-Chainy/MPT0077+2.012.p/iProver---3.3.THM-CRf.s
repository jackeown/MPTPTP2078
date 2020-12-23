%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:38 EST 2020

% Result     : Theorem 12.03s
% Output     : CNFRefutation 12.03s
% Verified   : 
% Statistics : Number of formulae       :  105 (1241 expanded)
%              Number of clauses        :   74 ( 490 expanded)
%              Number of leaves         :   10 ( 314 expanded)
%              Depth                    :   20
%              Number of atoms          :  190 (1858 expanded)
%              Number of equality atoms :  128 (1275 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f30,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f24])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_332,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_333,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_981,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_332,c_333])).

cnf(c_1245,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_981,c_333])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1258,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1245,c_7])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1259,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_1258,c_5])).

cnf(c_1314,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1259,c_7])).

cnf(c_1315,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_1314,c_5])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_601,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_614,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_601,c_6])).

cnf(c_5116,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_1315,c_614])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_331,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_982,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_331,c_333])).

cnf(c_1247,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_982,c_333])).

cnf(c_605,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_609,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_605,c_6])).

cnf(c_4024,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1247,c_609])).

cnf(c_532,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_535,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_538,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_535,c_6])).

cnf(c_4194,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_4024,c_532,c_538])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_335,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_5])).

cnf(c_534,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_335,c_6])).

cnf(c_703,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_534])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_705,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_534])).

cnf(c_711,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_705,c_335])).

cnf(c_733,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_703,c_711])).

cnf(c_800,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_733,c_6])).

cnf(c_4709,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4194,c_800])).

cnf(c_4812,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4709,c_7])).

cnf(c_4813,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_4812,c_5])).

cnf(c_5194,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_5116,c_4813])).

cnf(c_4809,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_4709,c_609])).

cnf(c_4842,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_4809,c_532])).

cnf(c_5195,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k4_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_5194,c_4842])).

cnf(c_5196,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_5195,c_5,c_335])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_334,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5704,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4842,c_334])).

cnf(c_23356,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_5704])).

cnf(c_23522,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23356,c_335])).

cnf(c_23523,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_23522])).

cnf(c_4025,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1245,c_609])).

cnf(c_4193,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_4025,c_532,c_538])).

cnf(c_4644,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(X0,sK2))) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4193])).

cnf(c_4922,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_4644,c_4842])).

cnf(c_1257,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1245,c_6])).

cnf(c_1260,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1257,c_711])).

cnf(c_606,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_607,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_606,c_6])).

cnf(c_608,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_607,c_6])).

cnf(c_3051,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1260,c_608])).

cnf(c_536,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_3170,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_3051,c_536])).

cnf(c_4957,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_4922,c_3170])).

cnf(c_5003,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4957,c_4813])).

cnf(c_713,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_711,c_534])).

cnf(c_5004,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5003,c_713,c_4842])).

cnf(c_1208,plain,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1210,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_345,plain,
    ( r1_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_346,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_14,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != iProver_top
    | r1_xboole_0(sK0,sK2) != iProver_top
    | r1_xboole_0(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23523,c_5004,c_4709,c_1210,c_346,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 12.03/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.03/2.00  
% 12.03/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.03/2.00  
% 12.03/2.00  ------  iProver source info
% 12.03/2.00  
% 12.03/2.00  git: date: 2020-06-30 10:37:57 +0100
% 12.03/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.03/2.00  git: non_committed_changes: false
% 12.03/2.00  git: last_make_outside_of_git: false
% 12.03/2.00  
% 12.03/2.00  ------ 
% 12.03/2.00  
% 12.03/2.00  ------ Input Options
% 12.03/2.00  
% 12.03/2.00  --out_options                           all
% 12.03/2.00  --tptp_safe_out                         true
% 12.03/2.00  --problem_path                          ""
% 12.03/2.00  --include_path                          ""
% 12.03/2.00  --clausifier                            res/vclausify_rel
% 12.03/2.00  --clausifier_options                    ""
% 12.03/2.00  --stdin                                 false
% 12.03/2.00  --stats_out                             all
% 12.03/2.00  
% 12.03/2.00  ------ General Options
% 12.03/2.00  
% 12.03/2.00  --fof                                   false
% 12.03/2.00  --time_out_real                         305.
% 12.03/2.00  --time_out_virtual                      -1.
% 12.03/2.00  --symbol_type_check                     false
% 12.03/2.00  --clausify_out                          false
% 12.03/2.00  --sig_cnt_out                           false
% 12.03/2.00  --trig_cnt_out                          false
% 12.03/2.00  --trig_cnt_out_tolerance                1.
% 12.03/2.00  --trig_cnt_out_sk_spl                   false
% 12.03/2.00  --abstr_cl_out                          false
% 12.03/2.00  
% 12.03/2.00  ------ Global Options
% 12.03/2.00  
% 12.03/2.00  --schedule                              default
% 12.03/2.00  --add_important_lit                     false
% 12.03/2.00  --prop_solver_per_cl                    1000
% 12.03/2.00  --min_unsat_core                        false
% 12.03/2.00  --soft_assumptions                      false
% 12.03/2.00  --soft_lemma_size                       3
% 12.03/2.00  --prop_impl_unit_size                   0
% 12.03/2.00  --prop_impl_unit                        []
% 12.03/2.00  --share_sel_clauses                     true
% 12.03/2.00  --reset_solvers                         false
% 12.03/2.00  --bc_imp_inh                            [conj_cone]
% 12.03/2.00  --conj_cone_tolerance                   3.
% 12.03/2.00  --extra_neg_conj                        none
% 12.03/2.00  --large_theory_mode                     true
% 12.03/2.00  --prolific_symb_bound                   200
% 12.03/2.00  --lt_threshold                          2000
% 12.03/2.00  --clause_weak_htbl                      true
% 12.03/2.00  --gc_record_bc_elim                     false
% 12.03/2.00  
% 12.03/2.00  ------ Preprocessing Options
% 12.03/2.00  
% 12.03/2.00  --preprocessing_flag                    true
% 12.03/2.00  --time_out_prep_mult                    0.1
% 12.03/2.00  --splitting_mode                        input
% 12.03/2.00  --splitting_grd                         true
% 12.03/2.00  --splitting_cvd                         false
% 12.03/2.00  --splitting_cvd_svl                     false
% 12.03/2.00  --splitting_nvd                         32
% 12.03/2.00  --sub_typing                            true
% 12.03/2.00  --prep_gs_sim                           true
% 12.03/2.00  --prep_unflatten                        true
% 12.03/2.00  --prep_res_sim                          true
% 12.03/2.00  --prep_upred                            true
% 12.03/2.00  --prep_sem_filter                       exhaustive
% 12.03/2.00  --prep_sem_filter_out                   false
% 12.03/2.00  --pred_elim                             true
% 12.03/2.00  --res_sim_input                         true
% 12.03/2.00  --eq_ax_congr_red                       true
% 12.03/2.00  --pure_diseq_elim                       true
% 12.03/2.00  --brand_transform                       false
% 12.03/2.00  --non_eq_to_eq                          false
% 12.03/2.00  --prep_def_merge                        true
% 12.03/2.00  --prep_def_merge_prop_impl              false
% 12.03/2.00  --prep_def_merge_mbd                    true
% 12.03/2.00  --prep_def_merge_tr_red                 false
% 12.03/2.00  --prep_def_merge_tr_cl                  false
% 12.03/2.00  --smt_preprocessing                     true
% 12.03/2.00  --smt_ac_axioms                         fast
% 12.03/2.00  --preprocessed_out                      false
% 12.03/2.00  --preprocessed_stats                    false
% 12.03/2.00  
% 12.03/2.00  ------ Abstraction refinement Options
% 12.03/2.00  
% 12.03/2.00  --abstr_ref                             []
% 12.03/2.00  --abstr_ref_prep                        false
% 12.03/2.00  --abstr_ref_until_sat                   false
% 12.03/2.00  --abstr_ref_sig_restrict                funpre
% 12.03/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 12.03/2.00  --abstr_ref_under                       []
% 12.03/2.00  
% 12.03/2.00  ------ SAT Options
% 12.03/2.00  
% 12.03/2.00  --sat_mode                              false
% 12.03/2.00  --sat_fm_restart_options                ""
% 12.03/2.00  --sat_gr_def                            false
% 12.03/2.00  --sat_epr_types                         true
% 12.03/2.00  --sat_non_cyclic_types                  false
% 12.03/2.00  --sat_finite_models                     false
% 12.03/2.00  --sat_fm_lemmas                         false
% 12.03/2.00  --sat_fm_prep                           false
% 12.03/2.00  --sat_fm_uc_incr                        true
% 12.03/2.00  --sat_out_model                         small
% 12.03/2.00  --sat_out_clauses                       false
% 12.03/2.00  
% 12.03/2.00  ------ QBF Options
% 12.03/2.00  
% 12.03/2.00  --qbf_mode                              false
% 12.03/2.00  --qbf_elim_univ                         false
% 12.03/2.00  --qbf_dom_inst                          none
% 12.03/2.00  --qbf_dom_pre_inst                      false
% 12.03/2.00  --qbf_sk_in                             false
% 12.03/2.00  --qbf_pred_elim                         true
% 12.03/2.00  --qbf_split                             512
% 12.03/2.00  
% 12.03/2.00  ------ BMC1 Options
% 12.03/2.00  
% 12.03/2.00  --bmc1_incremental                      false
% 12.03/2.00  --bmc1_axioms                           reachable_all
% 12.03/2.00  --bmc1_min_bound                        0
% 12.03/2.00  --bmc1_max_bound                        -1
% 12.03/2.00  --bmc1_max_bound_default                -1
% 12.03/2.00  --bmc1_symbol_reachability              true
% 12.03/2.00  --bmc1_property_lemmas                  false
% 12.03/2.00  --bmc1_k_induction                      false
% 12.03/2.00  --bmc1_non_equiv_states                 false
% 12.03/2.00  --bmc1_deadlock                         false
% 12.03/2.00  --bmc1_ucm                              false
% 12.03/2.00  --bmc1_add_unsat_core                   none
% 12.03/2.00  --bmc1_unsat_core_children              false
% 12.03/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 12.03/2.00  --bmc1_out_stat                         full
% 12.03/2.00  --bmc1_ground_init                      false
% 12.03/2.00  --bmc1_pre_inst_next_state              false
% 12.03/2.00  --bmc1_pre_inst_state                   false
% 12.03/2.00  --bmc1_pre_inst_reach_state             false
% 12.03/2.00  --bmc1_out_unsat_core                   false
% 12.03/2.00  --bmc1_aig_witness_out                  false
% 12.03/2.00  --bmc1_verbose                          false
% 12.03/2.00  --bmc1_dump_clauses_tptp                false
% 12.03/2.00  --bmc1_dump_unsat_core_tptp             false
% 12.03/2.00  --bmc1_dump_file                        -
% 12.03/2.00  --bmc1_ucm_expand_uc_limit              128
% 12.03/2.00  --bmc1_ucm_n_expand_iterations          6
% 12.03/2.00  --bmc1_ucm_extend_mode                  1
% 12.03/2.00  --bmc1_ucm_init_mode                    2
% 12.03/2.00  --bmc1_ucm_cone_mode                    none
% 12.03/2.00  --bmc1_ucm_reduced_relation_type        0
% 12.03/2.00  --bmc1_ucm_relax_model                  4
% 12.03/2.00  --bmc1_ucm_full_tr_after_sat            true
% 12.03/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 12.03/2.00  --bmc1_ucm_layered_model                none
% 12.03/2.00  --bmc1_ucm_max_lemma_size               10
% 12.03/2.00  
% 12.03/2.00  ------ AIG Options
% 12.03/2.00  
% 12.03/2.00  --aig_mode                              false
% 12.03/2.00  
% 12.03/2.00  ------ Instantiation Options
% 12.03/2.00  
% 12.03/2.00  --instantiation_flag                    true
% 12.03/2.00  --inst_sos_flag                         true
% 12.03/2.00  --inst_sos_phase                        true
% 12.03/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.03/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.03/2.00  --inst_lit_sel_side                     num_symb
% 12.03/2.00  --inst_solver_per_active                1400
% 12.03/2.00  --inst_solver_calls_frac                1.
% 12.03/2.00  --inst_passive_queue_type               priority_queues
% 12.03/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.03/2.00  --inst_passive_queues_freq              [25;2]
% 12.03/2.00  --inst_dismatching                      true
% 12.03/2.00  --inst_eager_unprocessed_to_passive     true
% 12.03/2.00  --inst_prop_sim_given                   true
% 12.03/2.00  --inst_prop_sim_new                     false
% 12.03/2.00  --inst_subs_new                         false
% 12.03/2.00  --inst_eq_res_simp                      false
% 12.03/2.00  --inst_subs_given                       false
% 12.03/2.00  --inst_orphan_elimination               true
% 12.03/2.00  --inst_learning_loop_flag               true
% 12.03/2.00  --inst_learning_start                   3000
% 12.03/2.00  --inst_learning_factor                  2
% 12.03/2.00  --inst_start_prop_sim_after_learn       3
% 12.03/2.00  --inst_sel_renew                        solver
% 12.03/2.00  --inst_lit_activity_flag                true
% 12.03/2.00  --inst_restr_to_given                   false
% 12.03/2.00  --inst_activity_threshold               500
% 12.03/2.00  --inst_out_proof                        true
% 12.03/2.00  
% 12.03/2.00  ------ Resolution Options
% 12.03/2.00  
% 12.03/2.00  --resolution_flag                       true
% 12.03/2.00  --res_lit_sel                           adaptive
% 12.03/2.00  --res_lit_sel_side                      none
% 12.03/2.00  --res_ordering                          kbo
% 12.03/2.00  --res_to_prop_solver                    active
% 12.03/2.00  --res_prop_simpl_new                    false
% 12.03/2.00  --res_prop_simpl_given                  true
% 12.03/2.00  --res_passive_queue_type                priority_queues
% 12.03/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.03/2.00  --res_passive_queues_freq               [15;5]
% 12.03/2.00  --res_forward_subs                      full
% 12.03/2.00  --res_backward_subs                     full
% 12.03/2.00  --res_forward_subs_resolution           true
% 12.03/2.00  --res_backward_subs_resolution          true
% 12.03/2.00  --res_orphan_elimination                true
% 12.03/2.00  --res_time_limit                        2.
% 12.03/2.00  --res_out_proof                         true
% 12.03/2.00  
% 12.03/2.00  ------ Superposition Options
% 12.03/2.00  
% 12.03/2.00  --superposition_flag                    true
% 12.03/2.00  --sup_passive_queue_type                priority_queues
% 12.03/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.03/2.00  --sup_passive_queues_freq               [8;1;4]
% 12.03/2.00  --demod_completeness_check              fast
% 12.03/2.00  --demod_use_ground                      true
% 12.03/2.00  --sup_to_prop_solver                    passive
% 12.03/2.00  --sup_prop_simpl_new                    true
% 12.03/2.00  --sup_prop_simpl_given                  true
% 12.03/2.00  --sup_fun_splitting                     true
% 12.03/2.00  --sup_smt_interval                      50000
% 12.03/2.00  
% 12.03/2.00  ------ Superposition Simplification Setup
% 12.03/2.00  
% 12.03/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.03/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.03/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.03/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.03/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 12.03/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.03/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.03/2.00  --sup_immed_triv                        [TrivRules]
% 12.03/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.03/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.03/2.00  --sup_immed_bw_main                     []
% 12.03/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.03/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 12.03/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.03/2.00  --sup_input_bw                          []
% 12.03/2.00  
% 12.03/2.00  ------ Combination Options
% 12.03/2.00  
% 12.03/2.00  --comb_res_mult                         3
% 12.03/2.00  --comb_sup_mult                         2
% 12.03/2.00  --comb_inst_mult                        10
% 12.03/2.00  
% 12.03/2.00  ------ Debug Options
% 12.03/2.00  
% 12.03/2.00  --dbg_backtrace                         false
% 12.03/2.00  --dbg_dump_prop_clauses                 false
% 12.03/2.00  --dbg_dump_prop_clauses_file            -
% 12.03/2.00  --dbg_out_stat                          false
% 12.03/2.00  ------ Parsing...
% 12.03/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.03/2.00  
% 12.03/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 12.03/2.00  
% 12.03/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.03/2.00  
% 12.03/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.03/2.00  ------ Proving...
% 12.03/2.00  ------ Problem Properties 
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  clauses                                 11
% 12.03/2.00  conjectures                             3
% 12.03/2.00  EPR                                     0
% 12.03/2.00  Horn                                    9
% 12.03/2.00  unary                                   6
% 12.03/2.00  binary                                  4
% 12.03/2.00  lits                                    17
% 12.03/2.00  lits eq                                 8
% 12.03/2.00  fd_pure                                 0
% 12.03/2.00  fd_pseudo                               0
% 12.03/2.00  fd_cond                                 0
% 12.03/2.00  fd_pseudo_cond                          0
% 12.03/2.00  AC symbols                              0
% 12.03/2.00  
% 12.03/2.00  ------ Schedule dynamic 5 is on 
% 12.03/2.00  
% 12.03/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  ------ 
% 12.03/2.00  Current options:
% 12.03/2.00  ------ 
% 12.03/2.00  
% 12.03/2.00  ------ Input Options
% 12.03/2.00  
% 12.03/2.00  --out_options                           all
% 12.03/2.00  --tptp_safe_out                         true
% 12.03/2.00  --problem_path                          ""
% 12.03/2.00  --include_path                          ""
% 12.03/2.00  --clausifier                            res/vclausify_rel
% 12.03/2.00  --clausifier_options                    ""
% 12.03/2.00  --stdin                                 false
% 12.03/2.00  --stats_out                             all
% 12.03/2.00  
% 12.03/2.00  ------ General Options
% 12.03/2.00  
% 12.03/2.00  --fof                                   false
% 12.03/2.00  --time_out_real                         305.
% 12.03/2.00  --time_out_virtual                      -1.
% 12.03/2.00  --symbol_type_check                     false
% 12.03/2.00  --clausify_out                          false
% 12.03/2.00  --sig_cnt_out                           false
% 12.03/2.00  --trig_cnt_out                          false
% 12.03/2.00  --trig_cnt_out_tolerance                1.
% 12.03/2.00  --trig_cnt_out_sk_spl                   false
% 12.03/2.00  --abstr_cl_out                          false
% 12.03/2.00  
% 12.03/2.00  ------ Global Options
% 12.03/2.00  
% 12.03/2.00  --schedule                              default
% 12.03/2.00  --add_important_lit                     false
% 12.03/2.00  --prop_solver_per_cl                    1000
% 12.03/2.00  --min_unsat_core                        false
% 12.03/2.00  --soft_assumptions                      false
% 12.03/2.00  --soft_lemma_size                       3
% 12.03/2.00  --prop_impl_unit_size                   0
% 12.03/2.00  --prop_impl_unit                        []
% 12.03/2.00  --share_sel_clauses                     true
% 12.03/2.00  --reset_solvers                         false
% 12.03/2.00  --bc_imp_inh                            [conj_cone]
% 12.03/2.00  --conj_cone_tolerance                   3.
% 12.03/2.00  --extra_neg_conj                        none
% 12.03/2.00  --large_theory_mode                     true
% 12.03/2.00  --prolific_symb_bound                   200
% 12.03/2.00  --lt_threshold                          2000
% 12.03/2.00  --clause_weak_htbl                      true
% 12.03/2.00  --gc_record_bc_elim                     false
% 12.03/2.00  
% 12.03/2.00  ------ Preprocessing Options
% 12.03/2.00  
% 12.03/2.00  --preprocessing_flag                    true
% 12.03/2.00  --time_out_prep_mult                    0.1
% 12.03/2.00  --splitting_mode                        input
% 12.03/2.00  --splitting_grd                         true
% 12.03/2.00  --splitting_cvd                         false
% 12.03/2.00  --splitting_cvd_svl                     false
% 12.03/2.00  --splitting_nvd                         32
% 12.03/2.00  --sub_typing                            true
% 12.03/2.00  --prep_gs_sim                           true
% 12.03/2.00  --prep_unflatten                        true
% 12.03/2.00  --prep_res_sim                          true
% 12.03/2.00  --prep_upred                            true
% 12.03/2.00  --prep_sem_filter                       exhaustive
% 12.03/2.00  --prep_sem_filter_out                   false
% 12.03/2.00  --pred_elim                             true
% 12.03/2.00  --res_sim_input                         true
% 12.03/2.00  --eq_ax_congr_red                       true
% 12.03/2.00  --pure_diseq_elim                       true
% 12.03/2.00  --brand_transform                       false
% 12.03/2.00  --non_eq_to_eq                          false
% 12.03/2.00  --prep_def_merge                        true
% 12.03/2.00  --prep_def_merge_prop_impl              false
% 12.03/2.00  --prep_def_merge_mbd                    true
% 12.03/2.00  --prep_def_merge_tr_red                 false
% 12.03/2.00  --prep_def_merge_tr_cl                  false
% 12.03/2.00  --smt_preprocessing                     true
% 12.03/2.00  --smt_ac_axioms                         fast
% 12.03/2.00  --preprocessed_out                      false
% 12.03/2.00  --preprocessed_stats                    false
% 12.03/2.00  
% 12.03/2.00  ------ Abstraction refinement Options
% 12.03/2.00  
% 12.03/2.00  --abstr_ref                             []
% 12.03/2.00  --abstr_ref_prep                        false
% 12.03/2.00  --abstr_ref_until_sat                   false
% 12.03/2.00  --abstr_ref_sig_restrict                funpre
% 12.03/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 12.03/2.00  --abstr_ref_under                       []
% 12.03/2.00  
% 12.03/2.00  ------ SAT Options
% 12.03/2.00  
% 12.03/2.00  --sat_mode                              false
% 12.03/2.00  --sat_fm_restart_options                ""
% 12.03/2.00  --sat_gr_def                            false
% 12.03/2.00  --sat_epr_types                         true
% 12.03/2.00  --sat_non_cyclic_types                  false
% 12.03/2.00  --sat_finite_models                     false
% 12.03/2.00  --sat_fm_lemmas                         false
% 12.03/2.00  --sat_fm_prep                           false
% 12.03/2.00  --sat_fm_uc_incr                        true
% 12.03/2.00  --sat_out_model                         small
% 12.03/2.00  --sat_out_clauses                       false
% 12.03/2.00  
% 12.03/2.00  ------ QBF Options
% 12.03/2.00  
% 12.03/2.00  --qbf_mode                              false
% 12.03/2.00  --qbf_elim_univ                         false
% 12.03/2.00  --qbf_dom_inst                          none
% 12.03/2.00  --qbf_dom_pre_inst                      false
% 12.03/2.00  --qbf_sk_in                             false
% 12.03/2.00  --qbf_pred_elim                         true
% 12.03/2.00  --qbf_split                             512
% 12.03/2.00  
% 12.03/2.00  ------ BMC1 Options
% 12.03/2.00  
% 12.03/2.00  --bmc1_incremental                      false
% 12.03/2.00  --bmc1_axioms                           reachable_all
% 12.03/2.00  --bmc1_min_bound                        0
% 12.03/2.00  --bmc1_max_bound                        -1
% 12.03/2.00  --bmc1_max_bound_default                -1
% 12.03/2.00  --bmc1_symbol_reachability              true
% 12.03/2.00  --bmc1_property_lemmas                  false
% 12.03/2.00  --bmc1_k_induction                      false
% 12.03/2.00  --bmc1_non_equiv_states                 false
% 12.03/2.00  --bmc1_deadlock                         false
% 12.03/2.00  --bmc1_ucm                              false
% 12.03/2.00  --bmc1_add_unsat_core                   none
% 12.03/2.00  --bmc1_unsat_core_children              false
% 12.03/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 12.03/2.00  --bmc1_out_stat                         full
% 12.03/2.00  --bmc1_ground_init                      false
% 12.03/2.00  --bmc1_pre_inst_next_state              false
% 12.03/2.00  --bmc1_pre_inst_state                   false
% 12.03/2.00  --bmc1_pre_inst_reach_state             false
% 12.03/2.00  --bmc1_out_unsat_core                   false
% 12.03/2.00  --bmc1_aig_witness_out                  false
% 12.03/2.00  --bmc1_verbose                          false
% 12.03/2.00  --bmc1_dump_clauses_tptp                false
% 12.03/2.00  --bmc1_dump_unsat_core_tptp             false
% 12.03/2.00  --bmc1_dump_file                        -
% 12.03/2.00  --bmc1_ucm_expand_uc_limit              128
% 12.03/2.00  --bmc1_ucm_n_expand_iterations          6
% 12.03/2.00  --bmc1_ucm_extend_mode                  1
% 12.03/2.00  --bmc1_ucm_init_mode                    2
% 12.03/2.00  --bmc1_ucm_cone_mode                    none
% 12.03/2.00  --bmc1_ucm_reduced_relation_type        0
% 12.03/2.00  --bmc1_ucm_relax_model                  4
% 12.03/2.00  --bmc1_ucm_full_tr_after_sat            true
% 12.03/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 12.03/2.00  --bmc1_ucm_layered_model                none
% 12.03/2.00  --bmc1_ucm_max_lemma_size               10
% 12.03/2.00  
% 12.03/2.00  ------ AIG Options
% 12.03/2.00  
% 12.03/2.00  --aig_mode                              false
% 12.03/2.00  
% 12.03/2.00  ------ Instantiation Options
% 12.03/2.00  
% 12.03/2.00  --instantiation_flag                    true
% 12.03/2.00  --inst_sos_flag                         true
% 12.03/2.00  --inst_sos_phase                        true
% 12.03/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.03/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.03/2.00  --inst_lit_sel_side                     none
% 12.03/2.00  --inst_solver_per_active                1400
% 12.03/2.00  --inst_solver_calls_frac                1.
% 12.03/2.00  --inst_passive_queue_type               priority_queues
% 12.03/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.03/2.00  --inst_passive_queues_freq              [25;2]
% 12.03/2.00  --inst_dismatching                      true
% 12.03/2.00  --inst_eager_unprocessed_to_passive     true
% 12.03/2.00  --inst_prop_sim_given                   true
% 12.03/2.00  --inst_prop_sim_new                     false
% 12.03/2.00  --inst_subs_new                         false
% 12.03/2.00  --inst_eq_res_simp                      false
% 12.03/2.00  --inst_subs_given                       false
% 12.03/2.00  --inst_orphan_elimination               true
% 12.03/2.00  --inst_learning_loop_flag               true
% 12.03/2.00  --inst_learning_start                   3000
% 12.03/2.00  --inst_learning_factor                  2
% 12.03/2.00  --inst_start_prop_sim_after_learn       3
% 12.03/2.00  --inst_sel_renew                        solver
% 12.03/2.00  --inst_lit_activity_flag                true
% 12.03/2.00  --inst_restr_to_given                   false
% 12.03/2.00  --inst_activity_threshold               500
% 12.03/2.00  --inst_out_proof                        true
% 12.03/2.00  
% 12.03/2.00  ------ Resolution Options
% 12.03/2.00  
% 12.03/2.00  --resolution_flag                       false
% 12.03/2.00  --res_lit_sel                           adaptive
% 12.03/2.00  --res_lit_sel_side                      none
% 12.03/2.00  --res_ordering                          kbo
% 12.03/2.00  --res_to_prop_solver                    active
% 12.03/2.00  --res_prop_simpl_new                    false
% 12.03/2.00  --res_prop_simpl_given                  true
% 12.03/2.00  --res_passive_queue_type                priority_queues
% 12.03/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.03/2.00  --res_passive_queues_freq               [15;5]
% 12.03/2.00  --res_forward_subs                      full
% 12.03/2.00  --res_backward_subs                     full
% 12.03/2.00  --res_forward_subs_resolution           true
% 12.03/2.00  --res_backward_subs_resolution          true
% 12.03/2.00  --res_orphan_elimination                true
% 12.03/2.00  --res_time_limit                        2.
% 12.03/2.00  --res_out_proof                         true
% 12.03/2.00  
% 12.03/2.00  ------ Superposition Options
% 12.03/2.00  
% 12.03/2.00  --superposition_flag                    true
% 12.03/2.00  --sup_passive_queue_type                priority_queues
% 12.03/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.03/2.00  --sup_passive_queues_freq               [8;1;4]
% 12.03/2.00  --demod_completeness_check              fast
% 12.03/2.00  --demod_use_ground                      true
% 12.03/2.00  --sup_to_prop_solver                    passive
% 12.03/2.00  --sup_prop_simpl_new                    true
% 12.03/2.00  --sup_prop_simpl_given                  true
% 12.03/2.00  --sup_fun_splitting                     true
% 12.03/2.00  --sup_smt_interval                      50000
% 12.03/2.00  
% 12.03/2.00  ------ Superposition Simplification Setup
% 12.03/2.00  
% 12.03/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.03/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.03/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.03/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.03/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 12.03/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.03/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.03/2.00  --sup_immed_triv                        [TrivRules]
% 12.03/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.03/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.03/2.00  --sup_immed_bw_main                     []
% 12.03/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.03/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 12.03/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.03/2.00  --sup_input_bw                          []
% 12.03/2.00  
% 12.03/2.00  ------ Combination Options
% 12.03/2.00  
% 12.03/2.00  --comb_res_mult                         3
% 12.03/2.00  --comb_sup_mult                         2
% 12.03/2.00  --comb_inst_mult                        10
% 12.03/2.00  
% 12.03/2.00  ------ Debug Options
% 12.03/2.00  
% 12.03/2.00  --dbg_backtrace                         false
% 12.03/2.00  --dbg_dump_prop_clauses                 false
% 12.03/2.00  --dbg_dump_prop_clauses_file            -
% 12.03/2.00  --dbg_out_stat                          false
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  ------ Proving...
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  % SZS status Theorem for theBenchmark.p
% 12.03/2.00  
% 12.03/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 12.03/2.00  
% 12.03/2.00  fof(f9,conjecture,(
% 12.03/2.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f10,negated_conjecture,(
% 12.03/2.00    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 12.03/2.00    inference(negated_conjecture,[],[f9])).
% 12.03/2.00  
% 12.03/2.00  fof(f12,plain,(
% 12.03/2.00    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 12.03/2.00    inference(ennf_transformation,[],[f10])).
% 12.03/2.00  
% 12.03/2.00  fof(f14,plain,(
% 12.03/2.00    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 12.03/2.00    introduced(choice_axiom,[])).
% 12.03/2.00  
% 12.03/2.00  fof(f15,plain,(
% 12.03/2.00    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 12.03/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 12.03/2.00  
% 12.03/2.00  fof(f30,plain,(
% 12.03/2.00    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 12.03/2.00    inference(cnf_transformation,[],[f15])).
% 12.03/2.00  
% 12.03/2.00  fof(f2,axiom,(
% 12.03/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f13,plain,(
% 12.03/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 12.03/2.00    inference(nnf_transformation,[],[f2])).
% 12.03/2.00  
% 12.03/2.00  fof(f17,plain,(
% 12.03/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f13])).
% 12.03/2.00  
% 12.03/2.00  fof(f8,axiom,(
% 12.03/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f24,plain,(
% 12.03/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.03/2.00    inference(cnf_transformation,[],[f8])).
% 12.03/2.00  
% 12.03/2.00  fof(f32,plain,(
% 12.03/2.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 12.03/2.00    inference(definition_unfolding,[],[f17,f24])).
% 12.03/2.00  
% 12.03/2.00  fof(f7,axiom,(
% 12.03/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f23,plain,(
% 12.03/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.03/2.00    inference(cnf_transformation,[],[f7])).
% 12.03/2.00  
% 12.03/2.00  fof(f34,plain,(
% 12.03/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 12.03/2.00    inference(definition_unfolding,[],[f23,f24])).
% 12.03/2.00  
% 12.03/2.00  fof(f5,axiom,(
% 12.03/2.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f21,plain,(
% 12.03/2.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.03/2.00    inference(cnf_transformation,[],[f5])).
% 12.03/2.00  
% 12.03/2.00  fof(f6,axiom,(
% 12.03/2.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f22,plain,(
% 12.03/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f6])).
% 12.03/2.00  
% 12.03/2.00  fof(f29,plain,(
% 12.03/2.00    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 12.03/2.00    inference(cnf_transformation,[],[f15])).
% 12.03/2.00  
% 12.03/2.00  fof(f1,axiom,(
% 12.03/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f16,plain,(
% 12.03/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f1])).
% 12.03/2.00  
% 12.03/2.00  fof(f4,axiom,(
% 12.03/2.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f20,plain,(
% 12.03/2.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 12.03/2.00    inference(cnf_transformation,[],[f4])).
% 12.03/2.00  
% 12.03/2.00  fof(f33,plain,(
% 12.03/2.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 12.03/2.00    inference(definition_unfolding,[],[f20,f24])).
% 12.03/2.00  
% 12.03/2.00  fof(f3,axiom,(
% 12.03/2.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f11,plain,(
% 12.03/2.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 12.03/2.00    inference(rectify,[],[f3])).
% 12.03/2.00  
% 12.03/2.00  fof(f19,plain,(
% 12.03/2.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 12.03/2.00    inference(cnf_transformation,[],[f11])).
% 12.03/2.00  
% 12.03/2.00  fof(f18,plain,(
% 12.03/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 12.03/2.00    inference(cnf_transformation,[],[f13])).
% 12.03/2.00  
% 12.03/2.00  fof(f31,plain,(
% 12.03/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.03/2.00    inference(definition_unfolding,[],[f18,f24])).
% 12.03/2.00  
% 12.03/2.00  fof(f25,plain,(
% 12.03/2.00    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 12.03/2.00    inference(cnf_transformation,[],[f15])).
% 12.03/2.00  
% 12.03/2.00  cnf(c_8,negated_conjecture,
% 12.03/2.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2) ),
% 12.03/2.00      inference(cnf_transformation,[],[f30]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_332,plain,
% 12.03/2.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
% 12.03/2.00      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_2,plain,
% 12.03/2.00      ( ~ r1_xboole_0(X0,X1)
% 12.03/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 12.03/2.00      inference(cnf_transformation,[],[f32]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_333,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 12.03/2.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_981,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 12.03/2.00      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_332,c_333]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1245,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_981,c_333]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_7,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 12.03/2.00      inference(cnf_transformation,[],[f34]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1258,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1245,c_7]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.03/2.00      inference(cnf_transformation,[],[f21]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1259,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_1258,c_5]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1314,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
% 12.03/2.00      | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1259,c_7]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1315,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
% 12.03/2.00      | k4_xboole_0(sK0,sK2) = sK0 ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_1314,c_5]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_6,plain,
% 12.03/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.03/2.00      inference(cnf_transformation,[],[f22]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_601,plain,
% 12.03/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_614,plain,
% 12.03/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_601,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5116,plain,
% 12.03/2.00      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 12.03/2.00      | k4_xboole_0(sK0,sK2) = sK0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1315,c_614]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_9,negated_conjecture,
% 12.03/2.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1) ),
% 12.03/2.00      inference(cnf_transformation,[],[f29]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_331,plain,
% 12.03/2.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
% 12.03/2.00      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_982,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 12.03/2.00      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_331,c_333]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1247,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_982,c_333]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_605,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_609,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_605,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4024,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1247,c_609]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_532,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_535,plain,
% 12.03/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_538,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_535,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4194,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_4024,c_532,c_538]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_0,plain,
% 12.03/2.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 12.03/2.00      inference(cnf_transformation,[],[f16]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 12.03/2.00      inference(cnf_transformation,[],[f33]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_335,plain,
% 12.03/2.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_4,c_5]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_534,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_335,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_703,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,X1) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_0,c_534]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_3,plain,
% 12.03/2.00      ( k2_xboole_0(X0,X0) = X0 ),
% 12.03/2.00      inference(cnf_transformation,[],[f19]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_705,plain,
% 12.03/2.00      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_3,c_534]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_711,plain,
% 12.03/2.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_705,c_335]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_733,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_703,c_711]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_800,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_733,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4709,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_4194,c_800]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4812,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_4709,c_7]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4813,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_4812,c_5]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5194,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 12.03/2.00      | k4_xboole_0(sK0,sK2) = sK0 ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_5116,c_4813]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4809,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_4709,c_609]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4842,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_4809,c_532]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5195,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k4_xboole_0(sK0,sK2)
% 12.03/2.00      | k4_xboole_0(sK0,sK2) = sK0 ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_5194,c_4842]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5196,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_5195,c_5,c_335]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1,plain,
% 12.03/2.00      ( r1_xboole_0(X0,X1)
% 12.03/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 12.03/2.00      inference(cnf_transformation,[],[f31]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_334,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 12.03/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5704,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) != k1_xboole_0
% 12.03/2.00      | r1_xboole_0(sK0,k2_xboole_0(sK1,X0)) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_4842,c_334]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_23356,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,sK0) != k1_xboole_0
% 12.03/2.00      | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_5196,c_5704]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_23522,plain,
% 12.03/2.00      ( k1_xboole_0 != k1_xboole_0
% 12.03/2.00      | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_23356,c_335]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_23523,plain,
% 12.03/2.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 12.03/2.00      inference(equality_resolution_simp,[status(thm)],[c_23522]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4025,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1245,c_609]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4193,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_4025,c_532,c_538]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4644,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(X0,sK2))) = k4_xboole_0(sK0,X0) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_0,c_4193]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4922,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0) ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_4644,c_4842]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1257,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1245,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1260,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) = k1_xboole_0 ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_1257,c_711]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_606,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_607,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_606,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_608,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_607,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_3051,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1260,c_608]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_536,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_3170,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_3051,c_536]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4957,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 12.03/2.00      | k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_4922,c_3170]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5003,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))
% 12.03/2.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_4957,c_4813]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_713,plain,
% 12.03/2.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_711,c_534]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5004,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 12.03/2.00      inference(demodulation,[status(thm)],[c_5003,c_713,c_4842]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1208,plain,
% 12.03/2.00      ( r1_xboole_0(sK0,sK1)
% 12.03/2.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 12.03/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1210,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0
% 12.03/2.00      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_345,plain,
% 12.03/2.00      ( r1_xboole_0(sK0,sK2)
% 12.03/2.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 12.03/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_346,plain,
% 12.03/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
% 12.03/2.00      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_13,negated_conjecture,
% 12.03/2.00      ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 12.03/2.00      | ~ r1_xboole_0(sK0,sK2)
% 12.03/2.00      | ~ r1_xboole_0(sK0,sK1) ),
% 12.03/2.00      inference(cnf_transformation,[],[f25]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_14,plain,
% 12.03/2.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != iProver_top
% 12.03/2.00      | r1_xboole_0(sK0,sK2) != iProver_top
% 12.03/2.00      | r1_xboole_0(sK0,sK1) != iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(contradiction,plain,
% 12.03/2.00      ( $false ),
% 12.03/2.00      inference(minisat,
% 12.03/2.00                [status(thm)],
% 12.03/2.00                [c_23523,c_5004,c_4709,c_1210,c_346,c_14]) ).
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 12.03/2.00  
% 12.03/2.00  ------                               Statistics
% 12.03/2.00  
% 12.03/2.00  ------ General
% 12.03/2.00  
% 12.03/2.00  abstr_ref_over_cycles:                  0
% 12.03/2.00  abstr_ref_under_cycles:                 0
% 12.03/2.00  gc_basic_clause_elim:                   0
% 12.03/2.00  forced_gc_time:                         0
% 12.03/2.00  parsing_time:                           0.019
% 12.03/2.00  unif_index_cands_time:                  0.
% 12.03/2.00  unif_index_add_time:                    0.
% 12.03/2.00  orderings_time:                         0.
% 12.03/2.00  out_proof_time:                         0.008
% 12.03/2.00  total_time:                             1.393
% 12.03/2.00  num_of_symbols:                         38
% 12.03/2.00  num_of_terms:                           47749
% 12.03/2.00  
% 12.03/2.00  ------ Preprocessing
% 12.03/2.00  
% 12.03/2.00  num_of_splits:                          0
% 12.03/2.00  num_of_split_atoms:                     0
% 12.03/2.00  num_of_reused_defs:                     0
% 12.03/2.00  num_eq_ax_congr_red:                    0
% 12.03/2.00  num_of_sem_filtered_clauses:            1
% 12.03/2.00  num_of_subtypes:                        0
% 12.03/2.00  monotx_restored_types:                  0
% 12.03/2.00  sat_num_of_epr_types:                   0
% 12.03/2.00  sat_num_of_non_cyclic_types:            0
% 12.03/2.00  sat_guarded_non_collapsed_types:        0
% 12.03/2.00  num_pure_diseq_elim:                    0
% 12.03/2.00  simp_replaced_by:                       0
% 12.03/2.00  res_preprocessed:                       55
% 12.03/2.00  prep_upred:                             0
% 12.03/2.00  prep_unflattend:                        0
% 12.03/2.00  smt_new_axioms:                         0
% 12.03/2.00  pred_elim_cands:                        1
% 12.03/2.00  pred_elim:                              0
% 12.03/2.00  pred_elim_cl:                           0
% 12.03/2.00  pred_elim_cycles:                       2
% 12.03/2.00  merged_defs:                            8
% 12.03/2.00  merged_defs_ncl:                        0
% 12.03/2.00  bin_hyper_res:                          8
% 12.03/2.00  prep_cycles:                            4
% 12.03/2.00  pred_elim_time:                         0.
% 12.03/2.00  splitting_time:                         0.
% 12.03/2.00  sem_filter_time:                        0.
% 12.03/2.00  monotx_time:                            0.
% 12.03/2.00  subtype_inf_time:                       0.
% 12.03/2.00  
% 12.03/2.00  ------ Problem properties
% 12.03/2.00  
% 12.03/2.00  clauses:                                11
% 12.03/2.00  conjectures:                            3
% 12.03/2.00  epr:                                    0
% 12.03/2.00  horn:                                   9
% 12.03/2.00  ground:                                 3
% 12.03/2.00  unary:                                  6
% 12.03/2.00  binary:                                 4
% 12.03/2.00  lits:                                   17
% 12.03/2.00  lits_eq:                                8
% 12.03/2.00  fd_pure:                                0
% 12.03/2.00  fd_pseudo:                              0
% 12.03/2.00  fd_cond:                                0
% 12.03/2.00  fd_pseudo_cond:                         0
% 12.03/2.00  ac_symbols:                             0
% 12.03/2.00  
% 12.03/2.00  ------ Propositional Solver
% 12.03/2.00  
% 12.03/2.00  prop_solver_calls:                      35
% 12.03/2.00  prop_fast_solver_calls:                 436
% 12.03/2.00  smt_solver_calls:                       0
% 12.03/2.00  smt_fast_solver_calls:                  0
% 12.03/2.00  prop_num_of_clauses:                    10586
% 12.03/2.00  prop_preprocess_simplified:             8090
% 12.03/2.00  prop_fo_subsumed:                       3
% 12.03/2.00  prop_solver_time:                       0.
% 12.03/2.00  smt_solver_time:                        0.
% 12.03/2.00  smt_fast_solver_time:                   0.
% 12.03/2.00  prop_fast_solver_time:                  0.
% 12.03/2.00  prop_unsat_core_time:                   0.001
% 12.03/2.00  
% 12.03/2.00  ------ QBF
% 12.03/2.00  
% 12.03/2.00  qbf_q_res:                              0
% 12.03/2.00  qbf_num_tautologies:                    0
% 12.03/2.00  qbf_prep_cycles:                        0
% 12.03/2.00  
% 12.03/2.00  ------ BMC1
% 12.03/2.00  
% 12.03/2.00  bmc1_current_bound:                     -1
% 12.03/2.00  bmc1_last_solved_bound:                 -1
% 12.03/2.00  bmc1_unsat_core_size:                   -1
% 12.03/2.00  bmc1_unsat_core_parents_size:           -1
% 12.03/2.00  bmc1_merge_next_fun:                    0
% 12.03/2.00  bmc1_unsat_core_clauses_time:           0.
% 12.03/2.00  
% 12.03/2.00  ------ Instantiation
% 12.03/2.00  
% 12.03/2.00  inst_num_of_clauses:                    1961
% 12.03/2.00  inst_num_in_passive:                    843
% 12.03/2.00  inst_num_in_active:                     650
% 12.03/2.00  inst_num_in_unprocessed:                468
% 12.03/2.00  inst_num_of_loops:                      890
% 12.03/2.00  inst_num_of_learning_restarts:          0
% 12.03/2.00  inst_num_moves_active_passive:          233
% 12.03/2.00  inst_lit_activity:                      0
% 12.03/2.00  inst_lit_activity_moves:                0
% 12.03/2.00  inst_num_tautologies:                   0
% 12.03/2.00  inst_num_prop_implied:                  0
% 12.03/2.00  inst_num_existing_simplified:           0
% 12.03/2.00  inst_num_eq_res_simplified:             0
% 12.03/2.00  inst_num_child_elim:                    0
% 12.03/2.00  inst_num_of_dismatching_blockings:      499
% 12.03/2.00  inst_num_of_non_proper_insts:           2013
% 12.03/2.00  inst_num_of_duplicates:                 0
% 12.03/2.00  inst_inst_num_from_inst_to_res:         0
% 12.03/2.00  inst_dismatching_checking_time:         0.
% 12.03/2.00  
% 12.03/2.00  ------ Resolution
% 12.03/2.00  
% 12.03/2.00  res_num_of_clauses:                     0
% 12.03/2.00  res_num_in_passive:                     0
% 12.03/2.00  res_num_in_active:                      0
% 12.03/2.00  res_num_of_loops:                       59
% 12.03/2.00  res_forward_subset_subsumed:            410
% 12.03/2.00  res_backward_subset_subsumed:           0
% 12.03/2.00  res_forward_subsumed:                   0
% 12.03/2.00  res_backward_subsumed:                  0
% 12.03/2.00  res_forward_subsumption_resolution:     0
% 12.03/2.00  res_backward_subsumption_resolution:    0
% 12.03/2.00  res_clause_to_clause_subsumption:       60631
% 12.03/2.00  res_orphan_elimination:                 0
% 12.03/2.00  res_tautology_del:                      184
% 12.03/2.00  res_num_eq_res_simplified:              0
% 12.03/2.00  res_num_sel_changes:                    0
% 12.03/2.00  res_moves_from_active_to_pass:          0
% 12.03/2.00  
% 12.03/2.00  ------ Superposition
% 12.03/2.00  
% 12.03/2.00  sup_time_total:                         0.
% 12.03/2.00  sup_time_generating:                    0.
% 12.03/2.00  sup_time_sim_full:                      0.
% 12.03/2.00  sup_time_sim_immed:                     0.
% 12.03/2.00  
% 12.03/2.00  sup_num_of_clauses:                     3723
% 12.03/2.00  sup_num_in_active:                      137
% 12.03/2.00  sup_num_in_passive:                     3586
% 12.03/2.00  sup_num_of_loops:                       177
% 12.03/2.00  sup_fw_superposition:                   5542
% 12.03/2.00  sup_bw_superposition:                   4724
% 12.03/2.00  sup_immediate_simplified:               3963
% 12.03/2.00  sup_given_eliminated:                   3
% 12.03/2.00  comparisons_done:                       0
% 12.03/2.00  comparisons_avoided:                    36
% 12.03/2.00  
% 12.03/2.00  ------ Simplifications
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  sim_fw_subset_subsumed:                 43
% 12.03/2.00  sim_bw_subset_subsumed:                 68
% 12.03/2.00  sim_fw_subsumed:                        1160
% 12.03/2.00  sim_bw_subsumed:                        39
% 12.03/2.00  sim_fw_subsumption_res:                 0
% 12.03/2.00  sim_bw_subsumption_res:                 0
% 12.03/2.00  sim_tautology_del:                      2
% 12.03/2.00  sim_eq_tautology_del:                   818
% 12.03/2.00  sim_eq_res_simp:                        17
% 12.03/2.00  sim_fw_demodulated:                     2418
% 12.03/2.00  sim_bw_demodulated:                     17
% 12.03/2.00  sim_light_normalised:                   788
% 12.03/2.00  sim_joinable_taut:                      0
% 12.03/2.00  sim_joinable_simp:                      0
% 12.03/2.00  sim_ac_normalised:                      0
% 12.03/2.00  sim_smt_subsumption:                    0
% 12.03/2.00  
%------------------------------------------------------------------------------
