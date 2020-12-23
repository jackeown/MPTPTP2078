%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:39 EST 2020

% Result     : Theorem 35.94s
% Output     : CNFRefutation 35.94s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 910 expanded)
%              Number of clauses        :   74 ( 373 expanded)
%              Number of leaves         :   13 ( 230 expanded)
%              Depth                    :   20
%              Number of atoms          :  199 (1489 expanded)
%              Number of equality atoms :  136 ( 957 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f13,plain,
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

fof(f14,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f28,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f16,f23])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f29,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f24,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_331,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_333,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_949,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_331,c_333])).

cnf(c_1238,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_949,c_333])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_557,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_562,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_557,c_6])).

cnf(c_7585,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1238,c_562])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_509,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_512,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_517,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_512,c_6])).

cnf(c_7731,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_7585,c_509,c_517])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_335,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_515,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_335])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_516,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_515,c_4])).

cnf(c_619,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_516,c_6])).

cnf(c_8820,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7731,c_619])).

cnf(c_8836,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_8820,c_562])).

cnf(c_9107,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_8836,c_509])).

cnf(c_26851,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_9107,c_6])).

cnf(c_26903,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_26851,c_6,c_517])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_505,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_335,c_4])).

cnf(c_572,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_505])).

cnf(c_774,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_572,c_509])).

cnf(c_125032,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,X0))) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_26903,c_774])).

cnf(c_125130,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_125032,c_9107])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_332,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_948,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_332,c_333])).

cnf(c_1197,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_948,c_333])).

cnf(c_1242,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1197,c_7])).

cnf(c_1244,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_1242,c_5])).

cnf(c_1351,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1244,c_7])).

cnf(c_1353,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_1351,c_5])).

cnf(c_11919,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_1353,c_9107])).

cnf(c_11937,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_11919,c_6])).

cnf(c_125583,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_125130,c_11937])).

cnf(c_125609,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_125583,c_11919])).

cnf(c_169,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2765,plain,
    ( X0 != X1
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != X1
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = X0 ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_9223,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_33430,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_9223])).

cnf(c_33431,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK0)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_33430])).

cnf(c_172,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_9214,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(X0,X1)
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_9215,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK0)
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != sK0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_9214])).

cnf(c_7586,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1197,c_562])).

cnf(c_7730,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_7586,c_509,c_517])).

cnf(c_8658,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_4,c_7730])).

cnf(c_9136,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8658,c_9107])).

cnf(c_9184,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)) != k1_xboole_0 ),
    inference(equality_factoring,[status(thm)],[c_9136])).

cnf(c_9185,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9184,c_516])).

cnf(c_9186,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9185])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2273,plain,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_367,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_390,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1295,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(X0,X1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_1296,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_831,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_168,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_418,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_345,plain,
    ( r1_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_337,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_176,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_125609,c_33431,c_9215,c_9186,c_8820,c_2273,c_1296,c_831,c_418,c_345,c_337,c_176,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.94/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.94/5.00  
% 35.94/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.94/5.00  
% 35.94/5.00  ------  iProver source info
% 35.94/5.00  
% 35.94/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.94/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.94/5.00  git: non_committed_changes: false
% 35.94/5.00  git: last_make_outside_of_git: false
% 35.94/5.00  
% 35.94/5.00  ------ 
% 35.94/5.00  
% 35.94/5.00  ------ Input Options
% 35.94/5.00  
% 35.94/5.00  --out_options                           all
% 35.94/5.00  --tptp_safe_out                         true
% 35.94/5.00  --problem_path                          ""
% 35.94/5.00  --include_path                          ""
% 35.94/5.00  --clausifier                            res/vclausify_rel
% 35.94/5.00  --clausifier_options                    ""
% 35.94/5.00  --stdin                                 false
% 35.94/5.00  --stats_out                             all
% 35.94/5.00  
% 35.94/5.00  ------ General Options
% 35.94/5.00  
% 35.94/5.00  --fof                                   false
% 35.94/5.00  --time_out_real                         305.
% 35.94/5.00  --time_out_virtual                      -1.
% 35.94/5.00  --symbol_type_check                     false
% 35.94/5.00  --clausify_out                          false
% 35.94/5.00  --sig_cnt_out                           false
% 35.94/5.00  --trig_cnt_out                          false
% 35.94/5.00  --trig_cnt_out_tolerance                1.
% 35.94/5.00  --trig_cnt_out_sk_spl                   false
% 35.94/5.00  --abstr_cl_out                          false
% 35.94/5.00  
% 35.94/5.00  ------ Global Options
% 35.94/5.00  
% 35.94/5.00  --schedule                              default
% 35.94/5.00  --add_important_lit                     false
% 35.94/5.00  --prop_solver_per_cl                    1000
% 35.94/5.00  --min_unsat_core                        false
% 35.94/5.00  --soft_assumptions                      false
% 35.94/5.00  --soft_lemma_size                       3
% 35.94/5.00  --prop_impl_unit_size                   0
% 35.94/5.00  --prop_impl_unit                        []
% 35.94/5.00  --share_sel_clauses                     true
% 35.94/5.00  --reset_solvers                         false
% 35.94/5.00  --bc_imp_inh                            [conj_cone]
% 35.94/5.00  --conj_cone_tolerance                   3.
% 35.94/5.00  --extra_neg_conj                        none
% 35.94/5.00  --large_theory_mode                     true
% 35.94/5.00  --prolific_symb_bound                   200
% 35.94/5.00  --lt_threshold                          2000
% 35.94/5.00  --clause_weak_htbl                      true
% 35.94/5.00  --gc_record_bc_elim                     false
% 35.94/5.00  
% 35.94/5.00  ------ Preprocessing Options
% 35.94/5.00  
% 35.94/5.00  --preprocessing_flag                    true
% 35.94/5.00  --time_out_prep_mult                    0.1
% 35.94/5.00  --splitting_mode                        input
% 35.94/5.00  --splitting_grd                         true
% 35.94/5.00  --splitting_cvd                         false
% 35.94/5.00  --splitting_cvd_svl                     false
% 35.94/5.00  --splitting_nvd                         32
% 35.94/5.00  --sub_typing                            true
% 35.94/5.00  --prep_gs_sim                           true
% 35.94/5.00  --prep_unflatten                        true
% 35.94/5.00  --prep_res_sim                          true
% 35.94/5.00  --prep_upred                            true
% 35.94/5.00  --prep_sem_filter                       exhaustive
% 35.94/5.00  --prep_sem_filter_out                   false
% 35.94/5.00  --pred_elim                             true
% 35.94/5.00  --res_sim_input                         true
% 35.94/5.00  --eq_ax_congr_red                       true
% 35.94/5.00  --pure_diseq_elim                       true
% 35.94/5.00  --brand_transform                       false
% 35.94/5.00  --non_eq_to_eq                          false
% 35.94/5.00  --prep_def_merge                        true
% 35.94/5.00  --prep_def_merge_prop_impl              false
% 35.94/5.00  --prep_def_merge_mbd                    true
% 35.94/5.00  --prep_def_merge_tr_red                 false
% 35.94/5.00  --prep_def_merge_tr_cl                  false
% 35.94/5.00  --smt_preprocessing                     true
% 35.94/5.00  --smt_ac_axioms                         fast
% 35.94/5.00  --preprocessed_out                      false
% 35.94/5.00  --preprocessed_stats                    false
% 35.94/5.00  
% 35.94/5.00  ------ Abstraction refinement Options
% 35.94/5.00  
% 35.94/5.00  --abstr_ref                             []
% 35.94/5.00  --abstr_ref_prep                        false
% 35.94/5.00  --abstr_ref_until_sat                   false
% 35.94/5.00  --abstr_ref_sig_restrict                funpre
% 35.94/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.94/5.00  --abstr_ref_under                       []
% 35.94/5.00  
% 35.94/5.00  ------ SAT Options
% 35.94/5.00  
% 35.94/5.00  --sat_mode                              false
% 35.94/5.00  --sat_fm_restart_options                ""
% 35.94/5.00  --sat_gr_def                            false
% 35.94/5.00  --sat_epr_types                         true
% 35.94/5.00  --sat_non_cyclic_types                  false
% 35.94/5.00  --sat_finite_models                     false
% 35.94/5.00  --sat_fm_lemmas                         false
% 35.94/5.00  --sat_fm_prep                           false
% 35.94/5.00  --sat_fm_uc_incr                        true
% 35.94/5.00  --sat_out_model                         small
% 35.94/5.00  --sat_out_clauses                       false
% 35.94/5.00  
% 35.94/5.00  ------ QBF Options
% 35.94/5.00  
% 35.94/5.00  --qbf_mode                              false
% 35.94/5.00  --qbf_elim_univ                         false
% 35.94/5.00  --qbf_dom_inst                          none
% 35.94/5.00  --qbf_dom_pre_inst                      false
% 35.94/5.00  --qbf_sk_in                             false
% 35.94/5.00  --qbf_pred_elim                         true
% 35.94/5.00  --qbf_split                             512
% 35.94/5.00  
% 35.94/5.00  ------ BMC1 Options
% 35.94/5.00  
% 35.94/5.00  --bmc1_incremental                      false
% 35.94/5.00  --bmc1_axioms                           reachable_all
% 35.94/5.00  --bmc1_min_bound                        0
% 35.94/5.00  --bmc1_max_bound                        -1
% 35.94/5.00  --bmc1_max_bound_default                -1
% 35.94/5.00  --bmc1_symbol_reachability              true
% 35.94/5.00  --bmc1_property_lemmas                  false
% 35.94/5.00  --bmc1_k_induction                      false
% 35.94/5.00  --bmc1_non_equiv_states                 false
% 35.94/5.00  --bmc1_deadlock                         false
% 35.94/5.00  --bmc1_ucm                              false
% 35.94/5.00  --bmc1_add_unsat_core                   none
% 35.94/5.00  --bmc1_unsat_core_children              false
% 35.94/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.94/5.00  --bmc1_out_stat                         full
% 35.94/5.00  --bmc1_ground_init                      false
% 35.94/5.00  --bmc1_pre_inst_next_state              false
% 35.94/5.00  --bmc1_pre_inst_state                   false
% 35.94/5.00  --bmc1_pre_inst_reach_state             false
% 35.94/5.00  --bmc1_out_unsat_core                   false
% 35.94/5.00  --bmc1_aig_witness_out                  false
% 35.94/5.00  --bmc1_verbose                          false
% 35.94/5.00  --bmc1_dump_clauses_tptp                false
% 35.94/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.94/5.00  --bmc1_dump_file                        -
% 35.94/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.94/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.94/5.00  --bmc1_ucm_extend_mode                  1
% 35.94/5.00  --bmc1_ucm_init_mode                    2
% 35.94/5.00  --bmc1_ucm_cone_mode                    none
% 35.94/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.94/5.00  --bmc1_ucm_relax_model                  4
% 35.94/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.94/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.94/5.00  --bmc1_ucm_layered_model                none
% 35.94/5.00  --bmc1_ucm_max_lemma_size               10
% 35.94/5.00  
% 35.94/5.00  ------ AIG Options
% 35.94/5.00  
% 35.94/5.00  --aig_mode                              false
% 35.94/5.00  
% 35.94/5.00  ------ Instantiation Options
% 35.94/5.00  
% 35.94/5.00  --instantiation_flag                    true
% 35.94/5.00  --inst_sos_flag                         true
% 35.94/5.00  --inst_sos_phase                        true
% 35.94/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.94/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.94/5.00  --inst_lit_sel_side                     num_symb
% 35.94/5.00  --inst_solver_per_active                1400
% 35.94/5.00  --inst_solver_calls_frac                1.
% 35.94/5.00  --inst_passive_queue_type               priority_queues
% 35.94/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.94/5.00  --inst_passive_queues_freq              [25;2]
% 35.94/5.00  --inst_dismatching                      true
% 35.94/5.00  --inst_eager_unprocessed_to_passive     true
% 35.94/5.00  --inst_prop_sim_given                   true
% 35.94/5.00  --inst_prop_sim_new                     false
% 35.94/5.00  --inst_subs_new                         false
% 35.94/5.00  --inst_eq_res_simp                      false
% 35.94/5.00  --inst_subs_given                       false
% 35.94/5.00  --inst_orphan_elimination               true
% 35.94/5.00  --inst_learning_loop_flag               true
% 35.94/5.00  --inst_learning_start                   3000
% 35.94/5.00  --inst_learning_factor                  2
% 35.94/5.00  --inst_start_prop_sim_after_learn       3
% 35.94/5.00  --inst_sel_renew                        solver
% 35.94/5.00  --inst_lit_activity_flag                true
% 35.94/5.00  --inst_restr_to_given                   false
% 35.94/5.00  --inst_activity_threshold               500
% 35.94/5.00  --inst_out_proof                        true
% 35.94/5.00  
% 35.94/5.00  ------ Resolution Options
% 35.94/5.00  
% 35.94/5.00  --resolution_flag                       true
% 35.94/5.00  --res_lit_sel                           adaptive
% 35.94/5.00  --res_lit_sel_side                      none
% 35.94/5.00  --res_ordering                          kbo
% 35.94/5.00  --res_to_prop_solver                    active
% 35.94/5.00  --res_prop_simpl_new                    false
% 35.94/5.00  --res_prop_simpl_given                  true
% 35.94/5.00  --res_passive_queue_type                priority_queues
% 35.94/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.94/5.00  --res_passive_queues_freq               [15;5]
% 35.94/5.00  --res_forward_subs                      full
% 35.94/5.00  --res_backward_subs                     full
% 35.94/5.00  --res_forward_subs_resolution           true
% 35.94/5.00  --res_backward_subs_resolution          true
% 35.94/5.00  --res_orphan_elimination                true
% 35.94/5.00  --res_time_limit                        2.
% 35.94/5.00  --res_out_proof                         true
% 35.94/5.00  
% 35.94/5.00  ------ Superposition Options
% 35.94/5.00  
% 35.94/5.00  --superposition_flag                    true
% 35.94/5.00  --sup_passive_queue_type                priority_queues
% 35.94/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.94/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.94/5.00  --demod_completeness_check              fast
% 35.94/5.00  --demod_use_ground                      true
% 35.94/5.00  --sup_to_prop_solver                    passive
% 35.94/5.00  --sup_prop_simpl_new                    true
% 35.94/5.00  --sup_prop_simpl_given                  true
% 35.94/5.00  --sup_fun_splitting                     true
% 35.94/5.00  --sup_smt_interval                      50000
% 35.94/5.00  
% 35.94/5.00  ------ Superposition Simplification Setup
% 35.94/5.00  
% 35.94/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.94/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.94/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.94/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.94/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.94/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.94/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.94/5.00  --sup_immed_triv                        [TrivRules]
% 35.94/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.94/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.94/5.00  --sup_immed_bw_main                     []
% 35.94/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.94/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.94/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.94/5.00  --sup_input_bw                          []
% 35.94/5.00  
% 35.94/5.00  ------ Combination Options
% 35.94/5.00  
% 35.94/5.00  --comb_res_mult                         3
% 35.94/5.00  --comb_sup_mult                         2
% 35.94/5.00  --comb_inst_mult                        10
% 35.94/5.00  
% 35.94/5.00  ------ Debug Options
% 35.94/5.00  
% 35.94/5.00  --dbg_backtrace                         false
% 35.94/5.00  --dbg_dump_prop_clauses                 false
% 35.94/5.00  --dbg_dump_prop_clauses_file            -
% 35.94/5.00  --dbg_out_stat                          false
% 35.94/5.00  ------ Parsing...
% 35.94/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.94/5.00  
% 35.94/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.94/5.00  
% 35.94/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.94/5.00  
% 35.94/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.94/5.00  ------ Proving...
% 35.94/5.00  ------ Problem Properties 
% 35.94/5.00  
% 35.94/5.00  
% 35.94/5.00  clauses                                 11
% 35.94/5.00  conjectures                             3
% 35.94/5.00  EPR                                     0
% 35.94/5.00  Horn                                    9
% 35.94/5.00  unary                                   6
% 35.94/5.00  binary                                  4
% 35.94/5.00  lits                                    17
% 35.94/5.00  lits eq                                 8
% 35.94/5.00  fd_pure                                 0
% 35.94/5.00  fd_pseudo                               0
% 35.94/5.00  fd_cond                                 0
% 35.94/5.00  fd_pseudo_cond                          0
% 35.94/5.00  AC symbols                              0
% 35.94/5.00  
% 35.94/5.00  ------ Schedule dynamic 5 is on 
% 35.94/5.00  
% 35.94/5.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.94/5.00  
% 35.94/5.00  
% 35.94/5.00  ------ 
% 35.94/5.00  Current options:
% 35.94/5.00  ------ 
% 35.94/5.00  
% 35.94/5.00  ------ Input Options
% 35.94/5.00  
% 35.94/5.00  --out_options                           all
% 35.94/5.00  --tptp_safe_out                         true
% 35.94/5.00  --problem_path                          ""
% 35.94/5.00  --include_path                          ""
% 35.94/5.00  --clausifier                            res/vclausify_rel
% 35.94/5.00  --clausifier_options                    ""
% 35.94/5.00  --stdin                                 false
% 35.94/5.00  --stats_out                             all
% 35.94/5.00  
% 35.94/5.00  ------ General Options
% 35.94/5.00  
% 35.94/5.00  --fof                                   false
% 35.94/5.00  --time_out_real                         305.
% 35.94/5.00  --time_out_virtual                      -1.
% 35.94/5.00  --symbol_type_check                     false
% 35.94/5.00  --clausify_out                          false
% 35.94/5.00  --sig_cnt_out                           false
% 35.94/5.00  --trig_cnt_out                          false
% 35.94/5.00  --trig_cnt_out_tolerance                1.
% 35.94/5.00  --trig_cnt_out_sk_spl                   false
% 35.94/5.00  --abstr_cl_out                          false
% 35.94/5.00  
% 35.94/5.00  ------ Global Options
% 35.94/5.00  
% 35.94/5.00  --schedule                              default
% 35.94/5.00  --add_important_lit                     false
% 35.94/5.00  --prop_solver_per_cl                    1000
% 35.94/5.00  --min_unsat_core                        false
% 35.94/5.00  --soft_assumptions                      false
% 35.94/5.00  --soft_lemma_size                       3
% 35.94/5.00  --prop_impl_unit_size                   0
% 35.94/5.00  --prop_impl_unit                        []
% 35.94/5.00  --share_sel_clauses                     true
% 35.94/5.00  --reset_solvers                         false
% 35.94/5.00  --bc_imp_inh                            [conj_cone]
% 35.94/5.00  --conj_cone_tolerance                   3.
% 35.94/5.00  --extra_neg_conj                        none
% 35.94/5.00  --large_theory_mode                     true
% 35.94/5.00  --prolific_symb_bound                   200
% 35.94/5.00  --lt_threshold                          2000
% 35.94/5.00  --clause_weak_htbl                      true
% 35.94/5.00  --gc_record_bc_elim                     false
% 35.94/5.00  
% 35.94/5.00  ------ Preprocessing Options
% 35.94/5.00  
% 35.94/5.00  --preprocessing_flag                    true
% 35.94/5.00  --time_out_prep_mult                    0.1
% 35.94/5.00  --splitting_mode                        input
% 35.94/5.00  --splitting_grd                         true
% 35.94/5.00  --splitting_cvd                         false
% 35.94/5.00  --splitting_cvd_svl                     false
% 35.94/5.00  --splitting_nvd                         32
% 35.94/5.00  --sub_typing                            true
% 35.94/5.00  --prep_gs_sim                           true
% 35.94/5.00  --prep_unflatten                        true
% 35.94/5.00  --prep_res_sim                          true
% 35.94/5.00  --prep_upred                            true
% 35.94/5.00  --prep_sem_filter                       exhaustive
% 35.94/5.00  --prep_sem_filter_out                   false
% 35.94/5.00  --pred_elim                             true
% 35.94/5.00  --res_sim_input                         true
% 35.94/5.00  --eq_ax_congr_red                       true
% 35.94/5.00  --pure_diseq_elim                       true
% 35.94/5.00  --brand_transform                       false
% 35.94/5.00  --non_eq_to_eq                          false
% 35.94/5.00  --prep_def_merge                        true
% 35.94/5.00  --prep_def_merge_prop_impl              false
% 35.94/5.00  --prep_def_merge_mbd                    true
% 35.94/5.00  --prep_def_merge_tr_red                 false
% 35.94/5.00  --prep_def_merge_tr_cl                  false
% 35.94/5.00  --smt_preprocessing                     true
% 35.94/5.00  --smt_ac_axioms                         fast
% 35.94/5.00  --preprocessed_out                      false
% 35.94/5.00  --preprocessed_stats                    false
% 35.94/5.00  
% 35.94/5.00  ------ Abstraction refinement Options
% 35.94/5.00  
% 35.94/5.00  --abstr_ref                             []
% 35.94/5.00  --abstr_ref_prep                        false
% 35.94/5.00  --abstr_ref_until_sat                   false
% 35.94/5.00  --abstr_ref_sig_restrict                funpre
% 35.94/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.94/5.00  --abstr_ref_under                       []
% 35.94/5.00  
% 35.94/5.00  ------ SAT Options
% 35.94/5.00  
% 35.94/5.00  --sat_mode                              false
% 35.94/5.00  --sat_fm_restart_options                ""
% 35.94/5.00  --sat_gr_def                            false
% 35.94/5.00  --sat_epr_types                         true
% 35.94/5.00  --sat_non_cyclic_types                  false
% 35.94/5.00  --sat_finite_models                     false
% 35.94/5.00  --sat_fm_lemmas                         false
% 35.94/5.00  --sat_fm_prep                           false
% 35.94/5.00  --sat_fm_uc_incr                        true
% 35.94/5.00  --sat_out_model                         small
% 35.94/5.00  --sat_out_clauses                       false
% 35.94/5.00  
% 35.94/5.00  ------ QBF Options
% 35.94/5.00  
% 35.94/5.00  --qbf_mode                              false
% 35.94/5.00  --qbf_elim_univ                         false
% 35.94/5.00  --qbf_dom_inst                          none
% 35.94/5.00  --qbf_dom_pre_inst                      false
% 35.94/5.00  --qbf_sk_in                             false
% 35.94/5.00  --qbf_pred_elim                         true
% 35.94/5.00  --qbf_split                             512
% 35.94/5.00  
% 35.94/5.00  ------ BMC1 Options
% 35.94/5.00  
% 35.94/5.00  --bmc1_incremental                      false
% 35.94/5.00  --bmc1_axioms                           reachable_all
% 35.94/5.00  --bmc1_min_bound                        0
% 35.94/5.00  --bmc1_max_bound                        -1
% 35.94/5.00  --bmc1_max_bound_default                -1
% 35.94/5.00  --bmc1_symbol_reachability              true
% 35.94/5.00  --bmc1_property_lemmas                  false
% 35.94/5.00  --bmc1_k_induction                      false
% 35.94/5.00  --bmc1_non_equiv_states                 false
% 35.94/5.00  --bmc1_deadlock                         false
% 35.94/5.00  --bmc1_ucm                              false
% 35.94/5.00  --bmc1_add_unsat_core                   none
% 35.94/5.00  --bmc1_unsat_core_children              false
% 35.94/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.94/5.00  --bmc1_out_stat                         full
% 35.94/5.00  --bmc1_ground_init                      false
% 35.94/5.00  --bmc1_pre_inst_next_state              false
% 35.94/5.00  --bmc1_pre_inst_state                   false
% 35.94/5.00  --bmc1_pre_inst_reach_state             false
% 35.94/5.00  --bmc1_out_unsat_core                   false
% 35.94/5.00  --bmc1_aig_witness_out                  false
% 35.94/5.00  --bmc1_verbose                          false
% 35.94/5.00  --bmc1_dump_clauses_tptp                false
% 35.94/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.94/5.00  --bmc1_dump_file                        -
% 35.94/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.94/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.94/5.00  --bmc1_ucm_extend_mode                  1
% 35.94/5.00  --bmc1_ucm_init_mode                    2
% 35.94/5.00  --bmc1_ucm_cone_mode                    none
% 35.94/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.94/5.00  --bmc1_ucm_relax_model                  4
% 35.94/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.94/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.94/5.00  --bmc1_ucm_layered_model                none
% 35.94/5.00  --bmc1_ucm_max_lemma_size               10
% 35.94/5.00  
% 35.94/5.00  ------ AIG Options
% 35.94/5.00  
% 35.94/5.00  --aig_mode                              false
% 35.94/5.00  
% 35.94/5.00  ------ Instantiation Options
% 35.94/5.00  
% 35.94/5.00  --instantiation_flag                    true
% 35.94/5.00  --inst_sos_flag                         true
% 35.94/5.00  --inst_sos_phase                        true
% 35.94/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.94/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.94/5.00  --inst_lit_sel_side                     none
% 35.94/5.00  --inst_solver_per_active                1400
% 35.94/5.00  --inst_solver_calls_frac                1.
% 35.94/5.00  --inst_passive_queue_type               priority_queues
% 35.94/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.94/5.00  --inst_passive_queues_freq              [25;2]
% 35.94/5.00  --inst_dismatching                      true
% 35.94/5.00  --inst_eager_unprocessed_to_passive     true
% 35.94/5.00  --inst_prop_sim_given                   true
% 35.94/5.00  --inst_prop_sim_new                     false
% 35.94/5.00  --inst_subs_new                         false
% 35.94/5.00  --inst_eq_res_simp                      false
% 35.94/5.00  --inst_subs_given                       false
% 35.94/5.00  --inst_orphan_elimination               true
% 35.94/5.00  --inst_learning_loop_flag               true
% 35.94/5.00  --inst_learning_start                   3000
% 35.94/5.00  --inst_learning_factor                  2
% 35.94/5.00  --inst_start_prop_sim_after_learn       3
% 35.94/5.00  --inst_sel_renew                        solver
% 35.94/5.00  --inst_lit_activity_flag                true
% 35.94/5.00  --inst_restr_to_given                   false
% 35.94/5.00  --inst_activity_threshold               500
% 35.94/5.00  --inst_out_proof                        true
% 35.94/5.00  
% 35.94/5.00  ------ Resolution Options
% 35.94/5.00  
% 35.94/5.00  --resolution_flag                       false
% 35.94/5.00  --res_lit_sel                           adaptive
% 35.94/5.00  --res_lit_sel_side                      none
% 35.94/5.00  --res_ordering                          kbo
% 35.94/5.00  --res_to_prop_solver                    active
% 35.94/5.00  --res_prop_simpl_new                    false
% 35.94/5.00  --res_prop_simpl_given                  true
% 35.94/5.00  --res_passive_queue_type                priority_queues
% 35.94/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.94/5.00  --res_passive_queues_freq               [15;5]
% 35.94/5.00  --res_forward_subs                      full
% 35.94/5.00  --res_backward_subs                     full
% 35.94/5.00  --res_forward_subs_resolution           true
% 35.94/5.00  --res_backward_subs_resolution          true
% 35.94/5.00  --res_orphan_elimination                true
% 35.94/5.00  --res_time_limit                        2.
% 35.94/5.00  --res_out_proof                         true
% 35.94/5.00  
% 35.94/5.00  ------ Superposition Options
% 35.94/5.00  
% 35.94/5.00  --superposition_flag                    true
% 35.94/5.00  --sup_passive_queue_type                priority_queues
% 35.94/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.94/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.94/5.00  --demod_completeness_check              fast
% 35.94/5.00  --demod_use_ground                      true
% 35.94/5.00  --sup_to_prop_solver                    passive
% 35.94/5.00  --sup_prop_simpl_new                    true
% 35.94/5.00  --sup_prop_simpl_given                  true
% 35.94/5.00  --sup_fun_splitting                     true
% 35.94/5.00  --sup_smt_interval                      50000
% 35.94/5.00  
% 35.94/5.00  ------ Superposition Simplification Setup
% 35.94/5.00  
% 35.94/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.94/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.94/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.94/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.94/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.94/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.94/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.94/5.00  --sup_immed_triv                        [TrivRules]
% 35.94/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.94/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.94/5.00  --sup_immed_bw_main                     []
% 35.94/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.94/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.94/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.94/5.00  --sup_input_bw                          []
% 35.94/5.00  
% 35.94/5.00  ------ Combination Options
% 35.94/5.00  
% 35.94/5.00  --comb_res_mult                         3
% 35.94/5.00  --comb_sup_mult                         2
% 35.94/5.00  --comb_inst_mult                        10
% 35.94/5.00  
% 35.94/5.00  ------ Debug Options
% 35.94/5.00  
% 35.94/5.00  --dbg_backtrace                         false
% 35.94/5.00  --dbg_dump_prop_clauses                 false
% 35.94/5.00  --dbg_dump_prop_clauses_file            -
% 35.94/5.00  --dbg_out_stat                          false
% 35.94/5.00  
% 35.94/5.00  
% 35.94/5.00  
% 35.94/5.00  
% 35.94/5.00  ------ Proving...
% 35.94/5.00  
% 35.94/5.00  
% 35.94/5.00  % SZS status Theorem for theBenchmark.p
% 35.94/5.00  
% 35.94/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.94/5.00  
% 35.94/5.00  fof(f9,conjecture,(
% 35.94/5.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f10,negated_conjecture,(
% 35.94/5.00    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.94/5.00    inference(negated_conjecture,[],[f9])).
% 35.94/5.00  
% 35.94/5.00  fof(f11,plain,(
% 35.94/5.00    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.94/5.00    inference(ennf_transformation,[],[f10])).
% 35.94/5.00  
% 35.94/5.00  fof(f13,plain,(
% 35.94/5.00    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 35.94/5.00    introduced(choice_axiom,[])).
% 35.94/5.00  
% 35.94/5.00  fof(f14,plain,(
% 35.94/5.00    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 35.94/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 35.94/5.00  
% 35.94/5.00  fof(f28,plain,(
% 35.94/5.00    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 35.94/5.00    inference(cnf_transformation,[],[f14])).
% 35.94/5.00  
% 35.94/5.00  fof(f2,axiom,(
% 35.94/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f12,plain,(
% 35.94/5.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.94/5.00    inference(nnf_transformation,[],[f2])).
% 35.94/5.00  
% 35.94/5.00  fof(f16,plain,(
% 35.94/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.94/5.00    inference(cnf_transformation,[],[f12])).
% 35.94/5.00  
% 35.94/5.00  fof(f8,axiom,(
% 35.94/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f23,plain,(
% 35.94/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.94/5.00    inference(cnf_transformation,[],[f8])).
% 35.94/5.00  
% 35.94/5.00  fof(f31,plain,(
% 35.94/5.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 35.94/5.00    inference(definition_unfolding,[],[f16,f23])).
% 35.94/5.00  
% 35.94/5.00  fof(f7,axiom,(
% 35.94/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f22,plain,(
% 35.94/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.94/5.00    inference(cnf_transformation,[],[f7])).
% 35.94/5.00  
% 35.94/5.00  fof(f33,plain,(
% 35.94/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 35.94/5.00    inference(definition_unfolding,[],[f22,f23])).
% 35.94/5.00  
% 35.94/5.00  fof(f6,axiom,(
% 35.94/5.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f21,plain,(
% 35.94/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 35.94/5.00    inference(cnf_transformation,[],[f6])).
% 35.94/5.00  
% 35.94/5.00  fof(f5,axiom,(
% 35.94/5.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f20,plain,(
% 35.94/5.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.94/5.00    inference(cnf_transformation,[],[f5])).
% 35.94/5.00  
% 35.94/5.00  fof(f3,axiom,(
% 35.94/5.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f18,plain,(
% 35.94/5.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 35.94/5.00    inference(cnf_transformation,[],[f3])).
% 35.94/5.00  
% 35.94/5.00  fof(f32,plain,(
% 35.94/5.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 35.94/5.00    inference(definition_unfolding,[],[f18,f23])).
% 35.94/5.00  
% 35.94/5.00  fof(f4,axiom,(
% 35.94/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f19,plain,(
% 35.94/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 35.94/5.00    inference(cnf_transformation,[],[f4])).
% 35.94/5.00  
% 35.94/5.00  fof(f1,axiom,(
% 35.94/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 35.94/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.94/5.00  
% 35.94/5.00  fof(f15,plain,(
% 35.94/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 35.94/5.00    inference(cnf_transformation,[],[f1])).
% 35.94/5.00  
% 35.94/5.00  fof(f29,plain,(
% 35.94/5.00    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 35.94/5.00    inference(cnf_transformation,[],[f14])).
% 35.94/5.00  
% 35.94/5.00  fof(f17,plain,(
% 35.94/5.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.94/5.00    inference(cnf_transformation,[],[f12])).
% 35.94/5.00  
% 35.94/5.00  fof(f30,plain,(
% 35.94/5.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.94/5.00    inference(definition_unfolding,[],[f17,f23])).
% 35.94/5.00  
% 35.94/5.00  fof(f24,plain,(
% 35.94/5.00    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 35.94/5.00    inference(cnf_transformation,[],[f14])).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9,negated_conjecture,
% 35.94/5.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1) ),
% 35.94/5.00      inference(cnf_transformation,[],[f28]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_331,plain,
% 35.94/5.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
% 35.94/5.00      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 35.94/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_2,plain,
% 35.94/5.00      ( ~ r1_xboole_0(X0,X1)
% 35.94/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.94/5.00      inference(cnf_transformation,[],[f31]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_333,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 35.94/5.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.94/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_949,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 35.94/5.00      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_331,c_333]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1238,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_949,c_333]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_7,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 35.94/5.00      inference(cnf_transformation,[],[f33]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_6,plain,
% 35.94/5.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.94/5.00      inference(cnf_transformation,[],[f21]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_557,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_562,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.94/5.00      inference(light_normalisation,[status(thm)],[c_557,c_6]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_7585,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_1238,c_562]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_5,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.94/5.00      inference(cnf_transformation,[],[f20]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_509,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_512,plain,
% 35.94/5.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_517,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_512,c_6]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_7731,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_7585,c_509,c_517]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_3,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 35.94/5.00      inference(cnf_transformation,[],[f32]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_335,plain,
% 35.94/5.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 35.94/5.00      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_515,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_6,c_335]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_4,plain,
% 35.94/5.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 35.94/5.00      inference(cnf_transformation,[],[f19]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_516,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_515,c_4]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_619,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_516,c_6]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_8820,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_7731,c_619]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_8836,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_8820,c_562]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9107,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_8836,c_509]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_26851,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_9107,c_6]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_26903,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK0,k2_xboole_0(X0,X1)) ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_26851,c_6,c_517]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_0,plain,
% 35.94/5.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 35.94/5.00      inference(cnf_transformation,[],[f15]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_505,plain,
% 35.94/5.00      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_335,c_4]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_572,plain,
% 35.94/5.00      ( k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_0,c_505]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_774,plain,
% 35.94/5.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_572,c_509]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_125032,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,X0))) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_26903,c_774]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_125130,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
% 35.94/5.00      inference(light_normalisation,[status(thm)],[c_125032,c_9107]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_8,negated_conjecture,
% 35.94/5.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2) ),
% 35.94/5.00      inference(cnf_transformation,[],[f29]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_332,plain,
% 35.94/5.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
% 35.94/5.00      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 35.94/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_948,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 35.94/5.00      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_332,c_333]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1197,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_948,c_333]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1242,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_1197,c_7]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1244,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_1242,c_5]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1351,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
% 35.94/5.00      | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_1244,c_7]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1353,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
% 35.94/5.00      | k4_xboole_0(sK0,sK2) = sK0 ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_1351,c_5]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_11919,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_1353,c_9107]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_11937,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_11919,c_6]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_125583,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK2) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_125130,c_11937]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_125609,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 35.94/5.00      inference(light_normalisation,[status(thm)],[c_125583,c_11919]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_169,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_2765,plain,
% 35.94/5.00      ( X0 != X1
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != X1
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = X0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_169]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9223,plain,
% 35.94/5.00      ( X0 != k4_xboole_0(X1,X2)
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = X0
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(X1,X2) ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_2765]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_33430,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(X0,X1)
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 35.94/5.00      | k1_xboole_0 != k4_xboole_0(X0,X1) ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_9223]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_33431,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK0)
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 35.94/5.00      | k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_33430]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_172,plain,
% 35.94/5.00      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 35.94/5.00      theory(equality) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9214,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(X0,X1)
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1
% 35.94/5.00      | sK0 != X0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_172]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9215,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK0)
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != sK0
% 35.94/5.00      | sK0 != sK0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_9214]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_7586,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_1197,c_562]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_7730,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_7586,c_509,c_517]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_8658,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
% 35.94/5.00      inference(superposition,[status(thm)],[c_4,c_7730]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9136,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_8658,c_9107]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9184,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
% 35.94/5.00      | k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)) != k1_xboole_0 ),
% 35.94/5.00      inference(equality_factoring,[status(thm)],[c_9136]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9185,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 35.94/5.00      | k1_xboole_0 != k1_xboole_0 ),
% 35.94/5.00      inference(demodulation,[status(thm)],[c_9184,c_516]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_9186,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 35.94/5.00      inference(equality_resolution_simp,[status(thm)],[c_9185]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1,plain,
% 35.94/5.00      ( r1_xboole_0(X0,X1)
% 35.94/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 35.94/5.00      inference(cnf_transformation,[],[f30]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_2273,plain,
% 35.94/5.00      ( r1_xboole_0(sK0,sK1)
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_1]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_367,plain,
% 35.94/5.00      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_169]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_390,plain,
% 35.94/5.00      ( X0 != k1_xboole_0
% 35.94/5.00      | k1_xboole_0 = X0
% 35.94/5.00      | k1_xboole_0 != k1_xboole_0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_367]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1295,plain,
% 35.94/5.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 35.94/5.00      | k1_xboole_0 = k4_xboole_0(X0,X1)
% 35.94/5.00      | k1_xboole_0 != k1_xboole_0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_390]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_1296,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,sK0) != k1_xboole_0
% 35.94/5.00      | k1_xboole_0 = k4_xboole_0(sK0,sK0)
% 35.94/5.00      | k1_xboole_0 != k1_xboole_0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_1295]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_831,plain,
% 35.94/5.00      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k1_xboole_0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_1]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_168,plain,( X0 = X0 ),theory(equality) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_418,plain,
% 35.94/5.00      ( k1_xboole_0 = k1_xboole_0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_168]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_345,plain,
% 35.94/5.00      ( r1_xboole_0(sK0,sK2)
% 35.94/5.00      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_1]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_337,plain,
% 35.94/5.00      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_335]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_176,plain,
% 35.94/5.00      ( sK0 = sK0 ),
% 35.94/5.00      inference(instantiation,[status(thm)],[c_168]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(c_13,negated_conjecture,
% 35.94/5.00      ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 35.94/5.00      | ~ r1_xboole_0(sK0,sK2)
% 35.94/5.00      | ~ r1_xboole_0(sK0,sK1) ),
% 35.94/5.00      inference(cnf_transformation,[],[f24]) ).
% 35.94/5.00  
% 35.94/5.00  cnf(contradiction,plain,
% 35.94/5.00      ( $false ),
% 35.94/5.00      inference(minisat,
% 35.94/5.00                [status(thm)],
% 35.94/5.00                [c_125609,c_33431,c_9215,c_9186,c_8820,c_2273,c_1296,
% 35.94/5.00                 c_831,c_418,c_345,c_337,c_176,c_13]) ).
% 35.94/5.00  
% 35.94/5.00  
% 35.94/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.94/5.00  
% 35.94/5.00  ------                               Statistics
% 35.94/5.00  
% 35.94/5.00  ------ General
% 35.94/5.00  
% 35.94/5.00  abstr_ref_over_cycles:                  0
% 35.94/5.00  abstr_ref_under_cycles:                 0
% 35.94/5.00  gc_basic_clause_elim:                   0
% 35.94/5.00  forced_gc_time:                         0
% 35.94/5.00  parsing_time:                           0.007
% 35.94/5.00  unif_index_cands_time:                  0.
% 35.94/5.00  unif_index_add_time:                    0.
% 35.94/5.00  orderings_time:                         0.
% 35.94/5.00  out_proof_time:                         0.015
% 35.94/5.00  total_time:                             4.472
% 35.94/5.00  num_of_symbols:                         38
% 35.94/5.00  num_of_terms:                           204112
% 35.94/5.00  
% 35.94/5.00  ------ Preprocessing
% 35.94/5.00  
% 35.94/5.00  num_of_splits:                          0
% 35.94/5.00  num_of_split_atoms:                     0
% 35.94/5.00  num_of_reused_defs:                     0
% 35.94/5.00  num_eq_ax_congr_red:                    0
% 35.94/5.00  num_of_sem_filtered_clauses:            1
% 35.94/5.00  num_of_subtypes:                        0
% 35.94/5.00  monotx_restored_types:                  0
% 35.94/5.00  sat_num_of_epr_types:                   0
% 35.94/5.00  sat_num_of_non_cyclic_types:            0
% 35.94/5.00  sat_guarded_non_collapsed_types:        0
% 35.94/5.00  num_pure_diseq_elim:                    0
% 35.94/5.00  simp_replaced_by:                       0
% 35.94/5.00  res_preprocessed:                       55
% 35.94/5.00  prep_upred:                             0
% 35.94/5.00  prep_unflattend:                        0
% 35.94/5.00  smt_new_axioms:                         0
% 35.94/5.00  pred_elim_cands:                        1
% 35.94/5.00  pred_elim:                              0
% 35.94/5.00  pred_elim_cl:                           0
% 35.94/5.00  pred_elim_cycles:                       2
% 35.94/5.00  merged_defs:                            8
% 35.94/5.00  merged_defs_ncl:                        0
% 35.94/5.00  bin_hyper_res:                          8
% 35.94/5.00  prep_cycles:                            4
% 35.94/5.00  pred_elim_time:                         0.
% 35.94/5.00  splitting_time:                         0.
% 35.94/5.00  sem_filter_time:                        0.
% 35.94/5.00  monotx_time:                            0.
% 35.94/5.00  subtype_inf_time:                       0.
% 35.94/5.00  
% 35.94/5.00  ------ Problem properties
% 35.94/5.00  
% 35.94/5.00  clauses:                                11
% 35.94/5.00  conjectures:                            3
% 35.94/5.00  epr:                                    0
% 35.94/5.00  horn:                                   9
% 35.94/5.00  ground:                                 3
% 35.94/5.00  unary:                                  6
% 35.94/5.00  binary:                                 4
% 35.94/5.00  lits:                                   17
% 35.94/5.00  lits_eq:                                8
% 35.94/5.00  fd_pure:                                0
% 35.94/5.00  fd_pseudo:                              0
% 35.94/5.00  fd_cond:                                0
% 35.94/5.00  fd_pseudo_cond:                         0
% 35.94/5.00  ac_symbols:                             0
% 35.94/5.00  
% 35.94/5.00  ------ Propositional Solver
% 35.94/5.00  
% 35.94/5.00  prop_solver_calls:                      40
% 35.94/5.00  prop_fast_solver_calls:                 1048
% 35.94/5.00  smt_solver_calls:                       0
% 35.94/5.00  smt_fast_solver_calls:                  0
% 35.94/5.00  prop_num_of_clauses:                    33445
% 35.94/5.00  prop_preprocess_simplified:             32092
% 35.94/5.00  prop_fo_subsumed:                       98
% 35.94/5.00  prop_solver_time:                       0.
% 35.94/5.00  smt_solver_time:                        0.
% 35.94/5.00  smt_fast_solver_time:                   0.
% 35.94/5.00  prop_fast_solver_time:                  0.
% 35.94/5.00  prop_unsat_core_time:                   0.004
% 35.94/5.00  
% 35.94/5.00  ------ QBF
% 35.94/5.00  
% 35.94/5.00  qbf_q_res:                              0
% 35.94/5.00  qbf_num_tautologies:                    0
% 35.94/5.00  qbf_prep_cycles:                        0
% 35.94/5.00  
% 35.94/5.00  ------ BMC1
% 35.94/5.00  
% 35.94/5.00  bmc1_current_bound:                     -1
% 35.94/5.00  bmc1_last_solved_bound:                 -1
% 35.94/5.00  bmc1_unsat_core_size:                   -1
% 35.94/5.00  bmc1_unsat_core_parents_size:           -1
% 35.94/5.00  bmc1_merge_next_fun:                    0
% 35.94/5.00  bmc1_unsat_core_clauses_time:           0.
% 35.94/5.00  
% 35.94/5.00  ------ Instantiation
% 35.94/5.00  
% 35.94/5.00  inst_num_of_clauses:                    6410
% 35.94/5.00  inst_num_in_passive:                    4509
% 35.94/5.00  inst_num_in_active:                     1481
% 35.94/5.00  inst_num_in_unprocessed:                420
% 35.94/5.00  inst_num_of_loops:                      1870
% 35.94/5.00  inst_num_of_learning_restarts:          0
% 35.94/5.00  inst_num_moves_active_passive:          382
% 35.94/5.00  inst_lit_activity:                      0
% 35.94/5.00  inst_lit_activity_moves:                2
% 35.94/5.00  inst_num_tautologies:                   0
% 35.94/5.00  inst_num_prop_implied:                  0
% 35.94/5.00  inst_num_existing_simplified:           0
% 35.94/5.00  inst_num_eq_res_simplified:             0
% 35.94/5.00  inst_num_child_elim:                    0
% 35.94/5.00  inst_num_of_dismatching_blockings:      5967
% 35.94/5.00  inst_num_of_non_proper_insts:           6791
% 35.94/5.00  inst_num_of_duplicates:                 0
% 35.94/5.00  inst_inst_num_from_inst_to_res:         0
% 35.94/5.00  inst_dismatching_checking_time:         0.
% 35.94/5.00  
% 35.94/5.00  ------ Resolution
% 35.94/5.00  
% 35.94/5.00  res_num_of_clauses:                     0
% 35.94/5.00  res_num_in_passive:                     0
% 35.94/5.00  res_num_in_active:                      0
% 35.94/5.00  res_num_of_loops:                       59
% 35.94/5.00  res_forward_subset_subsumed:            630
% 35.94/5.00  res_backward_subset_subsumed:           0
% 35.94/5.00  res_forward_subsumed:                   0
% 35.94/5.00  res_backward_subsumed:                  0
% 35.94/5.00  res_forward_subsumption_resolution:     0
% 35.94/5.00  res_backward_subsumption_resolution:    0
% 35.94/5.00  res_clause_to_clause_subsumption:       379340
% 35.94/5.00  res_orphan_elimination:                 0
% 35.94/5.00  res_tautology_del:                      338
% 35.94/5.00  res_num_eq_res_simplified:              0
% 35.94/5.00  res_num_sel_changes:                    0
% 35.94/5.00  res_moves_from_active_to_pass:          0
% 35.94/5.00  
% 35.94/5.00  ------ Superposition
% 35.94/5.00  
% 35.94/5.00  sup_time_total:                         0.
% 35.94/5.00  sup_time_generating:                    0.
% 35.94/5.00  sup_time_sim_full:                      0.
% 35.94/5.00  sup_time_sim_immed:                     0.
% 35.94/5.00  
% 35.94/5.00  sup_num_of_clauses:                     10623
% 35.94/5.00  sup_num_in_active:                      291
% 35.94/5.00  sup_num_in_passive:                     10332
% 35.94/5.00  sup_num_of_loops:                       373
% 35.94/5.00  sup_fw_superposition:                   26015
% 35.94/5.00  sup_bw_superposition:                   25905
% 35.94/5.00  sup_immediate_simplified:               31188
% 35.94/5.00  sup_given_eliminated:                   6
% 35.94/5.00  comparisons_done:                       0
% 35.94/5.00  comparisons_avoided:                    70
% 35.94/5.00  
% 35.94/5.00  ------ Simplifications
% 35.94/5.00  
% 35.94/5.00  
% 35.94/5.00  sim_fw_subset_subsumed:                 84
% 35.94/5.00  sim_bw_subset_subsumed:                 147
% 35.94/5.00  sim_fw_subsumed:                        8012
% 35.94/5.00  sim_bw_subsumed:                        204
% 35.94/5.00  sim_fw_subsumption_res:                 0
% 35.94/5.00  sim_bw_subsumption_res:                 0
% 35.94/5.00  sim_tautology_del:                      3
% 35.94/5.00  sim_eq_tautology_del:                   9744
% 35.94/5.00  sim_eq_res_simp:                        132
% 35.94/5.00  sim_fw_demodulated:                     19927
% 35.94/5.00  sim_bw_demodulated:                     226
% 35.94/5.00  sim_light_normalised:                   8484
% 35.94/5.00  sim_joinable_taut:                      0
% 35.94/5.00  sim_joinable_simp:                      0
% 35.94/5.00  sim_ac_normalised:                      0
% 35.94/5.00  sim_smt_subsumption:                    0
% 35.94/5.00  
%------------------------------------------------------------------------------
