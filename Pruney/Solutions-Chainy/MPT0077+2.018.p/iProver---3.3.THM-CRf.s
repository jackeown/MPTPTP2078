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
% DateTime   : Thu Dec  3 11:23:39 EST 2020

% Result     : Theorem 55.48s
% Output     : CNFRefutation 55.48s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 814 expanded)
%              Number of clauses        :   73 ( 348 expanded)
%              Number of leaves         :   13 ( 206 expanded)
%              Depth                    :   21
%              Number of atoms          :  208 (1250 expanded)
%              Number of equality atoms :  146 ( 875 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

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

fof(f29,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
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

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f23])).

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

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_332,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_333,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_947,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_332,c_333])).

cnf(c_1193,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_947,c_333])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1263,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1193,c_7])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_442,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_515,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_442,c_5])).

cnf(c_517,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_515,c_442])).

cnf(c_1266,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_1263,c_517])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_575,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_580,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_575,c_6])).

cnf(c_8005,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0))
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(superposition,[status(thm)],[c_1266,c_580])).

cnf(c_8178,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
    | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_8005,c_442])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_331,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_948,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_331,c_333])).

cnf(c_1195,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_948,c_333])).

cnf(c_8007,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1195,c_580])).

cnf(c_8175,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_8007,c_442])).

cnf(c_562,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_566,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_562,c_6])).

cnf(c_8176,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_8175,c_566])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_519,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_4,c_517])).

cnf(c_564,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_519])).

cnf(c_565,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_564,c_5])).

cnf(c_716,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_565,c_6])).

cnf(c_8983,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8176,c_716])).

cnf(c_9040,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_8983,c_580])).

cnf(c_9231,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_9040,c_442])).

cnf(c_9321,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
    | k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_8178,c_9231])).

cnf(c_9334,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | k4_xboole_0(sK0,sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_3,c_9321])).

cnf(c_9403,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_9334,c_517])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_334,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_49777,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9231,c_334])).

cnf(c_175523,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9403,c_49777])).

cnf(c_175738,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_175523,c_519])).

cnf(c_175739,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_175738])).

cnf(c_169,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_22246,plain,
    ( k4_xboole_0(X0,k1_xboole_0) != X1
    | k4_xboole_0(sK0,sK2) != X1
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_22247,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | k4_xboole_0(sK0,sK2) != sK0
    | k4_xboole_0(sK0,k1_xboole_0) != sK0 ),
    inference(instantiation,[status(thm)],[c_22246])).

cnf(c_172,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_1697,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(X0,k1_xboole_0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_1698,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k1_xboole_0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_1206,plain,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1208,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_354,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_455,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_1196,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_1197,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_365,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_388,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_435,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_594,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_595,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_518,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_168,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_416,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_343,plain,
    ( r1_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_344,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_176,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_23,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != iProver_top
    | r1_xboole_0(sK0,sK2) != iProver_top
    | r1_xboole_0(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_175739,c_22247,c_9403,c_8983,c_1698,c_1208,c_1197,c_595,c_518,c_416,c_344,c_176,c_23,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.48/7.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.48/7.53  
% 55.48/7.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.48/7.53  
% 55.48/7.53  ------  iProver source info
% 55.48/7.53  
% 55.48/7.53  git: date: 2020-06-30 10:37:57 +0100
% 55.48/7.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.48/7.53  git: non_committed_changes: false
% 55.48/7.53  git: last_make_outside_of_git: false
% 55.48/7.53  
% 55.48/7.53  ------ 
% 55.48/7.53  
% 55.48/7.53  ------ Input Options
% 55.48/7.53  
% 55.48/7.53  --out_options                           all
% 55.48/7.53  --tptp_safe_out                         true
% 55.48/7.53  --problem_path                          ""
% 55.48/7.53  --include_path                          ""
% 55.48/7.53  --clausifier                            res/vclausify_rel
% 55.48/7.53  --clausifier_options                    ""
% 55.48/7.53  --stdin                                 false
% 55.48/7.53  --stats_out                             all
% 55.48/7.53  
% 55.48/7.53  ------ General Options
% 55.48/7.53  
% 55.48/7.53  --fof                                   false
% 55.48/7.53  --time_out_real                         305.
% 55.48/7.53  --time_out_virtual                      -1.
% 55.48/7.53  --symbol_type_check                     false
% 55.48/7.53  --clausify_out                          false
% 55.48/7.53  --sig_cnt_out                           false
% 55.48/7.53  --trig_cnt_out                          false
% 55.48/7.53  --trig_cnt_out_tolerance                1.
% 55.48/7.53  --trig_cnt_out_sk_spl                   false
% 55.48/7.53  --abstr_cl_out                          false
% 55.48/7.53  
% 55.48/7.53  ------ Global Options
% 55.48/7.53  
% 55.48/7.53  --schedule                              default
% 55.48/7.53  --add_important_lit                     false
% 55.48/7.53  --prop_solver_per_cl                    1000
% 55.48/7.53  --min_unsat_core                        false
% 55.48/7.53  --soft_assumptions                      false
% 55.48/7.53  --soft_lemma_size                       3
% 55.48/7.53  --prop_impl_unit_size                   0
% 55.48/7.53  --prop_impl_unit                        []
% 55.48/7.53  --share_sel_clauses                     true
% 55.48/7.53  --reset_solvers                         false
% 55.48/7.53  --bc_imp_inh                            [conj_cone]
% 55.48/7.53  --conj_cone_tolerance                   3.
% 55.48/7.53  --extra_neg_conj                        none
% 55.48/7.53  --large_theory_mode                     true
% 55.48/7.53  --prolific_symb_bound                   200
% 55.48/7.53  --lt_threshold                          2000
% 55.48/7.53  --clause_weak_htbl                      true
% 55.48/7.53  --gc_record_bc_elim                     false
% 55.48/7.53  
% 55.48/7.53  ------ Preprocessing Options
% 55.48/7.53  
% 55.48/7.53  --preprocessing_flag                    true
% 55.48/7.53  --time_out_prep_mult                    0.1
% 55.48/7.53  --splitting_mode                        input
% 55.48/7.53  --splitting_grd                         true
% 55.48/7.53  --splitting_cvd                         false
% 55.48/7.53  --splitting_cvd_svl                     false
% 55.48/7.53  --splitting_nvd                         32
% 55.48/7.53  --sub_typing                            true
% 55.48/7.53  --prep_gs_sim                           true
% 55.48/7.53  --prep_unflatten                        true
% 55.48/7.53  --prep_res_sim                          true
% 55.48/7.53  --prep_upred                            true
% 55.48/7.53  --prep_sem_filter                       exhaustive
% 55.48/7.53  --prep_sem_filter_out                   false
% 55.48/7.53  --pred_elim                             true
% 55.48/7.53  --res_sim_input                         true
% 55.48/7.53  --eq_ax_congr_red                       true
% 55.48/7.53  --pure_diseq_elim                       true
% 55.48/7.53  --brand_transform                       false
% 55.48/7.53  --non_eq_to_eq                          false
% 55.48/7.53  --prep_def_merge                        true
% 55.48/7.53  --prep_def_merge_prop_impl              false
% 55.48/7.53  --prep_def_merge_mbd                    true
% 55.48/7.53  --prep_def_merge_tr_red                 false
% 55.48/7.53  --prep_def_merge_tr_cl                  false
% 55.48/7.53  --smt_preprocessing                     true
% 55.48/7.53  --smt_ac_axioms                         fast
% 55.48/7.53  --preprocessed_out                      false
% 55.48/7.53  --preprocessed_stats                    false
% 55.48/7.53  
% 55.48/7.53  ------ Abstraction refinement Options
% 55.48/7.53  
% 55.48/7.53  --abstr_ref                             []
% 55.48/7.53  --abstr_ref_prep                        false
% 55.48/7.53  --abstr_ref_until_sat                   false
% 55.48/7.53  --abstr_ref_sig_restrict                funpre
% 55.48/7.53  --abstr_ref_af_restrict_to_split_sk     false
% 55.48/7.53  --abstr_ref_under                       []
% 55.48/7.53  
% 55.48/7.53  ------ SAT Options
% 55.48/7.53  
% 55.48/7.53  --sat_mode                              false
% 55.48/7.53  --sat_fm_restart_options                ""
% 55.48/7.53  --sat_gr_def                            false
% 55.48/7.53  --sat_epr_types                         true
% 55.48/7.53  --sat_non_cyclic_types                  false
% 55.48/7.53  --sat_finite_models                     false
% 55.48/7.53  --sat_fm_lemmas                         false
% 55.48/7.53  --sat_fm_prep                           false
% 55.48/7.53  --sat_fm_uc_incr                        true
% 55.48/7.53  --sat_out_model                         small
% 55.48/7.53  --sat_out_clauses                       false
% 55.48/7.53  
% 55.48/7.53  ------ QBF Options
% 55.48/7.53  
% 55.48/7.53  --qbf_mode                              false
% 55.48/7.53  --qbf_elim_univ                         false
% 55.48/7.53  --qbf_dom_inst                          none
% 55.48/7.53  --qbf_dom_pre_inst                      false
% 55.48/7.53  --qbf_sk_in                             false
% 55.48/7.53  --qbf_pred_elim                         true
% 55.48/7.53  --qbf_split                             512
% 55.48/7.53  
% 55.48/7.53  ------ BMC1 Options
% 55.48/7.53  
% 55.48/7.53  --bmc1_incremental                      false
% 55.48/7.53  --bmc1_axioms                           reachable_all
% 55.48/7.53  --bmc1_min_bound                        0
% 55.48/7.53  --bmc1_max_bound                        -1
% 55.48/7.53  --bmc1_max_bound_default                -1
% 55.48/7.53  --bmc1_symbol_reachability              true
% 55.48/7.53  --bmc1_property_lemmas                  false
% 55.48/7.53  --bmc1_k_induction                      false
% 55.48/7.53  --bmc1_non_equiv_states                 false
% 55.48/7.53  --bmc1_deadlock                         false
% 55.48/7.53  --bmc1_ucm                              false
% 55.48/7.53  --bmc1_add_unsat_core                   none
% 55.48/7.53  --bmc1_unsat_core_children              false
% 55.48/7.53  --bmc1_unsat_core_extrapolate_axioms    false
% 55.48/7.53  --bmc1_out_stat                         full
% 55.48/7.53  --bmc1_ground_init                      false
% 55.48/7.53  --bmc1_pre_inst_next_state              false
% 55.48/7.53  --bmc1_pre_inst_state                   false
% 55.48/7.53  --bmc1_pre_inst_reach_state             false
% 55.48/7.53  --bmc1_out_unsat_core                   false
% 55.48/7.53  --bmc1_aig_witness_out                  false
% 55.48/7.53  --bmc1_verbose                          false
% 55.48/7.53  --bmc1_dump_clauses_tptp                false
% 55.48/7.53  --bmc1_dump_unsat_core_tptp             false
% 55.48/7.53  --bmc1_dump_file                        -
% 55.48/7.53  --bmc1_ucm_expand_uc_limit              128
% 55.48/7.53  --bmc1_ucm_n_expand_iterations          6
% 55.48/7.53  --bmc1_ucm_extend_mode                  1
% 55.48/7.53  --bmc1_ucm_init_mode                    2
% 55.48/7.53  --bmc1_ucm_cone_mode                    none
% 55.48/7.53  --bmc1_ucm_reduced_relation_type        0
% 55.48/7.53  --bmc1_ucm_relax_model                  4
% 55.48/7.53  --bmc1_ucm_full_tr_after_sat            true
% 55.48/7.53  --bmc1_ucm_expand_neg_assumptions       false
% 55.48/7.53  --bmc1_ucm_layered_model                none
% 55.48/7.53  --bmc1_ucm_max_lemma_size               10
% 55.48/7.53  
% 55.48/7.53  ------ AIG Options
% 55.48/7.53  
% 55.48/7.53  --aig_mode                              false
% 55.48/7.53  
% 55.48/7.53  ------ Instantiation Options
% 55.48/7.53  
% 55.48/7.53  --instantiation_flag                    true
% 55.48/7.53  --inst_sos_flag                         true
% 55.48/7.53  --inst_sos_phase                        true
% 55.48/7.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.48/7.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.48/7.53  --inst_lit_sel_side                     num_symb
% 55.48/7.53  --inst_solver_per_active                1400
% 55.48/7.53  --inst_solver_calls_frac                1.
% 55.48/7.53  --inst_passive_queue_type               priority_queues
% 55.48/7.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.48/7.53  --inst_passive_queues_freq              [25;2]
% 55.48/7.53  --inst_dismatching                      true
% 55.48/7.53  --inst_eager_unprocessed_to_passive     true
% 55.48/7.53  --inst_prop_sim_given                   true
% 55.48/7.53  --inst_prop_sim_new                     false
% 55.48/7.53  --inst_subs_new                         false
% 55.48/7.53  --inst_eq_res_simp                      false
% 55.48/7.53  --inst_subs_given                       false
% 55.48/7.53  --inst_orphan_elimination               true
% 55.48/7.53  --inst_learning_loop_flag               true
% 55.48/7.53  --inst_learning_start                   3000
% 55.48/7.53  --inst_learning_factor                  2
% 55.48/7.53  --inst_start_prop_sim_after_learn       3
% 55.48/7.53  --inst_sel_renew                        solver
% 55.48/7.53  --inst_lit_activity_flag                true
% 55.48/7.53  --inst_restr_to_given                   false
% 55.48/7.53  --inst_activity_threshold               500
% 55.48/7.53  --inst_out_proof                        true
% 55.48/7.53  
% 55.48/7.53  ------ Resolution Options
% 55.48/7.53  
% 55.48/7.53  --resolution_flag                       true
% 55.48/7.53  --res_lit_sel                           adaptive
% 55.48/7.53  --res_lit_sel_side                      none
% 55.48/7.53  --res_ordering                          kbo
% 55.48/7.53  --res_to_prop_solver                    active
% 55.48/7.53  --res_prop_simpl_new                    false
% 55.48/7.53  --res_prop_simpl_given                  true
% 55.48/7.53  --res_passive_queue_type                priority_queues
% 55.48/7.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.48/7.53  --res_passive_queues_freq               [15;5]
% 55.48/7.53  --res_forward_subs                      full
% 55.48/7.53  --res_backward_subs                     full
% 55.48/7.53  --res_forward_subs_resolution           true
% 55.48/7.53  --res_backward_subs_resolution          true
% 55.48/7.53  --res_orphan_elimination                true
% 55.48/7.53  --res_time_limit                        2.
% 55.48/7.53  --res_out_proof                         true
% 55.48/7.53  
% 55.48/7.53  ------ Superposition Options
% 55.48/7.53  
% 55.48/7.53  --superposition_flag                    true
% 55.48/7.53  --sup_passive_queue_type                priority_queues
% 55.48/7.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.48/7.53  --sup_passive_queues_freq               [8;1;4]
% 55.48/7.53  --demod_completeness_check              fast
% 55.48/7.53  --demod_use_ground                      true
% 55.48/7.53  --sup_to_prop_solver                    passive
% 55.48/7.53  --sup_prop_simpl_new                    true
% 55.48/7.53  --sup_prop_simpl_given                  true
% 55.48/7.53  --sup_fun_splitting                     true
% 55.48/7.53  --sup_smt_interval                      50000
% 55.48/7.53  
% 55.48/7.53  ------ Superposition Simplification Setup
% 55.48/7.53  
% 55.48/7.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.48/7.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.48/7.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.48/7.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.48/7.53  --sup_full_triv                         [TrivRules;PropSubs]
% 55.48/7.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.48/7.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.48/7.53  --sup_immed_triv                        [TrivRules]
% 55.48/7.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.48/7.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.48/7.53  --sup_immed_bw_main                     []
% 55.48/7.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.48/7.53  --sup_input_triv                        [Unflattening;TrivRules]
% 55.48/7.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.48/7.53  --sup_input_bw                          []
% 55.48/7.53  
% 55.48/7.53  ------ Combination Options
% 55.48/7.53  
% 55.48/7.53  --comb_res_mult                         3
% 55.48/7.53  --comb_sup_mult                         2
% 55.48/7.53  --comb_inst_mult                        10
% 55.48/7.53  
% 55.48/7.53  ------ Debug Options
% 55.48/7.53  
% 55.48/7.53  --dbg_backtrace                         false
% 55.48/7.53  --dbg_dump_prop_clauses                 false
% 55.48/7.53  --dbg_dump_prop_clauses_file            -
% 55.48/7.53  --dbg_out_stat                          false
% 55.48/7.53  ------ Parsing...
% 55.48/7.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.48/7.53  
% 55.48/7.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.48/7.53  
% 55.48/7.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.48/7.53  
% 55.48/7.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.48/7.53  ------ Proving...
% 55.48/7.53  ------ Problem Properties 
% 55.48/7.53  
% 55.48/7.53  
% 55.48/7.53  clauses                                 11
% 55.48/7.53  conjectures                             3
% 55.48/7.53  EPR                                     0
% 55.48/7.53  Horn                                    9
% 55.48/7.53  unary                                   6
% 55.48/7.53  binary                                  4
% 55.48/7.53  lits                                    17
% 55.48/7.53  lits eq                                 8
% 55.48/7.53  fd_pure                                 0
% 55.48/7.53  fd_pseudo                               0
% 55.48/7.53  fd_cond                                 0
% 55.48/7.53  fd_pseudo_cond                          0
% 55.48/7.53  AC symbols                              0
% 55.48/7.53  
% 55.48/7.53  ------ Schedule dynamic 5 is on 
% 55.48/7.53  
% 55.48/7.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.48/7.53  
% 55.48/7.53  
% 55.48/7.53  ------ 
% 55.48/7.53  Current options:
% 55.48/7.53  ------ 
% 55.48/7.53  
% 55.48/7.53  ------ Input Options
% 55.48/7.53  
% 55.48/7.53  --out_options                           all
% 55.48/7.53  --tptp_safe_out                         true
% 55.48/7.53  --problem_path                          ""
% 55.48/7.53  --include_path                          ""
% 55.48/7.53  --clausifier                            res/vclausify_rel
% 55.48/7.53  --clausifier_options                    ""
% 55.48/7.53  --stdin                                 false
% 55.48/7.53  --stats_out                             all
% 55.48/7.53  
% 55.48/7.53  ------ General Options
% 55.48/7.53  
% 55.48/7.53  --fof                                   false
% 55.48/7.53  --time_out_real                         305.
% 55.48/7.53  --time_out_virtual                      -1.
% 55.48/7.53  --symbol_type_check                     false
% 55.48/7.53  --clausify_out                          false
% 55.48/7.53  --sig_cnt_out                           false
% 55.48/7.53  --trig_cnt_out                          false
% 55.48/7.53  --trig_cnt_out_tolerance                1.
% 55.48/7.53  --trig_cnt_out_sk_spl                   false
% 55.48/7.53  --abstr_cl_out                          false
% 55.48/7.53  
% 55.48/7.53  ------ Global Options
% 55.48/7.53  
% 55.48/7.53  --schedule                              default
% 55.48/7.53  --add_important_lit                     false
% 55.48/7.53  --prop_solver_per_cl                    1000
% 55.48/7.53  --min_unsat_core                        false
% 55.48/7.53  --soft_assumptions                      false
% 55.48/7.53  --soft_lemma_size                       3
% 55.48/7.53  --prop_impl_unit_size                   0
% 55.48/7.53  --prop_impl_unit                        []
% 55.48/7.53  --share_sel_clauses                     true
% 55.48/7.53  --reset_solvers                         false
% 55.48/7.53  --bc_imp_inh                            [conj_cone]
% 55.48/7.53  --conj_cone_tolerance                   3.
% 55.48/7.53  --extra_neg_conj                        none
% 55.48/7.53  --large_theory_mode                     true
% 55.48/7.53  --prolific_symb_bound                   200
% 55.48/7.53  --lt_threshold                          2000
% 55.48/7.53  --clause_weak_htbl                      true
% 55.48/7.53  --gc_record_bc_elim                     false
% 55.48/7.53  
% 55.48/7.53  ------ Preprocessing Options
% 55.48/7.53  
% 55.48/7.53  --preprocessing_flag                    true
% 55.48/7.53  --time_out_prep_mult                    0.1
% 55.48/7.53  --splitting_mode                        input
% 55.48/7.53  --splitting_grd                         true
% 55.48/7.53  --splitting_cvd                         false
% 55.48/7.53  --splitting_cvd_svl                     false
% 55.48/7.53  --splitting_nvd                         32
% 55.48/7.53  --sub_typing                            true
% 55.48/7.53  --prep_gs_sim                           true
% 55.48/7.53  --prep_unflatten                        true
% 55.48/7.53  --prep_res_sim                          true
% 55.48/7.53  --prep_upred                            true
% 55.48/7.53  --prep_sem_filter                       exhaustive
% 55.48/7.53  --prep_sem_filter_out                   false
% 55.48/7.53  --pred_elim                             true
% 55.48/7.53  --res_sim_input                         true
% 55.48/7.53  --eq_ax_congr_red                       true
% 55.48/7.53  --pure_diseq_elim                       true
% 55.48/7.53  --brand_transform                       false
% 55.48/7.53  --non_eq_to_eq                          false
% 55.48/7.53  --prep_def_merge                        true
% 55.48/7.53  --prep_def_merge_prop_impl              false
% 55.48/7.53  --prep_def_merge_mbd                    true
% 55.48/7.53  --prep_def_merge_tr_red                 false
% 55.48/7.53  --prep_def_merge_tr_cl                  false
% 55.48/7.53  --smt_preprocessing                     true
% 55.48/7.53  --smt_ac_axioms                         fast
% 55.48/7.53  --preprocessed_out                      false
% 55.48/7.53  --preprocessed_stats                    false
% 55.48/7.53  
% 55.48/7.53  ------ Abstraction refinement Options
% 55.48/7.53  
% 55.48/7.53  --abstr_ref                             []
% 55.48/7.53  --abstr_ref_prep                        false
% 55.48/7.53  --abstr_ref_until_sat                   false
% 55.48/7.53  --abstr_ref_sig_restrict                funpre
% 55.48/7.53  --abstr_ref_af_restrict_to_split_sk     false
% 55.48/7.53  --abstr_ref_under                       []
% 55.48/7.53  
% 55.48/7.53  ------ SAT Options
% 55.48/7.53  
% 55.48/7.53  --sat_mode                              false
% 55.48/7.53  --sat_fm_restart_options                ""
% 55.48/7.53  --sat_gr_def                            false
% 55.48/7.53  --sat_epr_types                         true
% 55.48/7.53  --sat_non_cyclic_types                  false
% 55.48/7.53  --sat_finite_models                     false
% 55.48/7.53  --sat_fm_lemmas                         false
% 55.48/7.53  --sat_fm_prep                           false
% 55.48/7.53  --sat_fm_uc_incr                        true
% 55.48/7.53  --sat_out_model                         small
% 55.48/7.53  --sat_out_clauses                       false
% 55.48/7.53  
% 55.48/7.53  ------ QBF Options
% 55.48/7.53  
% 55.48/7.53  --qbf_mode                              false
% 55.48/7.53  --qbf_elim_univ                         false
% 55.48/7.53  --qbf_dom_inst                          none
% 55.48/7.53  --qbf_dom_pre_inst                      false
% 55.48/7.53  --qbf_sk_in                             false
% 55.48/7.53  --qbf_pred_elim                         true
% 55.48/7.53  --qbf_split                             512
% 55.48/7.53  
% 55.48/7.53  ------ BMC1 Options
% 55.48/7.53  
% 55.48/7.53  --bmc1_incremental                      false
% 55.48/7.53  --bmc1_axioms                           reachable_all
% 55.48/7.53  --bmc1_min_bound                        0
% 55.48/7.53  --bmc1_max_bound                        -1
% 55.48/7.53  --bmc1_max_bound_default                -1
% 55.48/7.53  --bmc1_symbol_reachability              true
% 55.48/7.53  --bmc1_property_lemmas                  false
% 55.48/7.53  --bmc1_k_induction                      false
% 55.48/7.53  --bmc1_non_equiv_states                 false
% 55.48/7.53  --bmc1_deadlock                         false
% 55.48/7.53  --bmc1_ucm                              false
% 55.48/7.53  --bmc1_add_unsat_core                   none
% 55.48/7.53  --bmc1_unsat_core_children              false
% 55.48/7.53  --bmc1_unsat_core_extrapolate_axioms    false
% 55.48/7.53  --bmc1_out_stat                         full
% 55.48/7.53  --bmc1_ground_init                      false
% 55.48/7.53  --bmc1_pre_inst_next_state              false
% 55.48/7.53  --bmc1_pre_inst_state                   false
% 55.48/7.53  --bmc1_pre_inst_reach_state             false
% 55.48/7.53  --bmc1_out_unsat_core                   false
% 55.48/7.53  --bmc1_aig_witness_out                  false
% 55.48/7.53  --bmc1_verbose                          false
% 55.48/7.53  --bmc1_dump_clauses_tptp                false
% 55.48/7.53  --bmc1_dump_unsat_core_tptp             false
% 55.48/7.53  --bmc1_dump_file                        -
% 55.48/7.53  --bmc1_ucm_expand_uc_limit              128
% 55.48/7.53  --bmc1_ucm_n_expand_iterations          6
% 55.48/7.53  --bmc1_ucm_extend_mode                  1
% 55.48/7.53  --bmc1_ucm_init_mode                    2
% 55.48/7.53  --bmc1_ucm_cone_mode                    none
% 55.48/7.53  --bmc1_ucm_reduced_relation_type        0
% 55.48/7.53  --bmc1_ucm_relax_model                  4
% 55.48/7.53  --bmc1_ucm_full_tr_after_sat            true
% 55.48/7.53  --bmc1_ucm_expand_neg_assumptions       false
% 55.48/7.53  --bmc1_ucm_layered_model                none
% 55.48/7.53  --bmc1_ucm_max_lemma_size               10
% 55.48/7.53  
% 55.48/7.53  ------ AIG Options
% 55.48/7.53  
% 55.48/7.53  --aig_mode                              false
% 55.48/7.53  
% 55.48/7.53  ------ Instantiation Options
% 55.48/7.53  
% 55.48/7.53  --instantiation_flag                    true
% 55.48/7.53  --inst_sos_flag                         true
% 55.48/7.53  --inst_sos_phase                        true
% 55.48/7.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.48/7.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.48/7.53  --inst_lit_sel_side                     none
% 55.48/7.53  --inst_solver_per_active                1400
% 55.48/7.53  --inst_solver_calls_frac                1.
% 55.48/7.53  --inst_passive_queue_type               priority_queues
% 55.48/7.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.48/7.53  --inst_passive_queues_freq              [25;2]
% 55.48/7.53  --inst_dismatching                      true
% 55.48/7.53  --inst_eager_unprocessed_to_passive     true
% 55.48/7.53  --inst_prop_sim_given                   true
% 55.48/7.53  --inst_prop_sim_new                     false
% 55.48/7.53  --inst_subs_new                         false
% 55.48/7.53  --inst_eq_res_simp                      false
% 55.48/7.53  --inst_subs_given                       false
% 55.48/7.53  --inst_orphan_elimination               true
% 55.48/7.53  --inst_learning_loop_flag               true
% 55.48/7.53  --inst_learning_start                   3000
% 55.48/7.53  --inst_learning_factor                  2
% 55.48/7.53  --inst_start_prop_sim_after_learn       3
% 55.48/7.53  --inst_sel_renew                        solver
% 55.48/7.53  --inst_lit_activity_flag                true
% 55.48/7.53  --inst_restr_to_given                   false
% 55.48/7.53  --inst_activity_threshold               500
% 55.48/7.53  --inst_out_proof                        true
% 55.48/7.53  
% 55.48/7.53  ------ Resolution Options
% 55.48/7.53  
% 55.48/7.53  --resolution_flag                       false
% 55.48/7.53  --res_lit_sel                           adaptive
% 55.48/7.53  --res_lit_sel_side                      none
% 55.48/7.53  --res_ordering                          kbo
% 55.48/7.53  --res_to_prop_solver                    active
% 55.48/7.53  --res_prop_simpl_new                    false
% 55.48/7.53  --res_prop_simpl_given                  true
% 55.48/7.53  --res_passive_queue_type                priority_queues
% 55.48/7.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.48/7.53  --res_passive_queues_freq               [15;5]
% 55.48/7.53  --res_forward_subs                      full
% 55.48/7.53  --res_backward_subs                     full
% 55.48/7.53  --res_forward_subs_resolution           true
% 55.48/7.53  --res_backward_subs_resolution          true
% 55.48/7.53  --res_orphan_elimination                true
% 55.48/7.53  --res_time_limit                        2.
% 55.48/7.53  --res_out_proof                         true
% 55.48/7.53  
% 55.48/7.53  ------ Superposition Options
% 55.48/7.53  
% 55.48/7.53  --superposition_flag                    true
% 55.48/7.53  --sup_passive_queue_type                priority_queues
% 55.48/7.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.48/7.53  --sup_passive_queues_freq               [8;1;4]
% 55.48/7.53  --demod_completeness_check              fast
% 55.48/7.53  --demod_use_ground                      true
% 55.48/7.53  --sup_to_prop_solver                    passive
% 55.48/7.53  --sup_prop_simpl_new                    true
% 55.48/7.53  --sup_prop_simpl_given                  true
% 55.48/7.53  --sup_fun_splitting                     true
% 55.48/7.53  --sup_smt_interval                      50000
% 55.48/7.53  
% 55.48/7.53  ------ Superposition Simplification Setup
% 55.48/7.53  
% 55.48/7.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.48/7.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.48/7.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.48/7.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.48/7.53  --sup_full_triv                         [TrivRules;PropSubs]
% 55.48/7.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.48/7.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.48/7.53  --sup_immed_triv                        [TrivRules]
% 55.48/7.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.48/7.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.48/7.53  --sup_immed_bw_main                     []
% 55.48/7.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.48/7.53  --sup_input_triv                        [Unflattening;TrivRules]
% 55.48/7.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.48/7.53  --sup_input_bw                          []
% 55.48/7.53  
% 55.48/7.53  ------ Combination Options
% 55.48/7.53  
% 55.48/7.53  --comb_res_mult                         3
% 55.48/7.53  --comb_sup_mult                         2
% 55.48/7.53  --comb_inst_mult                        10
% 55.48/7.53  
% 55.48/7.53  ------ Debug Options
% 55.48/7.53  
% 55.48/7.53  --dbg_backtrace                         false
% 55.48/7.53  --dbg_dump_prop_clauses                 false
% 55.48/7.53  --dbg_dump_prop_clauses_file            -
% 55.48/7.53  --dbg_out_stat                          false
% 55.48/7.53  
% 55.48/7.53  
% 55.48/7.53  
% 55.48/7.53  
% 55.48/7.53  ------ Proving...
% 55.48/7.53  
% 55.48/7.53  
% 55.48/7.53  % SZS status Theorem for theBenchmark.p
% 55.48/7.53  
% 55.48/7.53  % SZS output start CNFRefutation for theBenchmark.p
% 55.48/7.53  
% 55.48/7.53  fof(f3,axiom,(
% 55.48/7.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f18,plain,(
% 55.48/7.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.48/7.53    inference(cnf_transformation,[],[f3])).
% 55.48/7.53  
% 55.48/7.53  fof(f9,conjecture,(
% 55.48/7.53    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f10,negated_conjecture,(
% 55.48/7.53    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 55.48/7.53    inference(negated_conjecture,[],[f9])).
% 55.48/7.53  
% 55.48/7.53  fof(f11,plain,(
% 55.48/7.53    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 55.48/7.53    inference(ennf_transformation,[],[f10])).
% 55.48/7.53  
% 55.48/7.53  fof(f13,plain,(
% 55.48/7.53    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 55.48/7.53    introduced(choice_axiom,[])).
% 55.48/7.53  
% 55.48/7.53  fof(f14,plain,(
% 55.48/7.53    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 55.48/7.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 55.48/7.53  
% 55.48/7.53  fof(f29,plain,(
% 55.48/7.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 55.48/7.53    inference(cnf_transformation,[],[f14])).
% 55.48/7.53  
% 55.48/7.53  fof(f2,axiom,(
% 55.48/7.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f12,plain,(
% 55.48/7.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 55.48/7.53    inference(nnf_transformation,[],[f2])).
% 55.48/7.53  
% 55.48/7.53  fof(f16,plain,(
% 55.48/7.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 55.48/7.53    inference(cnf_transformation,[],[f12])).
% 55.48/7.53  
% 55.48/7.53  fof(f8,axiom,(
% 55.48/7.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f23,plain,(
% 55.48/7.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 55.48/7.53    inference(cnf_transformation,[],[f8])).
% 55.48/7.53  
% 55.48/7.53  fof(f31,plain,(
% 55.48/7.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 55.48/7.53    inference(definition_unfolding,[],[f16,f23])).
% 55.48/7.53  
% 55.48/7.53  fof(f7,axiom,(
% 55.48/7.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f22,plain,(
% 55.48/7.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.48/7.53    inference(cnf_transformation,[],[f7])).
% 55.48/7.53  
% 55.48/7.53  fof(f33,plain,(
% 55.48/7.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.48/7.53    inference(definition_unfolding,[],[f22,f23])).
% 55.48/7.53  
% 55.48/7.53  fof(f1,axiom,(
% 55.48/7.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f15,plain,(
% 55.48/7.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 55.48/7.53    inference(cnf_transformation,[],[f1])).
% 55.48/7.53  
% 55.48/7.53  fof(f5,axiom,(
% 55.48/7.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f20,plain,(
% 55.48/7.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 55.48/7.53    inference(cnf_transformation,[],[f5])).
% 55.48/7.53  
% 55.48/7.53  fof(f6,axiom,(
% 55.48/7.53    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f21,plain,(
% 55.48/7.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 55.48/7.53    inference(cnf_transformation,[],[f6])).
% 55.48/7.53  
% 55.48/7.53  fof(f28,plain,(
% 55.48/7.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 55.48/7.53    inference(cnf_transformation,[],[f14])).
% 55.48/7.53  
% 55.48/7.53  fof(f4,axiom,(
% 55.48/7.53    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 55.48/7.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.48/7.53  
% 55.48/7.53  fof(f19,plain,(
% 55.48/7.53    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 55.48/7.53    inference(cnf_transformation,[],[f4])).
% 55.48/7.53  
% 55.48/7.53  fof(f32,plain,(
% 55.48/7.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 55.48/7.53    inference(definition_unfolding,[],[f19,f23])).
% 55.48/7.53  
% 55.48/7.53  fof(f17,plain,(
% 55.48/7.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 55.48/7.53    inference(cnf_transformation,[],[f12])).
% 55.48/7.53  
% 55.48/7.53  fof(f30,plain,(
% 55.48/7.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 55.48/7.53    inference(definition_unfolding,[],[f17,f23])).
% 55.48/7.53  
% 55.48/7.53  fof(f24,plain,(
% 55.48/7.53    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 55.48/7.53    inference(cnf_transformation,[],[f14])).
% 55.48/7.53  
% 55.48/7.53  cnf(c_3,plain,
% 55.48/7.53      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.48/7.53      inference(cnf_transformation,[],[f18]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_8,negated_conjecture,
% 55.48/7.53      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2) ),
% 55.48/7.53      inference(cnf_transformation,[],[f29]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_332,plain,
% 55.48/7.53      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
% 55.48/7.53      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 55.48/7.53      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_2,plain,
% 55.48/7.53      ( ~ r1_xboole_0(X0,X1)
% 55.48/7.53      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.48/7.53      inference(cnf_transformation,[],[f31]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_333,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 55.48/7.53      | r1_xboole_0(X0,X1) != iProver_top ),
% 55.48/7.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_947,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 55.48/7.53      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_332,c_333]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1193,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 55.48/7.53      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_947,c_333]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_7,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 55.48/7.53      inference(cnf_transformation,[],[f33]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1263,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 55.48/7.53      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_1193,c_7]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_0,plain,
% 55.48/7.53      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 55.48/7.53      inference(cnf_transformation,[],[f15]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_442,plain,
% 55.48/7.53      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_5,plain,
% 55.48/7.53      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.48/7.53      inference(cnf_transformation,[],[f20]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_515,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_442,c_5]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_517,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.48/7.53      inference(light_normalisation,[status(thm)],[c_515,c_442]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1266,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 55.48/7.53      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 55.48/7.53      inference(demodulation,[status(thm)],[c_1263,c_517]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_6,plain,
% 55.48/7.53      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.48/7.53      inference(cnf_transformation,[],[f21]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_575,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_580,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.48/7.53      inference(light_normalisation,[status(thm)],[c_575,c_6]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_8005,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0))
% 55.48/7.53      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_1266,c_580]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_8178,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
% 55.48/7.53      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 55.48/7.53      inference(light_normalisation,[status(thm)],[c_8005,c_442]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_9,negated_conjecture,
% 55.48/7.53      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1) ),
% 55.48/7.53      inference(cnf_transformation,[],[f28]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_331,plain,
% 55.48/7.53      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
% 55.48/7.53      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 55.48/7.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_948,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 55.48/7.53      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_331,c_333]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1195,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k1_xboole_0
% 55.48/7.53      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_948,c_333]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_8007,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 55.48/7.53      | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_1195,c_580]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_8175,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 55.48/7.53      | k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
% 55.48/7.53      inference(light_normalisation,[status(thm)],[c_8007,c_442]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_562,plain,
% 55.48/7.53      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_566,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 55.48/7.53      inference(demodulation,[status(thm)],[c_562,c_6]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_8176,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 55.48/7.53      | k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 55.48/7.53      inference(demodulation,[status(thm)],[c_8175,c_566]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_4,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.48/7.53      inference(cnf_transformation,[],[f32]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_519,plain,
% 55.48/7.53      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.48/7.53      inference(light_normalisation,[status(thm)],[c_4,c_4,c_517]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_564,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_6,c_519]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_565,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.48/7.53      inference(demodulation,[status(thm)],[c_564,c_5]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_716,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_565,c_6]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_8983,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_8176,c_716]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_9040,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_8983,c_580]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_9231,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
% 55.48/7.53      inference(light_normalisation,[status(thm)],[c_9040,c_442]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_9321,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
% 55.48/7.53      | k4_xboole_0(sK0,sK2) = sK0 ),
% 55.48/7.53      inference(demodulation,[status(thm)],[c_8178,c_9231]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_9334,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
% 55.48/7.53      | k4_xboole_0(sK0,sK2) = sK0 ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_3,c_9321]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_9403,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 55.48/7.53      inference(demodulation,[status(thm)],[c_9334,c_517]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1,plain,
% 55.48/7.53      ( r1_xboole_0(X0,X1)
% 55.48/7.53      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 55.48/7.53      inference(cnf_transformation,[],[f30]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_334,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 55.48/7.53      | r1_xboole_0(X0,X1) = iProver_top ),
% 55.48/7.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_49777,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) != k1_xboole_0
% 55.48/7.53      | r1_xboole_0(sK0,k2_xboole_0(sK1,X0)) = iProver_top ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_9231,c_334]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_175523,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,sK0) != k1_xboole_0
% 55.48/7.53      | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 55.48/7.53      inference(superposition,[status(thm)],[c_9403,c_49777]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_175738,plain,
% 55.48/7.53      ( k1_xboole_0 != k1_xboole_0
% 55.48/7.53      | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 55.48/7.53      inference(demodulation,[status(thm)],[c_175523,c_519]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_175739,plain,
% 55.48/7.53      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 55.48/7.53      inference(equality_resolution_simp,[status(thm)],[c_175738]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_169,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_22246,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k1_xboole_0) != X1
% 55.48/7.53      | k4_xboole_0(sK0,sK2) != X1
% 55.48/7.53      | k4_xboole_0(sK0,sK2) = k4_xboole_0(X0,k1_xboole_0) ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_169]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_22247,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
% 55.48/7.53      | k4_xboole_0(sK0,sK2) != sK0
% 55.48/7.53      | k4_xboole_0(sK0,k1_xboole_0) != sK0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_22246]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_172,plain,
% 55.48/7.53      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 55.48/7.53      theory(equality) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1697,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
% 55.48/7.53      | k4_xboole_0(sK0,sK2) != k4_xboole_0(X0,k1_xboole_0)
% 55.48/7.53      | sK0 != X0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_172]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1698,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
% 55.48/7.53      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k1_xboole_0)
% 55.48/7.53      | sK0 != sK0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_1697]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1206,plain,
% 55.48/7.53      ( r1_xboole_0(sK0,sK1)
% 55.48/7.53      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_1]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1208,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0
% 55.48/7.53      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 55.48/7.53      inference(predicate_to_equality,[status(thm)],[c_1206]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_354,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
% 55.48/7.53      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 55.48/7.53      | k1_xboole_0 != X0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_169]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_455,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
% 55.48/7.53      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 55.48/7.53      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_354]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1196,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
% 55.48/7.53      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 55.48/7.53      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_455]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_1197,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
% 55.48/7.53      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 55.48/7.53      | k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_1196]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_365,plain,
% 55.48/7.53      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_169]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_388,plain,
% 55.48/7.53      ( X0 != k1_xboole_0
% 55.48/7.53      | k1_xboole_0 = X0
% 55.48/7.53      | k1_xboole_0 != k1_xboole_0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_365]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_435,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 55.48/7.53      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
% 55.48/7.53      | k1_xboole_0 != k1_xboole_0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_388]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_594,plain,
% 55.48/7.53      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0
% 55.48/7.53      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
% 55.48/7.53      | k1_xboole_0 != k1_xboole_0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_435]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_595,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) != k1_xboole_0
% 55.48/7.53      | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
% 55.48/7.53      | k1_xboole_0 != k1_xboole_0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_594]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_518,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_517]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_168,plain,( X0 = X0 ),theory(equality) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_416,plain,
% 55.48/7.53      ( k1_xboole_0 = k1_xboole_0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_168]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_343,plain,
% 55.48/7.53      ( r1_xboole_0(sK0,sK2)
% 55.48/7.53      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_1]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_344,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
% 55.48/7.53      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 55.48/7.53      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_176,plain,
% 55.48/7.53      ( sK0 = sK0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_168]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_23,plain,
% 55.48/7.53      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 55.48/7.53      inference(instantiation,[status(thm)],[c_4]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_13,negated_conjecture,
% 55.48/7.53      ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 55.48/7.53      | ~ r1_xboole_0(sK0,sK2)
% 55.48/7.53      | ~ r1_xboole_0(sK0,sK1) ),
% 55.48/7.53      inference(cnf_transformation,[],[f24]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(c_14,plain,
% 55.48/7.53      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != iProver_top
% 55.48/7.53      | r1_xboole_0(sK0,sK2) != iProver_top
% 55.48/7.53      | r1_xboole_0(sK0,sK1) != iProver_top ),
% 55.48/7.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.48/7.53  
% 55.48/7.53  cnf(contradiction,plain,
% 55.48/7.53      ( $false ),
% 55.48/7.53      inference(minisat,
% 55.48/7.53                [status(thm)],
% 55.48/7.53                [c_175739,c_22247,c_9403,c_8983,c_1698,c_1208,c_1197,
% 55.48/7.53                 c_595,c_518,c_416,c_344,c_176,c_23,c_14]) ).
% 55.48/7.53  
% 55.48/7.53  
% 55.48/7.53  % SZS output end CNFRefutation for theBenchmark.p
% 55.48/7.53  
% 55.48/7.53  ------                               Statistics
% 55.48/7.53  
% 55.48/7.53  ------ General
% 55.48/7.53  
% 55.48/7.53  abstr_ref_over_cycles:                  0
% 55.48/7.53  abstr_ref_under_cycles:                 0
% 55.48/7.53  gc_basic_clause_elim:                   0
% 55.48/7.53  forced_gc_time:                         0
% 55.48/7.53  parsing_time:                           0.009
% 55.48/7.53  unif_index_cands_time:                  0.
% 55.48/7.53  unif_index_add_time:                    0.
% 55.48/7.53  orderings_time:                         0.
% 55.48/7.53  out_proof_time:                         0.01
% 55.48/7.53  total_time:                             6.71
% 55.48/7.53  num_of_symbols:                         38
% 55.48/7.53  num_of_terms:                           360278
% 55.48/7.53  
% 55.48/7.53  ------ Preprocessing
% 55.48/7.53  
% 55.48/7.53  num_of_splits:                          0
% 55.48/7.53  num_of_split_atoms:                     0
% 55.48/7.53  num_of_reused_defs:                     0
% 55.48/7.53  num_eq_ax_congr_red:                    0
% 55.48/7.53  num_of_sem_filtered_clauses:            1
% 55.48/7.53  num_of_subtypes:                        0
% 55.48/7.53  monotx_restored_types:                  0
% 55.48/7.53  sat_num_of_epr_types:                   0
% 55.48/7.53  sat_num_of_non_cyclic_types:            0
% 55.48/7.53  sat_guarded_non_collapsed_types:        0
% 55.48/7.53  num_pure_diseq_elim:                    0
% 55.48/7.53  simp_replaced_by:                       0
% 55.48/7.53  res_preprocessed:                       55
% 55.48/7.53  prep_upred:                             0
% 55.48/7.53  prep_unflattend:                        0
% 55.48/7.53  smt_new_axioms:                         0
% 55.48/7.53  pred_elim_cands:                        1
% 55.48/7.53  pred_elim:                              0
% 55.48/7.53  pred_elim_cl:                           0
% 55.48/7.53  pred_elim_cycles:                       2
% 55.48/7.53  merged_defs:                            8
% 55.48/7.53  merged_defs_ncl:                        0
% 55.48/7.53  bin_hyper_res:                          8
% 55.48/7.53  prep_cycles:                            4
% 55.48/7.53  pred_elim_time:                         0.
% 55.48/7.53  splitting_time:                         0.
% 55.48/7.53  sem_filter_time:                        0.
% 55.48/7.53  monotx_time:                            0.001
% 55.48/7.53  subtype_inf_time:                       0.
% 55.48/7.53  
% 55.48/7.53  ------ Problem properties
% 55.48/7.53  
% 55.48/7.53  clauses:                                11
% 55.48/7.53  conjectures:                            3
% 55.48/7.53  epr:                                    0
% 55.48/7.53  horn:                                   9
% 55.48/7.53  ground:                                 3
% 55.48/7.53  unary:                                  6
% 55.48/7.53  binary:                                 4
% 55.48/7.53  lits:                                   17
% 55.48/7.53  lits_eq:                                8
% 55.48/7.53  fd_pure:                                0
% 55.48/7.53  fd_pseudo:                              0
% 55.48/7.53  fd_cond:                                0
% 55.48/7.53  fd_pseudo_cond:                         0
% 55.48/7.53  ac_symbols:                             0
% 55.48/7.53  
% 55.48/7.53  ------ Propositional Solver
% 55.48/7.53  
% 55.48/7.53  prop_solver_calls:                      39
% 55.48/7.53  prop_fast_solver_calls:                 1297
% 55.48/7.53  smt_solver_calls:                       0
% 55.48/7.53  smt_fast_solver_calls:                  0
% 55.48/7.53  prop_num_of_clauses:                    38765
% 55.48/7.53  prop_preprocess_simplified:             22390
% 55.48/7.53  prop_fo_subsumed:                       164
% 55.48/7.53  prop_solver_time:                       0.
% 55.48/7.53  smt_solver_time:                        0.
% 55.48/7.53  smt_fast_solver_time:                   0.
% 55.48/7.53  prop_fast_solver_time:                  0.
% 55.48/7.53  prop_unsat_core_time:                   0.003
% 55.48/7.53  
% 55.48/7.53  ------ QBF
% 55.48/7.53  
% 55.48/7.53  qbf_q_res:                              0
% 55.48/7.53  qbf_num_tautologies:                    0
% 55.48/7.53  qbf_prep_cycles:                        0
% 55.48/7.53  
% 55.48/7.53  ------ BMC1
% 55.48/7.53  
% 55.48/7.53  bmc1_current_bound:                     -1
% 55.48/7.53  bmc1_last_solved_bound:                 -1
% 55.48/7.53  bmc1_unsat_core_size:                   -1
% 55.48/7.53  bmc1_unsat_core_parents_size:           -1
% 55.48/7.53  bmc1_merge_next_fun:                    0
% 55.48/7.53  bmc1_unsat_core_clauses_time:           0.
% 55.48/7.53  
% 55.48/7.53  ------ Instantiation
% 55.48/7.53  
% 55.48/7.53  inst_num_of_clauses:                    5129
% 55.48/7.53  inst_num_in_passive:                    1714
% 55.48/7.53  inst_num_in_active:                     1155
% 55.48/7.53  inst_num_in_unprocessed:                2260
% 55.48/7.53  inst_num_of_loops:                      1930
% 55.48/7.53  inst_num_of_learning_restarts:          0
% 55.48/7.53  inst_num_moves_active_passive:          767
% 55.48/7.53  inst_lit_activity:                      0
% 55.48/7.53  inst_lit_activity_moves:                1
% 55.48/7.53  inst_num_tautologies:                   0
% 55.48/7.53  inst_num_prop_implied:                  0
% 55.48/7.53  inst_num_existing_simplified:           0
% 55.48/7.53  inst_num_eq_res_simplified:             0
% 55.48/7.53  inst_num_child_elim:                    0
% 55.48/7.53  inst_num_of_dismatching_blockings:      4592
% 55.48/7.53  inst_num_of_non_proper_insts:           4837
% 55.48/7.53  inst_num_of_duplicates:                 0
% 55.48/7.53  inst_inst_num_from_inst_to_res:         0
% 55.48/7.53  inst_dismatching_checking_time:         0.
% 55.48/7.53  
% 55.48/7.53  ------ Resolution
% 55.48/7.53  
% 55.48/7.53  res_num_of_clauses:                     0
% 55.48/7.53  res_num_in_passive:                     0
% 55.48/7.53  res_num_in_active:                      0
% 55.48/7.53  res_num_of_loops:                       59
% 55.48/7.53  res_forward_subset_subsumed:            990
% 55.48/7.53  res_backward_subset_subsumed:           0
% 55.48/7.53  res_forward_subsumed:                   0
% 55.48/7.53  res_backward_subsumed:                  0
% 55.48/7.53  res_forward_subsumption_resolution:     0
% 55.48/7.53  res_backward_subsumption_resolution:    0
% 55.48/7.53  res_clause_to_clause_subsumption:       611958
% 55.48/7.53  res_orphan_elimination:                 0
% 55.48/7.53  res_tautology_del:                      289
% 55.48/7.53  res_num_eq_res_simplified:              0
% 55.48/7.53  res_num_sel_changes:                    0
% 55.48/7.53  res_moves_from_active_to_pass:          0
% 55.48/7.53  
% 55.48/7.53  ------ Superposition
% 55.48/7.53  
% 55.48/7.53  sup_time_total:                         0.
% 55.48/7.53  sup_time_generating:                    0.
% 55.48/7.53  sup_time_sim_full:                      0.
% 55.48/7.53  sup_time_sim_immed:                     0.
% 55.48/7.53  
% 55.48/7.53  sup_num_of_clauses:                     17180
% 55.48/7.53  sup_num_in_active:                      307
% 55.48/7.53  sup_num_in_passive:                     16873
% 55.48/7.53  sup_num_of_loops:                       384
% 55.48/7.53  sup_fw_superposition:                   44244
% 55.48/7.53  sup_bw_superposition:                   40097
% 55.48/7.53  sup_immediate_simplified:               52461
% 55.48/7.53  sup_given_eliminated:                   10
% 55.48/7.53  comparisons_done:                       0
% 55.48/7.53  comparisons_avoided:                    75
% 55.48/7.53  
% 55.48/7.53  ------ Simplifications
% 55.48/7.53  
% 55.48/7.53  
% 55.48/7.53  sim_fw_subset_subsumed:                 265
% 55.48/7.53  sim_bw_subset_subsumed:                 69
% 55.48/7.53  sim_fw_subsumed:                        9958
% 55.48/7.53  sim_bw_subsumed:                        303
% 55.48/7.53  sim_fw_subsumption_res:                 0
% 55.48/7.53  sim_bw_subsumption_res:                 0
% 55.48/7.53  sim_tautology_del:                      6
% 55.48/7.53  sim_eq_tautology_del:                   17697
% 55.48/7.53  sim_eq_res_simp:                        72
% 55.48/7.53  sim_fw_demodulated:                     39203
% 55.48/7.53  sim_bw_demodulated:                     283
% 55.48/7.53  sim_light_normalised:                   14805
% 55.48/7.53  sim_joinable_taut:                      0
% 55.48/7.53  sim_joinable_simp:                      0
% 55.48/7.53  sim_ac_normalised:                      0
% 55.48/7.53  sim_smt_subsumption:                    0
% 55.48/7.53  
%------------------------------------------------------------------------------
