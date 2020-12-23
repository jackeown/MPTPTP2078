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

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  113 (1803 expanded)
%              Number of clauses        :   74 ( 692 expanded)
%              Number of leaves         :   14 ( 457 expanded)
%              Depth                    :   22
%              Number of atoms          :  148 (2849 expanded)
%              Number of equality atoms :  115 (2104 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,
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

fof(f20,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).

fof(f34,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_566,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_101,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0])).

cnf(c_473,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_101])).

cnf(c_1107,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_473,c_0])).

cnf(c_15,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_100,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_10,c_0])).

cnf(c_609,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_100,c_10])).

cnf(c_683,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_609,c_10])).

cnf(c_1544,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1107,c_683])).

cnf(c_1549,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1544,c_100])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2116,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_1549,c_8])).

cnf(c_9600,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,k2_xboole_0(X0,sK0)))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_566,c_2116])).

cnf(c_9616,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) ),
    inference(demodulation,[status(thm)],[c_9600,c_566])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_267,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_269,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_949,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_267,c_269])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_270,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1523,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_949,c_270])).

cnf(c_8449,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_1523,c_6])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8450,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_8449,c_4,c_473])).

cnf(c_542,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_8915,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k2_xboole_0(sK2,sK0),sK0) ),
    inference(superposition,[status(thm)],[c_8450,c_542])).

cnf(c_8916,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK0),sK0) = k4_xboole_0(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_8915,c_8450])).

cnf(c_1521,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_267,c_270])).

cnf(c_2197,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1521,c_6])).

cnf(c_2198,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_2197,c_4,c_473])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_268,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1520,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_268,c_270])).

cnf(c_2132,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1520,c_6])).

cnf(c_2134,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_2132,c_4,c_473])).

cnf(c_2401,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2134,c_9])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_272,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_567,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_272])).

cnf(c_568,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_567,c_6])).

cnf(c_1122,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_100,c_568])).

cnf(c_6251,plain,
    ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2401,c_1122])).

cnf(c_6830,plain,
    ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6251,c_6])).

cnf(c_6837,plain,
    ( k2_xboole_0(sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_6830,c_4])).

cnf(c_7707,plain,
    ( k2_xboole_0(sK3,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_6837,c_0])).

cnf(c_7800,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK0)) = k2_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_7707,c_683])).

cnf(c_472,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_272,c_6])).

cnf(c_474,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_472,c_4])).

cnf(c_7801,plain,
    ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_7800,c_474])).

cnf(c_8917,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8916,c_2198,c_7801])).

cnf(c_7702,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_6837,c_10])).

cnf(c_8942,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK3,X0)) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1107,c_7702])).

cnf(c_8992,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK3,X0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_8942,c_6837])).

cnf(c_9617,plain,
    ( k4_xboole_0(sK1,sK0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_9616,c_2116,c_8917,c_8992])).

cnf(c_948,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_268,c_269])).

cnf(c_1522,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_948,c_270])).

cnf(c_8332,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(superposition,[status(thm)],[c_1522,c_6])).

cnf(c_8333,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_8332,c_4,c_473])).

cnf(c_2118,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1549,c_568])).

cnf(c_9523,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_100,c_566])).

cnf(c_10375,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2118,c_9523])).

cnf(c_10431,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_10375,c_7707,c_8450,c_8992])).

cnf(c_10432,plain,
    ( sK0 = sK3 ),
    inference(demodulation,[status(thm)],[c_10431,c_4])).

cnf(c_10710,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_9617,c_8333,c_9617,c_10432])).

cnf(c_12,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10747,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_10710,c_12])).

cnf(c_10748,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10747])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 4.14/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.02  
% 4.14/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.14/1.02  
% 4.14/1.02  ------  iProver source info
% 4.14/1.02  
% 4.14/1.02  git: date: 2020-06-30 10:37:57 +0100
% 4.14/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.14/1.02  git: non_committed_changes: false
% 4.14/1.02  git: last_make_outside_of_git: false
% 4.14/1.02  
% 4.14/1.02  ------ 
% 4.14/1.02  
% 4.14/1.02  ------ Input Options
% 4.14/1.02  
% 4.14/1.02  --out_options                           all
% 4.14/1.02  --tptp_safe_out                         true
% 4.14/1.02  --problem_path                          ""
% 4.14/1.02  --include_path                          ""
% 4.14/1.02  --clausifier                            res/vclausify_rel
% 4.14/1.02  --clausifier_options                    ""
% 4.14/1.02  --stdin                                 false
% 4.14/1.02  --stats_out                             all
% 4.14/1.02  
% 4.14/1.02  ------ General Options
% 4.14/1.02  
% 4.14/1.02  --fof                                   false
% 4.14/1.02  --time_out_real                         305.
% 4.14/1.02  --time_out_virtual                      -1.
% 4.14/1.02  --symbol_type_check                     false
% 4.14/1.02  --clausify_out                          false
% 4.14/1.02  --sig_cnt_out                           false
% 4.14/1.02  --trig_cnt_out                          false
% 4.14/1.02  --trig_cnt_out_tolerance                1.
% 4.14/1.02  --trig_cnt_out_sk_spl                   false
% 4.14/1.02  --abstr_cl_out                          false
% 4.14/1.02  
% 4.14/1.02  ------ Global Options
% 4.14/1.02  
% 4.14/1.02  --schedule                              default
% 4.14/1.02  --add_important_lit                     false
% 4.14/1.02  --prop_solver_per_cl                    1000
% 4.14/1.02  --min_unsat_core                        false
% 4.14/1.02  --soft_assumptions                      false
% 4.14/1.02  --soft_lemma_size                       3
% 4.14/1.02  --prop_impl_unit_size                   0
% 4.14/1.02  --prop_impl_unit                        []
% 4.14/1.02  --share_sel_clauses                     true
% 4.14/1.02  --reset_solvers                         false
% 4.14/1.02  --bc_imp_inh                            [conj_cone]
% 4.14/1.02  --conj_cone_tolerance                   3.
% 4.14/1.02  --extra_neg_conj                        none
% 4.14/1.02  --large_theory_mode                     true
% 4.14/1.02  --prolific_symb_bound                   200
% 4.14/1.02  --lt_threshold                          2000
% 4.14/1.02  --clause_weak_htbl                      true
% 4.14/1.02  --gc_record_bc_elim                     false
% 4.14/1.02  
% 4.14/1.02  ------ Preprocessing Options
% 4.14/1.02  
% 4.14/1.02  --preprocessing_flag                    true
% 4.14/1.02  --time_out_prep_mult                    0.1
% 4.14/1.02  --splitting_mode                        input
% 4.14/1.02  --splitting_grd                         true
% 4.14/1.02  --splitting_cvd                         false
% 4.14/1.02  --splitting_cvd_svl                     false
% 4.14/1.02  --splitting_nvd                         32
% 4.14/1.02  --sub_typing                            true
% 4.14/1.02  --prep_gs_sim                           true
% 4.14/1.02  --prep_unflatten                        true
% 4.14/1.02  --prep_res_sim                          true
% 4.14/1.02  --prep_upred                            true
% 4.14/1.02  --prep_sem_filter                       exhaustive
% 4.14/1.02  --prep_sem_filter_out                   false
% 4.14/1.02  --pred_elim                             true
% 4.14/1.02  --res_sim_input                         true
% 4.14/1.02  --eq_ax_congr_red                       true
% 4.14/1.02  --pure_diseq_elim                       true
% 4.14/1.02  --brand_transform                       false
% 4.14/1.02  --non_eq_to_eq                          false
% 4.14/1.02  --prep_def_merge                        true
% 4.14/1.02  --prep_def_merge_prop_impl              false
% 4.14/1.02  --prep_def_merge_mbd                    true
% 4.14/1.02  --prep_def_merge_tr_red                 false
% 4.14/1.02  --prep_def_merge_tr_cl                  false
% 4.14/1.02  --smt_preprocessing                     true
% 4.14/1.02  --smt_ac_axioms                         fast
% 4.14/1.02  --preprocessed_out                      false
% 4.14/1.02  --preprocessed_stats                    false
% 4.14/1.02  
% 4.14/1.02  ------ Abstraction refinement Options
% 4.14/1.02  
% 4.14/1.02  --abstr_ref                             []
% 4.14/1.02  --abstr_ref_prep                        false
% 4.14/1.02  --abstr_ref_until_sat                   false
% 4.14/1.02  --abstr_ref_sig_restrict                funpre
% 4.14/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.14/1.02  --abstr_ref_under                       []
% 4.14/1.02  
% 4.14/1.02  ------ SAT Options
% 4.14/1.02  
% 4.14/1.02  --sat_mode                              false
% 4.14/1.02  --sat_fm_restart_options                ""
% 4.14/1.02  --sat_gr_def                            false
% 4.14/1.02  --sat_epr_types                         true
% 4.14/1.02  --sat_non_cyclic_types                  false
% 4.14/1.02  --sat_finite_models                     false
% 4.14/1.02  --sat_fm_lemmas                         false
% 4.14/1.02  --sat_fm_prep                           false
% 4.14/1.02  --sat_fm_uc_incr                        true
% 4.14/1.02  --sat_out_model                         small
% 4.14/1.02  --sat_out_clauses                       false
% 4.14/1.02  
% 4.14/1.02  ------ QBF Options
% 4.14/1.02  
% 4.14/1.02  --qbf_mode                              false
% 4.14/1.02  --qbf_elim_univ                         false
% 4.14/1.02  --qbf_dom_inst                          none
% 4.14/1.02  --qbf_dom_pre_inst                      false
% 4.14/1.02  --qbf_sk_in                             false
% 4.14/1.02  --qbf_pred_elim                         true
% 4.14/1.02  --qbf_split                             512
% 4.14/1.02  
% 4.14/1.02  ------ BMC1 Options
% 4.14/1.02  
% 4.14/1.02  --bmc1_incremental                      false
% 4.14/1.02  --bmc1_axioms                           reachable_all
% 4.14/1.02  --bmc1_min_bound                        0
% 4.14/1.02  --bmc1_max_bound                        -1
% 4.14/1.02  --bmc1_max_bound_default                -1
% 4.14/1.02  --bmc1_symbol_reachability              true
% 4.14/1.02  --bmc1_property_lemmas                  false
% 4.14/1.02  --bmc1_k_induction                      false
% 4.14/1.02  --bmc1_non_equiv_states                 false
% 4.14/1.02  --bmc1_deadlock                         false
% 4.14/1.02  --bmc1_ucm                              false
% 4.14/1.02  --bmc1_add_unsat_core                   none
% 4.14/1.02  --bmc1_unsat_core_children              false
% 4.14/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.14/1.02  --bmc1_out_stat                         full
% 4.14/1.02  --bmc1_ground_init                      false
% 4.14/1.02  --bmc1_pre_inst_next_state              false
% 4.14/1.02  --bmc1_pre_inst_state                   false
% 4.14/1.02  --bmc1_pre_inst_reach_state             false
% 4.14/1.02  --bmc1_out_unsat_core                   false
% 4.14/1.02  --bmc1_aig_witness_out                  false
% 4.14/1.02  --bmc1_verbose                          false
% 4.14/1.02  --bmc1_dump_clauses_tptp                false
% 4.14/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.14/1.02  --bmc1_dump_file                        -
% 4.14/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.14/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.14/1.02  --bmc1_ucm_extend_mode                  1
% 4.14/1.02  --bmc1_ucm_init_mode                    2
% 4.14/1.02  --bmc1_ucm_cone_mode                    none
% 4.14/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.14/1.02  --bmc1_ucm_relax_model                  4
% 4.14/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.14/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.14/1.02  --bmc1_ucm_layered_model                none
% 4.14/1.02  --bmc1_ucm_max_lemma_size               10
% 4.14/1.02  
% 4.14/1.02  ------ AIG Options
% 4.14/1.02  
% 4.14/1.02  --aig_mode                              false
% 4.14/1.02  
% 4.14/1.02  ------ Instantiation Options
% 4.14/1.02  
% 4.14/1.02  --instantiation_flag                    true
% 4.14/1.02  --inst_sos_flag                         true
% 4.14/1.02  --inst_sos_phase                        true
% 4.14/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.14/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.14/1.02  --inst_lit_sel_side                     num_symb
% 4.14/1.02  --inst_solver_per_active                1400
% 4.14/1.02  --inst_solver_calls_frac                1.
% 4.14/1.02  --inst_passive_queue_type               priority_queues
% 4.14/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.14/1.02  --inst_passive_queues_freq              [25;2]
% 4.14/1.02  --inst_dismatching                      true
% 4.14/1.02  --inst_eager_unprocessed_to_passive     true
% 4.14/1.02  --inst_prop_sim_given                   true
% 4.14/1.02  --inst_prop_sim_new                     false
% 4.14/1.02  --inst_subs_new                         false
% 4.14/1.02  --inst_eq_res_simp                      false
% 4.14/1.02  --inst_subs_given                       false
% 4.14/1.02  --inst_orphan_elimination               true
% 4.14/1.02  --inst_learning_loop_flag               true
% 4.14/1.02  --inst_learning_start                   3000
% 4.14/1.02  --inst_learning_factor                  2
% 4.14/1.02  --inst_start_prop_sim_after_learn       3
% 4.14/1.02  --inst_sel_renew                        solver
% 4.14/1.02  --inst_lit_activity_flag                true
% 4.14/1.02  --inst_restr_to_given                   false
% 4.14/1.02  --inst_activity_threshold               500
% 4.14/1.02  --inst_out_proof                        true
% 4.14/1.02  
% 4.14/1.02  ------ Resolution Options
% 4.14/1.02  
% 4.14/1.02  --resolution_flag                       true
% 4.14/1.02  --res_lit_sel                           adaptive
% 4.14/1.02  --res_lit_sel_side                      none
% 4.14/1.02  --res_ordering                          kbo
% 4.14/1.02  --res_to_prop_solver                    active
% 4.14/1.02  --res_prop_simpl_new                    false
% 4.14/1.02  --res_prop_simpl_given                  true
% 4.14/1.02  --res_passive_queue_type                priority_queues
% 4.14/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.14/1.02  --res_passive_queues_freq               [15;5]
% 4.14/1.02  --res_forward_subs                      full
% 4.14/1.02  --res_backward_subs                     full
% 4.14/1.02  --res_forward_subs_resolution           true
% 4.14/1.02  --res_backward_subs_resolution          true
% 4.14/1.02  --res_orphan_elimination                true
% 4.14/1.02  --res_time_limit                        2.
% 4.14/1.02  --res_out_proof                         true
% 4.14/1.02  
% 4.14/1.02  ------ Superposition Options
% 4.14/1.02  
% 4.14/1.02  --superposition_flag                    true
% 4.14/1.02  --sup_passive_queue_type                priority_queues
% 4.14/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.14/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.14/1.02  --demod_completeness_check              fast
% 4.14/1.02  --demod_use_ground                      true
% 4.14/1.02  --sup_to_prop_solver                    passive
% 4.14/1.02  --sup_prop_simpl_new                    true
% 4.14/1.02  --sup_prop_simpl_given                  true
% 4.14/1.02  --sup_fun_splitting                     true
% 4.14/1.02  --sup_smt_interval                      50000
% 4.14/1.02  
% 4.14/1.02  ------ Superposition Simplification Setup
% 4.14/1.02  
% 4.14/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.14/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.14/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.14/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.14/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.14/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.14/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.14/1.02  --sup_immed_triv                        [TrivRules]
% 4.14/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/1.02  --sup_immed_bw_main                     []
% 4.14/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.14/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.14/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/1.02  --sup_input_bw                          []
% 4.14/1.02  
% 4.14/1.02  ------ Combination Options
% 4.14/1.02  
% 4.14/1.02  --comb_res_mult                         3
% 4.14/1.02  --comb_sup_mult                         2
% 4.14/1.02  --comb_inst_mult                        10
% 4.14/1.02  
% 4.14/1.02  ------ Debug Options
% 4.14/1.02  
% 4.14/1.02  --dbg_backtrace                         false
% 4.14/1.02  --dbg_dump_prop_clauses                 false
% 4.14/1.02  --dbg_dump_prop_clauses_file            -
% 4.14/1.02  --dbg_out_stat                          false
% 4.14/1.02  ------ Parsing...
% 4.14/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.14/1.02  
% 4.14/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.14/1.02  
% 4.14/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.14/1.02  
% 4.14/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.14/1.02  ------ Proving...
% 4.14/1.02  ------ Problem Properties 
% 4.14/1.02  
% 4.14/1.02  
% 4.14/1.02  clauses                                 16
% 4.14/1.02  conjectures                             4
% 4.14/1.02  EPR                                     4
% 4.14/1.02  Horn                                    16
% 4.14/1.02  unary                                   13
% 4.14/1.02  binary                                  3
% 4.14/1.02  lits                                    19
% 4.14/1.02  lits eq                                 13
% 4.14/1.02  fd_pure                                 0
% 4.14/1.02  fd_pseudo                               0
% 4.14/1.02  fd_cond                                 0
% 4.14/1.02  fd_pseudo_cond                          0
% 4.14/1.02  AC symbols                              1
% 4.14/1.02  
% 4.14/1.02  ------ Schedule dynamic 5 is on 
% 4.14/1.02  
% 4.14/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.14/1.02  
% 4.14/1.02  
% 4.14/1.02  ------ 
% 4.14/1.02  Current options:
% 4.14/1.02  ------ 
% 4.14/1.02  
% 4.14/1.02  ------ Input Options
% 4.14/1.02  
% 4.14/1.02  --out_options                           all
% 4.14/1.02  --tptp_safe_out                         true
% 4.14/1.02  --problem_path                          ""
% 4.14/1.02  --include_path                          ""
% 4.14/1.02  --clausifier                            res/vclausify_rel
% 4.14/1.02  --clausifier_options                    ""
% 4.14/1.02  --stdin                                 false
% 4.14/1.02  --stats_out                             all
% 4.14/1.02  
% 4.14/1.02  ------ General Options
% 4.14/1.02  
% 4.14/1.02  --fof                                   false
% 4.14/1.02  --time_out_real                         305.
% 4.14/1.02  --time_out_virtual                      -1.
% 4.14/1.02  --symbol_type_check                     false
% 4.14/1.02  --clausify_out                          false
% 4.14/1.02  --sig_cnt_out                           false
% 4.14/1.02  --trig_cnt_out                          false
% 4.14/1.02  --trig_cnt_out_tolerance                1.
% 4.14/1.02  --trig_cnt_out_sk_spl                   false
% 4.14/1.02  --abstr_cl_out                          false
% 4.14/1.02  
% 4.14/1.02  ------ Global Options
% 4.14/1.02  
% 4.14/1.02  --schedule                              default
% 4.14/1.02  --add_important_lit                     false
% 4.14/1.02  --prop_solver_per_cl                    1000
% 4.14/1.02  --min_unsat_core                        false
% 4.14/1.02  --soft_assumptions                      false
% 4.14/1.02  --soft_lemma_size                       3
% 4.14/1.02  --prop_impl_unit_size                   0
% 4.14/1.02  --prop_impl_unit                        []
% 4.14/1.02  --share_sel_clauses                     true
% 4.14/1.02  --reset_solvers                         false
% 4.14/1.02  --bc_imp_inh                            [conj_cone]
% 4.14/1.02  --conj_cone_tolerance                   3.
% 4.14/1.02  --extra_neg_conj                        none
% 4.14/1.02  --large_theory_mode                     true
% 4.14/1.02  --prolific_symb_bound                   200
% 4.14/1.02  --lt_threshold                          2000
% 4.14/1.02  --clause_weak_htbl                      true
% 4.14/1.02  --gc_record_bc_elim                     false
% 4.14/1.02  
% 4.14/1.02  ------ Preprocessing Options
% 4.14/1.02  
% 4.14/1.02  --preprocessing_flag                    true
% 4.14/1.02  --time_out_prep_mult                    0.1
% 4.14/1.02  --splitting_mode                        input
% 4.14/1.02  --splitting_grd                         true
% 4.14/1.02  --splitting_cvd                         false
% 4.14/1.02  --splitting_cvd_svl                     false
% 4.14/1.02  --splitting_nvd                         32
% 4.14/1.02  --sub_typing                            true
% 4.14/1.02  --prep_gs_sim                           true
% 4.14/1.02  --prep_unflatten                        true
% 4.14/1.02  --prep_res_sim                          true
% 4.14/1.02  --prep_upred                            true
% 4.14/1.02  --prep_sem_filter                       exhaustive
% 4.14/1.02  --prep_sem_filter_out                   false
% 4.14/1.02  --pred_elim                             true
% 4.14/1.02  --res_sim_input                         true
% 4.14/1.02  --eq_ax_congr_red                       true
% 4.14/1.02  --pure_diseq_elim                       true
% 4.14/1.02  --brand_transform                       false
% 4.14/1.02  --non_eq_to_eq                          false
% 4.14/1.02  --prep_def_merge                        true
% 4.14/1.02  --prep_def_merge_prop_impl              false
% 4.14/1.02  --prep_def_merge_mbd                    true
% 4.14/1.02  --prep_def_merge_tr_red                 false
% 4.14/1.02  --prep_def_merge_tr_cl                  false
% 4.14/1.02  --smt_preprocessing                     true
% 4.14/1.02  --smt_ac_axioms                         fast
% 4.14/1.02  --preprocessed_out                      false
% 4.14/1.02  --preprocessed_stats                    false
% 4.14/1.02  
% 4.14/1.02  ------ Abstraction refinement Options
% 4.14/1.02  
% 4.14/1.02  --abstr_ref                             []
% 4.14/1.02  --abstr_ref_prep                        false
% 4.14/1.02  --abstr_ref_until_sat                   false
% 4.14/1.02  --abstr_ref_sig_restrict                funpre
% 4.14/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.14/1.02  --abstr_ref_under                       []
% 4.14/1.02  
% 4.14/1.02  ------ SAT Options
% 4.14/1.02  
% 4.14/1.02  --sat_mode                              false
% 4.14/1.02  --sat_fm_restart_options                ""
% 4.14/1.02  --sat_gr_def                            false
% 4.14/1.02  --sat_epr_types                         true
% 4.14/1.02  --sat_non_cyclic_types                  false
% 4.14/1.02  --sat_finite_models                     false
% 4.14/1.02  --sat_fm_lemmas                         false
% 4.14/1.02  --sat_fm_prep                           false
% 4.14/1.02  --sat_fm_uc_incr                        true
% 4.14/1.02  --sat_out_model                         small
% 4.14/1.02  --sat_out_clauses                       false
% 4.14/1.02  
% 4.14/1.02  ------ QBF Options
% 4.14/1.02  
% 4.14/1.02  --qbf_mode                              false
% 4.14/1.02  --qbf_elim_univ                         false
% 4.14/1.02  --qbf_dom_inst                          none
% 4.14/1.02  --qbf_dom_pre_inst                      false
% 4.14/1.02  --qbf_sk_in                             false
% 4.14/1.02  --qbf_pred_elim                         true
% 4.14/1.02  --qbf_split                             512
% 4.14/1.02  
% 4.14/1.02  ------ BMC1 Options
% 4.14/1.02  
% 4.14/1.02  --bmc1_incremental                      false
% 4.14/1.02  --bmc1_axioms                           reachable_all
% 4.14/1.02  --bmc1_min_bound                        0
% 4.14/1.02  --bmc1_max_bound                        -1
% 4.14/1.02  --bmc1_max_bound_default                -1
% 4.14/1.02  --bmc1_symbol_reachability              true
% 4.14/1.02  --bmc1_property_lemmas                  false
% 4.14/1.02  --bmc1_k_induction                      false
% 4.14/1.02  --bmc1_non_equiv_states                 false
% 4.14/1.02  --bmc1_deadlock                         false
% 4.14/1.02  --bmc1_ucm                              false
% 4.14/1.02  --bmc1_add_unsat_core                   none
% 4.14/1.02  --bmc1_unsat_core_children              false
% 4.14/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.14/1.02  --bmc1_out_stat                         full
% 4.14/1.02  --bmc1_ground_init                      false
% 4.14/1.02  --bmc1_pre_inst_next_state              false
% 4.14/1.02  --bmc1_pre_inst_state                   false
% 4.14/1.02  --bmc1_pre_inst_reach_state             false
% 4.14/1.02  --bmc1_out_unsat_core                   false
% 4.14/1.02  --bmc1_aig_witness_out                  false
% 4.14/1.02  --bmc1_verbose                          false
% 4.14/1.02  --bmc1_dump_clauses_tptp                false
% 4.14/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.14/1.02  --bmc1_dump_file                        -
% 4.14/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.14/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.14/1.02  --bmc1_ucm_extend_mode                  1
% 4.14/1.02  --bmc1_ucm_init_mode                    2
% 4.14/1.02  --bmc1_ucm_cone_mode                    none
% 4.14/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.14/1.02  --bmc1_ucm_relax_model                  4
% 4.14/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.14/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.14/1.02  --bmc1_ucm_layered_model                none
% 4.14/1.02  --bmc1_ucm_max_lemma_size               10
% 4.14/1.02  
% 4.14/1.02  ------ AIG Options
% 4.14/1.02  
% 4.14/1.02  --aig_mode                              false
% 4.14/1.02  
% 4.14/1.02  ------ Instantiation Options
% 4.14/1.02  
% 4.14/1.02  --instantiation_flag                    true
% 4.14/1.02  --inst_sos_flag                         true
% 4.14/1.02  --inst_sos_phase                        true
% 4.14/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.14/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.14/1.02  --inst_lit_sel_side                     none
% 4.14/1.02  --inst_solver_per_active                1400
% 4.14/1.02  --inst_solver_calls_frac                1.
% 4.14/1.02  --inst_passive_queue_type               priority_queues
% 4.14/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.14/1.02  --inst_passive_queues_freq              [25;2]
% 4.14/1.02  --inst_dismatching                      true
% 4.14/1.02  --inst_eager_unprocessed_to_passive     true
% 4.14/1.02  --inst_prop_sim_given                   true
% 4.14/1.02  --inst_prop_sim_new                     false
% 4.14/1.02  --inst_subs_new                         false
% 4.14/1.02  --inst_eq_res_simp                      false
% 4.14/1.02  --inst_subs_given                       false
% 4.14/1.02  --inst_orphan_elimination               true
% 4.14/1.02  --inst_learning_loop_flag               true
% 4.14/1.02  --inst_learning_start                   3000
% 4.14/1.02  --inst_learning_factor                  2
% 4.14/1.02  --inst_start_prop_sim_after_learn       3
% 4.14/1.02  --inst_sel_renew                        solver
% 4.14/1.02  --inst_lit_activity_flag                true
% 4.14/1.02  --inst_restr_to_given                   false
% 4.14/1.02  --inst_activity_threshold               500
% 4.14/1.02  --inst_out_proof                        true
% 4.14/1.02  
% 4.14/1.02  ------ Resolution Options
% 4.14/1.02  
% 4.14/1.02  --resolution_flag                       false
% 4.14/1.02  --res_lit_sel                           adaptive
% 4.14/1.02  --res_lit_sel_side                      none
% 4.14/1.02  --res_ordering                          kbo
% 4.14/1.02  --res_to_prop_solver                    active
% 4.14/1.02  --res_prop_simpl_new                    false
% 4.14/1.02  --res_prop_simpl_given                  true
% 4.14/1.02  --res_passive_queue_type                priority_queues
% 4.14/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.14/1.02  --res_passive_queues_freq               [15;5]
% 4.14/1.02  --res_forward_subs                      full
% 4.14/1.02  --res_backward_subs                     full
% 4.14/1.02  --res_forward_subs_resolution           true
% 4.14/1.02  --res_backward_subs_resolution          true
% 4.14/1.02  --res_orphan_elimination                true
% 4.14/1.02  --res_time_limit                        2.
% 4.14/1.02  --res_out_proof                         true
% 4.14/1.02  
% 4.14/1.02  ------ Superposition Options
% 4.14/1.02  
% 4.14/1.02  --superposition_flag                    true
% 4.14/1.02  --sup_passive_queue_type                priority_queues
% 4.14/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.14/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.14/1.02  --demod_completeness_check              fast
% 4.14/1.02  --demod_use_ground                      true
% 4.14/1.02  --sup_to_prop_solver                    passive
% 4.14/1.02  --sup_prop_simpl_new                    true
% 4.14/1.02  --sup_prop_simpl_given                  true
% 4.14/1.02  --sup_fun_splitting                     true
% 4.14/1.02  --sup_smt_interval                      50000
% 4.14/1.02  
% 4.14/1.02  ------ Superposition Simplification Setup
% 4.14/1.02  
% 4.14/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.14/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.14/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.14/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.14/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.14/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.14/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.14/1.02  --sup_immed_triv                        [TrivRules]
% 4.14/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/1.02  --sup_immed_bw_main                     []
% 4.14/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.14/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.14/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/1.02  --sup_input_bw                          []
% 4.14/1.02  
% 4.14/1.02  ------ Combination Options
% 4.14/1.02  
% 4.14/1.02  --comb_res_mult                         3
% 4.14/1.02  --comb_sup_mult                         2
% 4.14/1.02  --comb_inst_mult                        10
% 4.14/1.02  
% 4.14/1.02  ------ Debug Options
% 4.14/1.02  
% 4.14/1.02  --dbg_backtrace                         false
% 4.14/1.02  --dbg_dump_prop_clauses                 false
% 4.14/1.02  --dbg_dump_prop_clauses_file            -
% 4.14/1.02  --dbg_out_stat                          false
% 4.14/1.02  
% 4.14/1.02  
% 4.14/1.02  
% 4.14/1.02  
% 4.14/1.02  ------ Proving...
% 4.14/1.02  
% 4.14/1.02  
% 4.14/1.02  % SZS status Theorem for theBenchmark.p
% 4.14/1.02  
% 4.14/1.02   Resolution empty clause
% 4.14/1.02  
% 4.14/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 4.14/1.02  
% 4.14/1.02  fof(f9,axiom,(
% 4.14/1.02    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f30,plain,(
% 4.14/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 4.14/1.02    inference(cnf_transformation,[],[f9])).
% 4.14/1.02  
% 4.14/1.02  fof(f6,axiom,(
% 4.14/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f27,plain,(
% 4.14/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.14/1.02    inference(cnf_transformation,[],[f6])).
% 4.14/1.02  
% 4.14/1.02  fof(f12,axiom,(
% 4.14/1.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f33,plain,(
% 4.14/1.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 4.14/1.02    inference(cnf_transformation,[],[f12])).
% 4.14/1.02  
% 4.14/1.02  fof(f10,axiom,(
% 4.14/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f31,plain,(
% 4.14/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.14/1.02    inference(cnf_transformation,[],[f10])).
% 4.14/1.02  
% 4.14/1.02  fof(f41,plain,(
% 4.14/1.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 4.14/1.02    inference(definition_unfolding,[],[f33,f31])).
% 4.14/1.02  
% 4.14/1.02  fof(f11,axiom,(
% 4.14/1.02    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f32,plain,(
% 4.14/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 4.14/1.02    inference(cnf_transformation,[],[f11])).
% 4.14/1.02  
% 4.14/1.02  fof(f1,axiom,(
% 4.14/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f21,plain,(
% 4.14/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.14/1.02    inference(cnf_transformation,[],[f1])).
% 4.14/1.02  
% 4.14/1.02  fof(f13,conjecture,(
% 4.14/1.02    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f14,negated_conjecture,(
% 4.14/1.02    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 4.14/1.02    inference(negated_conjecture,[],[f13])).
% 4.14/1.02  
% 4.14/1.02  fof(f16,plain,(
% 4.14/1.02    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 4.14/1.02    inference(ennf_transformation,[],[f14])).
% 4.14/1.02  
% 4.14/1.02  fof(f17,plain,(
% 4.14/1.02    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 4.14/1.02    inference(flattening,[],[f16])).
% 4.14/1.02  
% 4.14/1.02  fof(f19,plain,(
% 4.14/1.02    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 4.14/1.02    introduced(choice_axiom,[])).
% 4.14/1.02  
% 4.14/1.02  fof(f20,plain,(
% 4.14/1.02    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 4.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).
% 4.14/1.02  
% 4.14/1.02  fof(f34,plain,(
% 4.14/1.02    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 4.14/1.02    inference(cnf_transformation,[],[f20])).
% 4.14/1.02  
% 4.14/1.02  fof(f8,axiom,(
% 4.14/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f29,plain,(
% 4.14/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 4.14/1.02    inference(cnf_transformation,[],[f8])).
% 4.14/1.02  
% 4.14/1.02  fof(f35,plain,(
% 4.14/1.02    r1_xboole_0(sK2,sK0)),
% 4.14/1.02    inference(cnf_transformation,[],[f20])).
% 4.14/1.02  
% 4.14/1.02  fof(f3,axiom,(
% 4.14/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f15,plain,(
% 4.14/1.02    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 4.14/1.02    inference(ennf_transformation,[],[f3])).
% 4.14/1.02  
% 4.14/1.02  fof(f24,plain,(
% 4.14/1.02    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 4.14/1.02    inference(cnf_transformation,[],[f15])).
% 4.14/1.02  
% 4.14/1.02  fof(f2,axiom,(
% 4.14/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f18,plain,(
% 4.14/1.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.14/1.02    inference(nnf_transformation,[],[f2])).
% 4.14/1.02  
% 4.14/1.02  fof(f22,plain,(
% 4.14/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.14/1.02    inference(cnf_transformation,[],[f18])).
% 4.14/1.02  
% 4.14/1.02  fof(f39,plain,(
% 4.14/1.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.14/1.02    inference(definition_unfolding,[],[f22,f31])).
% 4.14/1.02  
% 4.14/1.02  fof(f4,axiom,(
% 4.14/1.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f25,plain,(
% 4.14/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.14/1.02    inference(cnf_transformation,[],[f4])).
% 4.14/1.02  
% 4.14/1.02  fof(f36,plain,(
% 4.14/1.02    r1_xboole_0(sK3,sK1)),
% 4.14/1.02    inference(cnf_transformation,[],[f20])).
% 4.14/1.02  
% 4.14/1.02  fof(f5,axiom,(
% 4.14/1.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f26,plain,(
% 4.14/1.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 4.14/1.02    inference(cnf_transformation,[],[f5])).
% 4.14/1.02  
% 4.14/1.02  fof(f40,plain,(
% 4.14/1.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 4.14/1.02    inference(definition_unfolding,[],[f26,f31])).
% 4.14/1.02  
% 4.14/1.02  fof(f7,axiom,(
% 4.14/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.14/1.02  
% 4.14/1.02  fof(f28,plain,(
% 4.14/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.14/1.02    inference(cnf_transformation,[],[f7])).
% 4.14/1.02  
% 4.14/1.02  fof(f37,plain,(
% 4.14/1.02    sK1 != sK2),
% 4.14/1.02    inference(cnf_transformation,[],[f20])).
% 4.14/1.02  
% 4.14/1.02  cnf(c_9,plain,
% 4.14/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 4.14/1.02      inference(cnf_transformation,[],[f30]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_6,plain,
% 4.14/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.14/1.02      inference(cnf_transformation,[],[f27]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_566,plain,
% 4.14/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_9,c_6]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_11,plain,
% 4.14/1.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 4.14/1.02      inference(cnf_transformation,[],[f41]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_10,plain,
% 4.14/1.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 4.14/1.02      inference(cnf_transformation,[],[f32]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_0,plain,
% 4.14/1.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 4.14/1.02      inference(cnf_transformation,[],[f21]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_101,plain,
% 4.14/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 4.14/1.02      inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_473,plain,
% 4.14/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_6,c_101]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_1107,plain,
% 4.14/1.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_473,c_0]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_15,negated_conjecture,
% 4.14/1.02      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 4.14/1.02      inference(cnf_transformation,[],[f34]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_100,negated_conjecture,
% 4.14/1.02      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 4.14/1.02      inference(theory_normalisation,[status(thm)],[c_15,c_10,c_0]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_609,plain,
% 4.14/1.02      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_100,c_10]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_683,plain,
% 4.14/1.02      ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_609,c_10]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_1544,plain,
% 4.14/1.02      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK2,sK3) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_1107,c_683]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_1549,plain,
% 4.14/1.02      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK1,sK0) ),
% 4.14/1.02      inference(light_normalisation,[status(thm)],[c_1544,c_100]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8,plain,
% 4.14/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 4.14/1.02      inference(cnf_transformation,[],[f29]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_2116,plain,
% 4.14/1.02      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_1549,c_8]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_9600,plain,
% 4.14/1.02      ( k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,k2_xboole_0(X0,sK0)))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_566,c_2116]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_9616,plain,
% 4.14/1.02      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_9600,c_566]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_14,negated_conjecture,
% 4.14/1.02      ( r1_xboole_0(sK2,sK0) ),
% 4.14/1.02      inference(cnf_transformation,[],[f35]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_267,plain,
% 4.14/1.02      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 4.14/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_3,plain,
% 4.14/1.02      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 4.14/1.02      inference(cnf_transformation,[],[f24]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_269,plain,
% 4.14/1.02      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 4.14/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_949,plain,
% 4.14/1.02      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_267,c_269]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_2,plain,
% 4.14/1.02      ( ~ r1_xboole_0(X0,X1)
% 4.14/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 4.14/1.02      inference(cnf_transformation,[],[f39]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_270,plain,
% 4.14/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 4.14/1.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 4.14/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_1523,plain,
% 4.14/1.02      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_949,c_270]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8449,plain,
% 4.14/1.02      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_1523,c_6]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_4,plain,
% 4.14/1.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.14/1.02      inference(cnf_transformation,[],[f25]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8450,plain,
% 4.14/1.02      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_8449,c_4,c_473]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_542,plain,
% 4.14/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8915,plain,
% 4.14/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k2_xboole_0(sK2,sK0),sK0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_8450,c_542]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8916,plain,
% 4.14/1.02      ( k4_xboole_0(k2_xboole_0(sK2,sK0),sK0) = k4_xboole_0(sK2,sK0) ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_8915,c_8450]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_1521,plain,
% 4.14/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_267,c_270]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_2197,plain,
% 4.14/1.02      ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_1521,c_6]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_2198,plain,
% 4.14/1.02      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_2197,c_4,c_473]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_13,negated_conjecture,
% 4.14/1.02      ( r1_xboole_0(sK3,sK1) ),
% 4.14/1.02      inference(cnf_transformation,[],[f36]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_268,plain,
% 4.14/1.02      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 4.14/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_1520,plain,
% 4.14/1.02      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_268,c_270]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_2132,plain,
% 4.14/1.02      ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_1520,c_6]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_2134,plain,
% 4.14/1.02      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_2132,c_4,c_473]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_2401,plain,
% 4.14/1.02      ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_2134,c_9]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_5,plain,
% 4.14/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.14/1.02      inference(cnf_transformation,[],[f40]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_7,plain,
% 4.14/1.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.14/1.02      inference(cnf_transformation,[],[f28]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_272,plain,
% 4.14/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.14/1.02      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_567,plain,
% 4.14/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_9,c_272]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_568,plain,
% 4.14/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_567,c_6]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_1122,plain,
% 4.14/1.02      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_100,c_568]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_6251,plain,
% 4.14/1.02      ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_2401,c_1122]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_6830,plain,
% 4.14/1.02      ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_6251,c_6]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_6837,plain,
% 4.14/1.02      ( k2_xboole_0(sK0,sK3) = sK0 ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_6830,c_4]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_7707,plain,
% 4.14/1.02      ( k2_xboole_0(sK3,sK0) = sK0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_6837,c_0]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_7800,plain,
% 4.14/1.02      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK0)) = k2_xboole_0(sK2,sK0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_7707,c_683]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_472,plain,
% 4.14/1.02      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_272,c_6]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_474,plain,
% 4.14/1.02      ( k2_xboole_0(X0,X0) = X0 ),
% 4.14/1.02      inference(light_normalisation,[status(thm)],[c_472,c_4]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_7801,plain,
% 4.14/1.02      ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,sK0) ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_7800,c_474]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8917,plain,
% 4.14/1.02      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK0) = sK2 ),
% 4.14/1.02      inference(light_normalisation,[status(thm)],[c_8916,c_2198,c_7801]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_7702,plain,
% 4.14/1.02      ( k2_xboole_0(sK0,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,X0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_6837,c_10]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8942,plain,
% 4.14/1.02      ( k2_xboole_0(sK0,k4_xboole_0(sK3,X0)) = k2_xboole_0(sK0,sK3) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_1107,c_7702]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8992,plain,
% 4.14/1.02      ( k2_xboole_0(sK0,k4_xboole_0(sK3,X0)) = sK0 ),
% 4.14/1.02      inference(light_normalisation,[status(thm)],[c_8942,c_6837]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_9617,plain,
% 4.14/1.02      ( k4_xboole_0(sK1,sK0) = sK2 ),
% 4.14/1.02      inference(light_normalisation,
% 4.14/1.02                [status(thm)],
% 4.14/1.02                [c_9616,c_2116,c_8917,c_8992]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_948,plain,
% 4.14/1.02      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_268,c_269]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_1522,plain,
% 4.14/1.02      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_948,c_270]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8332,plain,
% 4.14/1.02      ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_1522,c_6]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_8333,plain,
% 4.14/1.02      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_8332,c_4,c_473]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_2118,plain,
% 4.14/1.02      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_1549,c_568]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_9523,plain,
% 4.14/1.02      ( k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_100,c_566]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_10375,plain,
% 4.14/1.02      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 4.14/1.02      inference(superposition,[status(thm)],[c_2118,c_9523]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_10431,plain,
% 4.14/1.02      ( k2_xboole_0(sK3,k1_xboole_0) = sK0 ),
% 4.14/1.02      inference(light_normalisation,
% 4.14/1.02                [status(thm)],
% 4.14/1.02                [c_10375,c_7707,c_8450,c_8992]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_10432,plain,
% 4.14/1.02      ( sK0 = sK3 ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_10431,c_4]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_10710,plain,
% 4.14/1.02      ( sK2 = sK1 ),
% 4.14/1.02      inference(light_normalisation,
% 4.14/1.02                [status(thm)],
% 4.14/1.02                [c_9617,c_8333,c_9617,c_10432]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_12,negated_conjecture,
% 4.14/1.02      ( sK1 != sK2 ),
% 4.14/1.02      inference(cnf_transformation,[],[f37]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_10747,plain,
% 4.14/1.02      ( sK1 != sK1 ),
% 4.14/1.02      inference(demodulation,[status(thm)],[c_10710,c_12]) ).
% 4.14/1.02  
% 4.14/1.02  cnf(c_10748,plain,
% 4.14/1.02      ( $false ),
% 4.14/1.02      inference(equality_resolution_simp,[status(thm)],[c_10747]) ).
% 4.14/1.02  
% 4.14/1.02  
% 4.14/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 4.14/1.02  
% 4.14/1.02  ------                               Statistics
% 4.14/1.02  
% 4.14/1.02  ------ General
% 4.14/1.02  
% 4.14/1.02  abstr_ref_over_cycles:                  0
% 4.14/1.02  abstr_ref_under_cycles:                 0
% 4.14/1.02  gc_basic_clause_elim:                   0
% 4.14/1.02  forced_gc_time:                         0
% 4.14/1.02  parsing_time:                           0.014
% 4.14/1.02  unif_index_cands_time:                  0.
% 4.14/1.02  unif_index_add_time:                    0.
% 4.14/1.02  orderings_time:                         0.
% 4.14/1.02  out_proof_time:                         0.008
% 4.14/1.02  total_time:                             0.412
% 4.14/1.02  num_of_symbols:                         39
% 4.14/1.02  num_of_terms:                           16731
% 4.14/1.02  
% 4.14/1.02  ------ Preprocessing
% 4.14/1.02  
% 4.14/1.02  num_of_splits:                          0
% 4.14/1.02  num_of_split_atoms:                     0
% 4.14/1.02  num_of_reused_defs:                     0
% 4.14/1.02  num_eq_ax_congr_red:                    0
% 4.14/1.02  num_of_sem_filtered_clauses:            1
% 4.14/1.02  num_of_subtypes:                        0
% 4.14/1.02  monotx_restored_types:                  0
% 4.14/1.02  sat_num_of_epr_types:                   0
% 4.14/1.02  sat_num_of_non_cyclic_types:            0
% 4.14/1.02  sat_guarded_non_collapsed_types:        0
% 4.14/1.02  num_pure_diseq_elim:                    0
% 4.14/1.02  simp_replaced_by:                       0
% 4.14/1.02  res_preprocessed:                       59
% 4.14/1.02  prep_upred:                             0
% 4.14/1.02  prep_unflattend:                        0
% 4.14/1.02  smt_new_axioms:                         0
% 4.14/1.02  pred_elim_cands:                        1
% 4.14/1.02  pred_elim:                              0
% 4.14/1.02  pred_elim_cl:                           0
% 4.14/1.02  pred_elim_cycles:                       1
% 4.14/1.02  merged_defs:                            6
% 4.14/1.02  merged_defs_ncl:                        0
% 4.14/1.02  bin_hyper_res:                          6
% 4.14/1.02  prep_cycles:                            3
% 4.14/1.02  pred_elim_time:                         0.
% 4.14/1.02  splitting_time:                         0.
% 4.14/1.02  sem_filter_time:                        0.
% 4.14/1.02  monotx_time:                            0.
% 4.14/1.02  subtype_inf_time:                       0.
% 4.14/1.02  
% 4.14/1.02  ------ Problem properties
% 4.14/1.02  
% 4.14/1.02  clauses:                                16
% 4.14/1.02  conjectures:                            4
% 4.14/1.02  epr:                                    4
% 4.14/1.02  horn:                                   16
% 4.14/1.02  ground:                                 4
% 4.14/1.02  unary:                                  13
% 4.14/1.02  binary:                                 3
% 4.14/1.02  lits:                                   19
% 4.14/1.02  lits_eq:                                13
% 4.14/1.02  fd_pure:                                0
% 4.14/1.02  fd_pseudo:                              0
% 4.14/1.02  fd_cond:                                0
% 4.14/1.02  fd_pseudo_cond:                         0
% 4.14/1.02  ac_symbols:                             1
% 4.14/1.02  
% 4.14/1.02  ------ Propositional Solver
% 4.14/1.02  
% 4.14/1.02  prop_solver_calls:                      31
% 4.14/1.02  prop_fast_solver_calls:                 318
% 4.14/1.02  smt_solver_calls:                       0
% 4.14/1.02  smt_fast_solver_calls:                  0
% 4.14/1.02  prop_num_of_clauses:                    4589
% 4.14/1.02  prop_preprocess_simplified:             5864
% 4.14/1.02  prop_fo_subsumed:                       0
% 4.14/1.02  prop_solver_time:                       0.
% 4.14/1.02  smt_solver_time:                        0.
% 4.14/1.02  smt_fast_solver_time:                   0.
% 4.14/1.02  prop_fast_solver_time:                  0.
% 4.14/1.02  prop_unsat_core_time:                   0.
% 4.14/1.02  
% 4.14/1.02  ------ QBF
% 4.14/1.02  
% 4.14/1.02  qbf_q_res:                              0
% 4.14/1.02  qbf_num_tautologies:                    0
% 4.14/1.02  qbf_prep_cycles:                        0
% 4.14/1.02  
% 4.14/1.02  ------ BMC1
% 4.14/1.02  
% 4.14/1.02  bmc1_current_bound:                     -1
% 4.14/1.02  bmc1_last_solved_bound:                 -1
% 4.14/1.02  bmc1_unsat_core_size:                   -1
% 4.14/1.02  bmc1_unsat_core_parents_size:           -1
% 4.14/1.02  bmc1_merge_next_fun:                    0
% 4.14/1.02  bmc1_unsat_core_clauses_time:           0.
% 4.14/1.02  
% 4.14/1.02  ------ Instantiation
% 4.14/1.02  
% 4.14/1.02  inst_num_of_clauses:                    1798
% 4.14/1.02  inst_num_in_passive:                    464
% 4.14/1.02  inst_num_in_active:                     510
% 4.14/1.02  inst_num_in_unprocessed:                824
% 4.14/1.02  inst_num_of_loops:                      610
% 4.14/1.02  inst_num_of_learning_restarts:          0
% 4.14/1.02  inst_num_moves_active_passive:          93
% 4.14/1.02  inst_lit_activity:                      0
% 4.14/1.02  inst_lit_activity_moves:                0
% 4.14/1.02  inst_num_tautologies:                   0
% 4.14/1.02  inst_num_prop_implied:                  0
% 4.14/1.02  inst_num_existing_simplified:           0
% 4.14/1.02  inst_num_eq_res_simplified:             0
% 4.14/1.02  inst_num_child_elim:                    0
% 4.14/1.02  inst_num_of_dismatching_blockings:      347
% 4.14/1.02  inst_num_of_non_proper_insts:           1528
% 4.14/1.02  inst_num_of_duplicates:                 0
% 4.14/1.02  inst_inst_num_from_inst_to_res:         0
% 4.14/1.02  inst_dismatching_checking_time:         0.
% 4.14/1.02  
% 4.14/1.02  ------ Resolution
% 4.14/1.02  
% 4.14/1.02  res_num_of_clauses:                     0
% 4.14/1.02  res_num_in_passive:                     0
% 4.14/1.02  res_num_in_active:                      0
% 4.14/1.02  res_num_of_loops:                       62
% 4.14/1.02  res_forward_subset_subsumed:            452
% 4.14/1.02  res_backward_subset_subsumed:           0
% 4.14/1.02  res_forward_subsumed:                   0
% 4.14/1.02  res_backward_subsumed:                  0
% 4.14/1.02  res_forward_subsumption_resolution:     0
% 4.14/1.02  res_backward_subsumption_resolution:    0
% 4.14/1.02  res_clause_to_clause_subsumption:       12853
% 4.14/1.02  res_orphan_elimination:                 0
% 4.14/1.02  res_tautology_del:                      139
% 4.14/1.02  res_num_eq_res_simplified:              0
% 4.14/1.02  res_num_sel_changes:                    0
% 4.14/1.02  res_moves_from_active_to_pass:          0
% 4.14/1.02  
% 4.14/1.02  ------ Superposition
% 4.14/1.02  
% 4.14/1.02  sup_time_total:                         0.
% 4.14/1.02  sup_time_generating:                    0.
% 4.14/1.02  sup_time_sim_full:                      0.
% 4.14/1.02  sup_time_sim_immed:                     0.
% 4.14/1.02  
% 4.14/1.02  sup_num_of_clauses:                     946
% 4.14/1.02  sup_num_in_active:                      61
% 4.14/1.02  sup_num_in_passive:                     885
% 4.14/1.02  sup_num_of_loops:                       120
% 4.14/1.02  sup_fw_superposition:                   1739
% 4.14/1.02  sup_bw_superposition:                   1453
% 4.14/1.02  sup_immediate_simplified:               1563
% 4.14/1.02  sup_given_eliminated:                   10
% 4.14/1.02  comparisons_done:                       0
% 4.14/1.02  comparisons_avoided:                    0
% 4.14/1.02  
% 4.14/1.02  ------ Simplifications
% 4.14/1.02  
% 4.14/1.02  
% 4.14/1.02  sim_fw_subset_subsumed:                 4
% 4.14/1.02  sim_bw_subset_subsumed:                 0
% 4.14/1.02  sim_fw_subsumed:                        261
% 4.14/1.02  sim_bw_subsumed:                        20
% 4.14/1.02  sim_fw_subsumption_res:                 0
% 4.14/1.02  sim_bw_subsumption_res:                 0
% 4.14/1.02  sim_tautology_del:                      0
% 4.14/1.02  sim_eq_tautology_del:                   351
% 4.14/1.02  sim_eq_res_simp:                        3
% 4.14/1.02  sim_fw_demodulated:                     824
% 4.14/1.02  sim_bw_demodulated:                     106
% 4.14/1.02  sim_light_normalised:                   685
% 4.14/1.02  sim_joinable_taut:                      61
% 4.14/1.02  sim_joinable_simp:                      0
% 4.14/1.02  sim_ac_normalised:                      0
% 4.14/1.02  sim_smt_subsumption:                    0
% 4.14/1.02  
%------------------------------------------------------------------------------
