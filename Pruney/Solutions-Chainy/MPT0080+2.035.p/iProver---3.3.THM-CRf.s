%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:58 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 506 expanded)
%              Number of clauses        :   67 ( 228 expanded)
%              Number of leaves         :   11 ( 115 expanded)
%              Depth                    :   21
%              Number of atoms          :  131 ( 762 expanded)
%              Number of equality atoms :   86 ( 435 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f14])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f29,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_651,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_657,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_651,c_4])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_294,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_299,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2685,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_294,c_299])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3251,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2685,c_7])).

cnf(c_3449,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3251])).

cnf(c_3957,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_657,c_3449])).

cnf(c_648,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_1802,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_648,c_4])).

cnf(c_1805,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1802,c_4])).

cnf(c_3959,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_1805,c_3449])).

cnf(c_3984,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3959,c_2685])).

cnf(c_4004,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3984,c_7])).

cnf(c_1795,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_4,c_648])).

cnf(c_1820,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1795,c_648])).

cnf(c_3247,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2685,c_1820])).

cnf(c_3261,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3247,c_2685])).

cnf(c_4521,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4004,c_3261])).

cnf(c_12639,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3957,c_4521])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_295,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_300,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4183,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_295,c_300])).

cnf(c_4714,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_4183,c_4])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_652,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_654,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_652,c_5])).

cnf(c_4716,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_4714,c_654])).

cnf(c_5288,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_4716,c_0])).

cnf(c_650,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_5779,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) ),
    inference(superposition,[status(thm)],[c_5288,c_650])).

cnf(c_5795,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_5779,c_7])).

cnf(c_816,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_654,c_0])).

cnf(c_829,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_816,c_6])).

cnf(c_937,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_829,c_4])).

cnf(c_939,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_937,c_654])).

cnf(c_1120,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_829,c_939])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_297,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_460,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_297])).

cnf(c_815,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_460])).

cnf(c_2689,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_815,c_299])).

cnf(c_535,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_460])).

cnf(c_1551,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_535])).

cnf(c_2076,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1551])).

cnf(c_2694,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2076,c_299])).

cnf(c_2710,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2689,c_2694])).

cnf(c_2713,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2710,c_5])).

cnf(c_2843,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_2713,c_7])).

cnf(c_2857,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_2843])).

cnf(c_5796,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_5795,c_1120,c_2857])).

cnf(c_5797,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_5796,c_4521])).

cnf(c_5798,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_5797,c_5])).

cnf(c_6095,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_5798,c_7])).

cnf(c_12658,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12639,c_6095])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_359,plain,
    ( r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12658,c_359,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.99  
% 3.53/0.99  ------  iProver source info
% 3.53/0.99  
% 3.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.99  git: non_committed_changes: false
% 3.53/0.99  git: last_make_outside_of_git: false
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  ------ Parsing...
% 3.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.99  ------ Proving...
% 3.53/0.99  ------ Problem Properties 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  clauses                                 12
% 3.53/0.99  conjectures                             3
% 3.53/0.99  EPR                                     2
% 3.53/0.99  Horn                                    12
% 3.53/0.99  unary                                   9
% 3.53/0.99  binary                                  3
% 3.53/0.99  lits                                    15
% 3.53/0.99  lits eq                                 8
% 3.53/0.99  fd_pure                                 0
% 3.53/0.99  fd_pseudo                               0
% 3.53/0.99  fd_cond                                 0
% 3.53/0.99  fd_pseudo_cond                          0
% 3.53/0.99  AC symbols                              0
% 3.53/0.99  
% 3.53/0.99  ------ Input Options Time Limit: Unbounded
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  Current options:
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ Proving...
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS status Theorem for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  fof(f6,axiom,(
% 3.53/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f25,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f6])).
% 3.53/0.99  
% 3.53/0.99  fof(f4,axiom,(
% 3.53/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f23,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f4])).
% 3.53/0.99  
% 3.53/0.99  fof(f1,axiom,(
% 3.53/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f19,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f1])).
% 3.53/0.99  
% 3.53/0.99  fof(f10,conjecture,(
% 3.53/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f11,negated_conjecture,(
% 3.53/0.99    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.53/0.99    inference(negated_conjecture,[],[f10])).
% 3.53/0.99  
% 3.53/0.99  fof(f14,plain,(
% 3.53/0.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.53/0.99    inference(ennf_transformation,[],[f11])).
% 3.53/0.99  
% 3.53/0.99  fof(f15,plain,(
% 3.53/0.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.53/0.99    inference(flattening,[],[f14])).
% 3.53/0.99  
% 3.53/0.99  fof(f17,plain,(
% 3.53/0.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f18,plain,(
% 3.53/0.99    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 3.53/0.99  
% 3.53/0.99  fof(f29,plain,(
% 3.53/0.99    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 3.53/0.99    inference(cnf_transformation,[],[f18])).
% 3.53/0.99  
% 3.53/0.99  fof(f3,axiom,(
% 3.53/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f16,plain,(
% 3.53/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.53/0.99    inference(nnf_transformation,[],[f3])).
% 3.53/0.99  
% 3.53/0.99  fof(f22,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f16])).
% 3.53/0.99  
% 3.53/0.99  fof(f7,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f26,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f7])).
% 3.53/0.99  
% 3.53/0.99  fof(f30,plain,(
% 3.53/0.99    r1_xboole_0(sK0,sK2)),
% 3.53/0.99    inference(cnf_transformation,[],[f18])).
% 3.53/0.99  
% 3.53/0.99  fof(f2,axiom,(
% 3.53/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f12,plain,(
% 3.53/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.53/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.53/0.99  
% 3.53/0.99  fof(f13,plain,(
% 3.53/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.53/0.99    inference(ennf_transformation,[],[f12])).
% 3.53/0.99  
% 3.53/0.99  fof(f20,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f13])).
% 3.53/0.99  
% 3.53/0.99  fof(f8,axiom,(
% 3.53/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f27,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f8])).
% 3.53/0.99  
% 3.53/0.99  fof(f32,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f20,f27])).
% 3.53/0.99  
% 3.53/0.99  fof(f5,axiom,(
% 3.53/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f24,plain,(
% 3.53/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.53/0.99    inference(cnf_transformation,[],[f5])).
% 3.53/0.99  
% 3.53/0.99  fof(f9,axiom,(
% 3.53/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f28,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f9])).
% 3.53/0.99  
% 3.53/0.99  fof(f21,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f16])).
% 3.53/0.99  
% 3.53/0.99  fof(f31,plain,(
% 3.53/0.99    ~r1_tarski(sK0,sK1)),
% 3.53/0.99    inference(cnf_transformation,[],[f18])).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6,plain,
% 3.53/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4,plain,
% 3.53/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_651,plain,
% 3.53/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_657,plain,
% 3.53/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.53/0.99      inference(light_normalisation,[status(thm)],[c_651,c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_0,plain,
% 3.53/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f19]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_11,negated_conjecture,
% 3.53/0.99      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_294,plain,
% 3.53/0.99      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_299,plain,
% 3.53/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.53/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2685,plain,
% 3.53/0.99      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_294,c_299]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7,plain,
% 3.53/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3251,plain,
% 3.53/0.99      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_2685,c_7]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3449,plain,
% 3.53/0.99      ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_0,c_3251]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3957,plain,
% 3.53/0.99      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k4_xboole_0(k1_xboole_0,sK2) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_657,c_3449]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_648,plain,
% 3.53/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1802,plain,
% 3.53/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_648,c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1805,plain,
% 3.53/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 3.53/0.99      inference(light_normalisation,[status(thm)],[c_1802,c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3959,plain,
% 3.53/0.99      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,sK1) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1805,c_3449]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3984,plain,
% 3.53/0.99      ( k4_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
% 3.53/0.99      inference(light_normalisation,[status(thm)],[c_3959,c_2685]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4004,plain,
% 3.53/0.99      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_3984,c_7]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1795,plain,
% 3.53/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_4,c_648]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1820,plain,
% 3.53/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.53/0.99      inference(demodulation,[status(thm)],[c_1795,c_648]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3247,plain,
% 3.53/0.99      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_2685,c_1820]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3261,plain,
% 3.53/0.99      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 3.53/0.99      inference(light_normalisation,[status(thm)],[c_3247,c_2685]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4521,plain,
% 3.53/0.99      ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_4004,c_3261]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_12639,plain,
% 3.53/0.99      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 3.53/0.99      inference(light_normalisation,[status(thm)],[c_3957,c_4521]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_10,negated_conjecture,
% 3.53/0.99      ( r1_xboole_0(sK0,sK2) ),
% 3.53/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_295,plain,
% 3.53/0.99      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1,plain,
% 3.53/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.53/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_300,plain,
% 3.53/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.53/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4183,plain,
% 3.53/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_295,c_300]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4714,plain,
% 3.53/1.00      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4183,c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5,plain,
% 3.53/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_652,plain,
% 3.53/1.00      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_654,plain,
% 3.53/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_652,c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4716,plain,
% 3.53/1.00      ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k4_xboole_0(sK0,sK2) ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_4714,c_654]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5288,plain,
% 3.53/1.00      ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK2) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4716,c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_650,plain,
% 3.53/1.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5779,plain,
% 3.53/1.00      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_5288,c_650]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5795,plain,
% 3.53/1.00      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK2,sK0))) ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_5779,c_7]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_816,plain,
% 3.53/1.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_654,c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_829,plain,
% 3.53/1.00      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_816,c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_937,plain,
% 3.53/1.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_829,c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_939,plain,
% 3.53/1.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_937,c_654]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1120,plain,
% 3.53/1.00      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_829,c_939]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8,plain,
% 3.53/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_297,plain,
% 3.53/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_460,plain,
% 3.53/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_0,c_297]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_815,plain,
% 3.53/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_654,c_460]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2689,plain,
% 3.53/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_815,c_299]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_535,plain,
% 3.53/1.00      ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4,c_460]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1551,plain,
% 3.53/1.00      ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_0,c_535]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2076,plain,
% 3.53/1.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1120,c_1551]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2694,plain,
% 3.53/1.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X0) = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2076,c_299]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2710,plain,
% 3.53/1.00      ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2689,c_2694]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2713,plain,
% 3.53/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2710,c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2843,plain,
% 3.53/1.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2713,c_7]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2857,plain,
% 3.53/1.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,X1) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_0,c_2843]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5796,plain,
% 3.53/1.00      ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK0,sK2) ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_5795,c_1120,c_2857]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5797,plain,
% 3.53/1.00      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_5796,c_4521]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5798,plain,
% 3.53/1.00      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_5797,c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6095,plain,
% 3.53/1.00      ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_5798,c_7]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12658,plain,
% 3.53/1.00      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_12639,c_6095]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f21]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_359,plain,
% 3.53/1.00      ( r1_tarski(sK0,sK1) | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9,negated_conjecture,
% 3.53/1.00      ( ~ r1_tarski(sK0,sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(contradiction,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(minisat,[status(thm)],[c_12658,c_359,c_9]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ Selected
% 3.53/1.00  
% 3.53/1.00  total_time:                             0.327
% 3.53/1.00  
%------------------------------------------------------------------------------
