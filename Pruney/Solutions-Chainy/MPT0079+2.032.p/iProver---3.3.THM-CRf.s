%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:50 EST 2020

% Result     : Theorem 43.47s
% Output     : CNFRefutation 43.47s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 661 expanded)
%              Number of clauses        :   79 ( 289 expanded)
%              Number of leaves         :   13 ( 161 expanded)
%              Depth                    :   26
%              Number of atoms          :  151 (1005 expanded)
%              Number of equality atoms :  118 ( 756 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f24,plain,
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

fof(f25,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f24])).

fof(f42,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f43,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_147,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_18,c_9,c_0])).

cnf(c_1116,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_147,c_9])).

cnf(c_1428,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1116,c_0])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_409,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_418,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12589,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_409,c_418])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14043,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_12589,c_6])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14045,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k4_xboole_0(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_14043,c_5])).

cnf(c_24325,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_14045,c_0])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_900,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_908,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_900,c_5])).

cnf(c_3946,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_908])).

cnf(c_12931,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3946,c_8])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1098,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_32502,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12931,c_1098])).

cnf(c_32916,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_32502,c_5])).

cnf(c_40318,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_32916])).

cnf(c_165263,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(k4_xboole_0(sK2,sK0),sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_24325,c_40318])).

cnf(c_166635,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)))) = sK2 ),
    inference(demodulation,[status(thm)],[c_165263,c_7])).

cnf(c_166636,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,k2_xboole_0(sK0,sK2))))) = sK2 ),
    inference(demodulation,[status(thm)],[c_166635,c_7])).

cnf(c_779,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_166637,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_166636,c_5,c_779,c_24325])).

cnf(c_176459,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_166637,c_7])).

cnf(c_193600,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,k2_xboole_0(sK3,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1428,c_176459])).

cnf(c_2392,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_779,c_6])).

cnf(c_2397,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2392,c_5])).

cnf(c_7640,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2397])).

cnf(c_16959,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_7640,c_0])).

cnf(c_193602,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_16959,c_176459])).

cnf(c_193743,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_193602,c_176459])).

cnf(c_193749,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,k2_xboole_0(sK3,sK0))) = k4_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_193600,c_193743])).

cnf(c_193751,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_193749,c_8])).

cnf(c_193860,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_193751,c_6])).

cnf(c_193881,plain,
    ( k2_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_193860,c_5])).

cnf(c_487,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_22481,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_5,c_487])).

cnf(c_194549,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_193881,c_22481])).

cnf(c_12905,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_147,c_3946])).

cnf(c_2386,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_147,c_779])).

cnf(c_2696,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2386,c_6])).

cnf(c_2698,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_2696,c_5])).

cnf(c_13064,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_12905,c_2698])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_410,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_417,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10745,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_417])).

cnf(c_12590,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10745,c_418])).

cnf(c_17728,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(superposition,[status(thm)],[c_12590,c_6])).

cnf(c_17730,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k4_xboole_0(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_17728,c_5])).

cnf(c_27866,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_17730,c_0])).

cnf(c_165266,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_27866,c_40318])).

cnf(c_166626,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)))) = sK1 ),
    inference(demodulation,[status(thm)],[c_165266,c_7])).

cnf(c_166627,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,k2_xboole_0(sK3,sK1))))) = sK1 ),
    inference(demodulation,[status(thm)],[c_166626,c_7])).

cnf(c_166628,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_166627,c_5,c_779,c_27866])).

cnf(c_176400,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_166628,c_7])).

cnf(c_187585,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_13064,c_176400])).

cnf(c_187842,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_187585,c_8])).

cnf(c_188520,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_187842,c_6])).

cnf(c_188551,plain,
    ( k2_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_188520,c_5])).

cnf(c_194782,plain,
    ( k2_xboole_0(k1_xboole_0,sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_194549,c_188551])).

cnf(c_635,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_194783,plain,
    ( sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_194782,c_635])).

cnf(c_151,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_632,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_152,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_533,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_631,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_194783,c_632,c_631,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.47/5.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.47/5.99  
% 43.47/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.47/5.99  
% 43.47/5.99  ------  iProver source info
% 43.47/5.99  
% 43.47/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.47/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.47/5.99  git: non_committed_changes: false
% 43.47/5.99  git: last_make_outside_of_git: false
% 43.47/5.99  
% 43.47/5.99  ------ 
% 43.47/5.99  ------ Parsing...
% 43.47/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.47/5.99  
% 43.47/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 43.47/5.99  
% 43.47/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.47/5.99  
% 43.47/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.47/5.99  ------ Proving...
% 43.47/5.99  ------ Problem Properties 
% 43.47/5.99  
% 43.47/5.99  
% 43.47/5.99  clauses                                 19
% 43.47/5.99  conjectures                             4
% 43.47/5.99  EPR                                     4
% 43.47/5.99  Horn                                    19
% 43.47/5.99  unary                                   11
% 43.47/5.99  binary                                  6
% 43.47/5.99  lits                                    30
% 43.47/5.99  lits eq                                 13
% 43.47/5.99  fd_pure                                 0
% 43.47/5.99  fd_pseudo                               0
% 43.47/5.99  fd_cond                                 0
% 43.47/5.99  fd_pseudo_cond                          1
% 43.47/5.99  AC symbols                              1
% 43.47/5.99  
% 43.47/5.99  ------ Input Options Time Limit: Unbounded
% 43.47/5.99  
% 43.47/5.99  
% 43.47/5.99  ------ 
% 43.47/5.99  Current options:
% 43.47/5.99  ------ 
% 43.47/5.99  
% 43.47/5.99  
% 43.47/5.99  
% 43.47/5.99  
% 43.47/5.99  ------ Proving...
% 43.47/5.99  
% 43.47/5.99  
% 43.47/5.99  % SZS status Theorem for theBenchmark.p
% 43.47/5.99  
% 43.47/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.47/5.99  
% 43.47/5.99  fof(f14,conjecture,(
% 43.47/5.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f15,negated_conjecture,(
% 43.47/5.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 43.47/5.99    inference(negated_conjecture,[],[f14])).
% 43.47/5.99  
% 43.47/5.99  fof(f21,plain,(
% 43.47/5.99    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 43.47/5.99    inference(ennf_transformation,[],[f15])).
% 43.47/5.99  
% 43.47/5.99  fof(f22,plain,(
% 43.47/5.99    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 43.47/5.99    inference(flattening,[],[f21])).
% 43.47/5.99  
% 43.47/5.99  fof(f24,plain,(
% 43.47/5.99    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 43.47/5.99    introduced(choice_axiom,[])).
% 43.47/5.99  
% 43.47/5.99  fof(f25,plain,(
% 43.47/5.99    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 43.47/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f24])).
% 43.47/5.99  
% 43.47/5.99  fof(f42,plain,(
% 43.47/5.99    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 43.47/5.99    inference(cnf_transformation,[],[f25])).
% 43.47/5.99  
% 43.47/5.99  fof(f10,axiom,(
% 43.47/5.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f36,plain,(
% 43.47/5.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 43.47/5.99    inference(cnf_transformation,[],[f10])).
% 43.47/5.99  
% 43.47/5.99  fof(f1,axiom,(
% 43.47/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f26,plain,(
% 43.47/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 43.47/5.99    inference(cnf_transformation,[],[f1])).
% 43.47/5.99  
% 43.47/5.99  fof(f43,plain,(
% 43.47/5.99    r1_xboole_0(sK2,sK0)),
% 43.47/5.99    inference(cnf_transformation,[],[f25])).
% 43.47/5.99  
% 43.47/5.99  fof(f2,axiom,(
% 43.47/5.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f23,plain,(
% 43.47/5.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 43.47/5.99    inference(nnf_transformation,[],[f2])).
% 43.47/5.99  
% 43.47/5.99  fof(f27,plain,(
% 43.47/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 43.47/5.99    inference(cnf_transformation,[],[f23])).
% 43.47/5.99  
% 43.47/5.99  fof(f9,axiom,(
% 43.47/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f35,plain,(
% 43.47/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.47/5.99    inference(cnf_transformation,[],[f9])).
% 43.47/5.99  
% 43.47/5.99  fof(f47,plain,(
% 43.47/5.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 43.47/5.99    inference(definition_unfolding,[],[f27,f35])).
% 43.47/5.99  
% 43.47/5.99  fof(f6,axiom,(
% 43.47/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f32,plain,(
% 43.47/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 43.47/5.99    inference(cnf_transformation,[],[f6])).
% 43.47/5.99  
% 43.47/5.99  fof(f5,axiom,(
% 43.47/5.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f31,plain,(
% 43.47/5.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.47/5.99    inference(cnf_transformation,[],[f5])).
% 43.47/5.99  
% 43.47/5.99  fof(f8,axiom,(
% 43.47/5.99    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f34,plain,(
% 43.47/5.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 43.47/5.99    inference(cnf_transformation,[],[f8])).
% 43.47/5.99  
% 43.47/5.99  fof(f7,axiom,(
% 43.47/5.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f33,plain,(
% 43.47/5.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 43.47/5.99    inference(cnf_transformation,[],[f7])).
% 43.47/5.99  
% 43.47/5.99  fof(f44,plain,(
% 43.47/5.99    r1_xboole_0(sK3,sK1)),
% 43.47/5.99    inference(cnf_transformation,[],[f25])).
% 43.47/5.99  
% 43.47/5.99  fof(f3,axiom,(
% 43.47/5.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 43.47/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.47/5.99  
% 43.47/5.99  fof(f16,plain,(
% 43.47/5.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 43.47/5.99    inference(ennf_transformation,[],[f3])).
% 43.47/5.99  
% 43.47/5.99  fof(f29,plain,(
% 43.47/5.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 43.47/5.99    inference(cnf_transformation,[],[f16])).
% 43.47/5.99  
% 43.47/5.99  fof(f45,plain,(
% 43.47/5.99    sK1 != sK2),
% 43.47/5.99    inference(cnf_transformation,[],[f25])).
% 43.47/5.99  
% 43.47/5.99  cnf(c_18,negated_conjecture,
% 43.47/5.99      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 43.47/5.99      inference(cnf_transformation,[],[f42]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_9,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.47/5.99      inference(cnf_transformation,[],[f36]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_0,plain,
% 43.47/5.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 43.47/5.99      inference(cnf_transformation,[],[f26]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_147,negated_conjecture,
% 43.47/5.99      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 43.47/5.99      inference(theory_normalisation,[status(thm)],[c_18,c_9,c_0]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_1116,plain,
% 43.47/5.99      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_147,c_9]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_1428,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_1116,c_0]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_17,negated_conjecture,
% 43.47/5.99      ( r1_xboole_0(sK2,sK0) ),
% 43.47/5.99      inference(cnf_transformation,[],[f43]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_409,plain,
% 43.47/5.99      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 43.47/5.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_2,plain,
% 43.47/5.99      ( ~ r1_xboole_0(X0,X1)
% 43.47/5.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.47/5.99      inference(cnf_transformation,[],[f47]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_418,plain,
% 43.47/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 43.47/5.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 43.47/5.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_12589,plain,
% 43.47/5.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_409,c_418]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_6,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 43.47/5.99      inference(cnf_transformation,[],[f32]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_14043,plain,
% 43.47/5.99      ( k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_12589,c_6]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_5,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.47/5.99      inference(cnf_transformation,[],[f31]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_14045,plain,
% 43.47/5.99      ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k4_xboole_0(sK2,sK0) ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_14043,c_5]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_24325,plain,
% 43.47/5.99      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_14045,c_0]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_8,plain,
% 43.47/5.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.47/5.99      inference(cnf_transformation,[],[f34]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_900,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_908,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_900,c_5]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_3946,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_0,c_908]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_12931,plain,
% 43.47/5.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_3946,c_8]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_7,plain,
% 43.47/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.47/5.99      inference(cnf_transformation,[],[f33]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_1098,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_32502,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_12931,c_1098]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_32916,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
% 43.47/5.99      inference(light_normalisation,[status(thm)],[c_32502,c_5]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_40318,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = X0 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_6,c_32916]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_165263,plain,
% 43.47/5.99      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(k4_xboole_0(sK2,sK0),sK2))) = sK2 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_24325,c_40318]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_166635,plain,
% 43.47/5.99      ( k2_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)))) = sK2 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_165263,c_7]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_166636,plain,
% 43.47/5.99      ( k2_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,k2_xboole_0(sK0,sK2))))) = sK2 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_166635,c_7]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_779,plain,
% 43.47/5.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_166637,plain,
% 43.47/5.99      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_166636,c_5,c_779,c_24325]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_176459,plain,
% 43.47/5.99      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_166637,c_7]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_193600,plain,
% 43.47/5.99      ( k4_xboole_0(sK2,k2_xboole_0(sK2,k2_xboole_0(sK3,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_1428,c_176459]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_2392,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_779,c_6]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_2397,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_2392,c_5]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_7640,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_0,c_2397]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_16959,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_7640,c_0]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_193602,plain,
% 43.47/5.99      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_16959,c_176459]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_193743,plain,
% 43.47/5.99      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,X0) ),
% 43.47/5.99      inference(light_normalisation,[status(thm)],[c_193602,c_176459]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_193749,plain,
% 43.47/5.99      ( k4_xboole_0(sK2,k2_xboole_0(sK2,k2_xboole_0(sK3,sK0))) = k4_xboole_0(sK2,sK1) ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_193600,c_193743]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_193751,plain,
% 43.47/5.99      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_193749,c_8]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_193860,plain,
% 43.47/5.99      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_193751,c_6]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_193881,plain,
% 43.47/5.99      ( k2_xboole_0(sK1,sK2) = sK1 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_193860,c_5]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_487,plain,
% 43.47/5.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_22481,plain,
% 43.47/5.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_5,c_487]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_194549,plain,
% 43.47/5.99      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK1) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_193881,c_22481]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_12905,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK3,sK2) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_147,c_3946]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_2386,plain,
% 43.47/5.99      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_147,c_779]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_2696,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_2386,c_6]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_2698,plain,
% 43.47/5.99      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_2696,c_5]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_13064,plain,
% 43.47/5.99      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
% 43.47/5.99      inference(light_normalisation,[status(thm)],[c_12905,c_2698]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_16,negated_conjecture,
% 43.47/5.99      ( r1_xboole_0(sK3,sK1) ),
% 43.47/5.99      inference(cnf_transformation,[],[f44]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_410,plain,
% 43.47/5.99      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 43.47/5.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_3,plain,
% 43.47/5.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 43.47/5.99      inference(cnf_transformation,[],[f29]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_417,plain,
% 43.47/5.99      ( r1_xboole_0(X0,X1) != iProver_top
% 43.47/5.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 43.47/5.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_10745,plain,
% 43.47/5.99      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_410,c_417]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_12590,plain,
% 43.47/5.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_10745,c_418]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_17728,plain,
% 43.47/5.99      ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_12590,c_6]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_17730,plain,
% 43.47/5.99      ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k4_xboole_0(sK1,sK3) ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_17728,c_5]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_27866,plain,
% 43.47/5.99      ( k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK1,sK3) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_17730,c_0]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_165266,plain,
% 43.47/5.99      ( k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) = sK1 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_27866,c_40318]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_166626,plain,
% 43.47/5.99      ( k2_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)))) = sK1 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_165266,c_7]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_166627,plain,
% 43.47/5.99      ( k2_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,k2_xboole_0(sK3,sK1))))) = sK1 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_166626,c_7]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_166628,plain,
% 43.47/5.99      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_166627,c_5,c_779,c_27866]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_176400,plain,
% 43.47/5.99      ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_166628,c_7]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_187585,plain,
% 43.47/5.99      ( k4_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK1,sK2) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_13064,c_176400]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_187842,plain,
% 43.47/5.99      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_187585,c_8]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_188520,plain,
% 43.47/5.99      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_187842,c_6]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_188551,plain,
% 43.47/5.99      ( k2_xboole_0(sK2,sK1) = sK2 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_188520,c_5]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_194782,plain,
% 43.47/5.99      ( k2_xboole_0(k1_xboole_0,sK1) = sK2 ),
% 43.47/5.99      inference(light_normalisation,[status(thm)],[c_194549,c_188551]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_635,plain,
% 43.47/5.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 43.47/5.99      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_194783,plain,
% 43.47/5.99      ( sK2 = sK1 ),
% 43.47/5.99      inference(demodulation,[status(thm)],[c_194782,c_635]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_151,plain,( X0 = X0 ),theory(equality) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_632,plain,
% 43.47/5.99      ( sK1 = sK1 ),
% 43.47/5.99      inference(instantiation,[status(thm)],[c_151]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_152,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_533,plain,
% 43.47/5.99      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 43.47/5.99      inference(instantiation,[status(thm)],[c_152]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_631,plain,
% 43.47/5.99      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 43.47/5.99      inference(instantiation,[status(thm)],[c_533]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(c_15,negated_conjecture,
% 43.47/5.99      ( sK1 != sK2 ),
% 43.47/5.99      inference(cnf_transformation,[],[f45]) ).
% 43.47/5.99  
% 43.47/5.99  cnf(contradiction,plain,
% 43.47/5.99      ( $false ),
% 43.47/5.99      inference(minisat,[status(thm)],[c_194783,c_632,c_631,c_15]) ).
% 43.47/5.99  
% 43.47/5.99  
% 43.47/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.47/5.99  
% 43.47/5.99  ------                               Statistics
% 43.47/5.99  
% 43.47/5.99  ------ Selected
% 43.47/5.99  
% 43.47/5.99  total_time:                             5.442
% 43.47/5.99  
%------------------------------------------------------------------------------
