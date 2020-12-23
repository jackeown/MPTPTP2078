%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:50 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 558 expanded)
%              Number of clauses        :   77 ( 221 expanded)
%              Number of leaves         :   16 ( 137 expanded)
%              Depth                    :   22
%              Number of atoms          :  169 ( 949 expanded)
%              Number of equality atoms :  127 ( 676 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f24])).

fof(f27,plain,
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

fof(f28,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27])).

fof(f46,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_278,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_19,c_10,c_0])).

cnf(c_591,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_23208,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_278,c_591])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_517,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_524,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15302,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_517,c_524])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17415,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_15302,c_7])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_281,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0])).

cnf(c_2340,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_281,c_7])).

cnf(c_17417,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_17415,c_6,c_2340])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19834,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_17417,c_8])).

cnf(c_26590,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK2,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_23208,c_19834])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_173,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k2_xboole_0(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_5])).

cnf(c_1019,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_173])).

cnf(c_6145,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1019])).

cnf(c_26593,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_6145,c_19834])).

cnf(c_26630,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_26593,c_19834])).

cnf(c_26639,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK2,sK0))) = k4_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_26590,c_26630])).

cnf(c_885,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_278,c_9])).

cnf(c_884,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_9])).

cnf(c_1360,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_884,c_7])).

cnf(c_1365,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1360,c_6])).

cnf(c_1198,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_278,c_10])).

cnf(c_1497,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1198,c_10])).

cnf(c_2641,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1365,c_1497])).

cnf(c_2652,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_2641,c_278])).

cnf(c_590,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_21122,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2652,c_590])).

cnf(c_21906,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1019,c_21122])).

cnf(c_22017,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_21906,c_2652])).

cnf(c_24432,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_23208,c_22017])).

cnf(c_26641,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_26639,c_885,c_24432])).

cnf(c_26965,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26641,c_7])).

cnf(c_26968,plain,
    ( k2_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_26965,c_6])).

cnf(c_882,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_2855,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_882,c_7])).

cnf(c_2860,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2855,c_6])).

cnf(c_12480,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2860])).

cnf(c_28320,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_26968,c_12480])).

cnf(c_15357,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_278,c_6145])).

cnf(c_2842,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_278,c_882])).

cnf(c_2893,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_2842,c_173])).

cnf(c_15541,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_15357,c_2893])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_518,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_523,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12451,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_518,c_523])).

cnf(c_15303,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12451,c_524])).

cnf(c_18154,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(superposition,[status(thm)],[c_15303,c_7])).

cnf(c_18156,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_18154,c_6,c_2340])).

cnf(c_20098,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_18156,c_8])).

cnf(c_26723,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_15541,c_20098])).

cnf(c_26793,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26723,c_9])).

cnf(c_26827,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26793,c_7])).

cnf(c_26829,plain,
    ( k2_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_26827,c_6])).

cnf(c_28380,plain,
    ( k2_xboole_0(sK1,sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_28320,c_26829])).

cnf(c_28381,plain,
    ( sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_28380,c_1365])).

cnf(c_283,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_729,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_284,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_634,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_728,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_16,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28381,c_729,c_728,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:02:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.72/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/1.48  
% 7.72/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.72/1.48  
% 7.72/1.48  ------  iProver source info
% 7.72/1.48  
% 7.72/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.72/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.72/1.48  git: non_committed_changes: false
% 7.72/1.48  git: last_make_outside_of_git: false
% 7.72/1.48  
% 7.72/1.48  ------ 
% 7.72/1.48  ------ Parsing...
% 7.72/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.72/1.48  
% 7.72/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.72/1.48  
% 7.72/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.72/1.48  
% 7.72/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.48  ------ Proving...
% 7.72/1.48  ------ Problem Properties 
% 7.72/1.48  
% 7.72/1.48  
% 7.72/1.48  clauses                                 19
% 7.72/1.48  conjectures                             4
% 7.72/1.48  EPR                                     4
% 7.72/1.48  Horn                                    19
% 7.72/1.48  unary                                   11
% 7.72/1.48  binary                                  6
% 7.72/1.48  lits                                    30
% 7.72/1.48  lits eq                                 15
% 7.72/1.48  fd_pure                                 0
% 7.72/1.48  fd_pseudo                               0
% 7.72/1.48  fd_cond                                 0
% 7.72/1.48  fd_pseudo_cond                          1
% 7.72/1.48  AC symbols                              1
% 7.72/1.48  
% 7.72/1.48  ------ Input Options Time Limit: Unbounded
% 7.72/1.48  
% 7.72/1.48  
% 7.72/1.48  ------ 
% 7.72/1.48  Current options:
% 7.72/1.48  ------ 
% 7.72/1.48  
% 7.72/1.48  
% 7.72/1.48  
% 7.72/1.48  
% 7.72/1.48  ------ Proving...
% 7.72/1.48  
% 7.72/1.48  
% 7.72/1.48  % SZS status Theorem for theBenchmark.p
% 7.72/1.48  
% 7.72/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.72/1.48  
% 7.72/1.48  fof(f15,conjecture,(
% 7.72/1.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f16,negated_conjecture,(
% 7.72/1.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 7.72/1.48    inference(negated_conjecture,[],[f15])).
% 7.72/1.48  
% 7.72/1.48  fof(f24,plain,(
% 7.72/1.48    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 7.72/1.48    inference(ennf_transformation,[],[f16])).
% 7.72/1.48  
% 7.72/1.48  fof(f25,plain,(
% 7.72/1.48    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 7.72/1.48    inference(flattening,[],[f24])).
% 7.72/1.48  
% 7.72/1.48  fof(f27,plain,(
% 7.72/1.48    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 7.72/1.48    introduced(choice_axiom,[])).
% 7.72/1.48  
% 7.72/1.48  fof(f28,plain,(
% 7.72/1.48    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 7.72/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27])).
% 7.72/1.48  
% 7.72/1.48  fof(f46,plain,(
% 7.72/1.48    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 7.72/1.48    inference(cnf_transformation,[],[f28])).
% 7.72/1.48  
% 7.72/1.48  fof(f11,axiom,(
% 7.72/1.48    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f40,plain,(
% 7.72/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.72/1.48    inference(cnf_transformation,[],[f11])).
% 7.72/1.48  
% 7.72/1.48  fof(f1,axiom,(
% 7.72/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f29,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.72/1.48    inference(cnf_transformation,[],[f1])).
% 7.72/1.48  
% 7.72/1.48  fof(f47,plain,(
% 7.72/1.48    r1_xboole_0(sK2,sK0)),
% 7.72/1.48    inference(cnf_transformation,[],[f28])).
% 7.72/1.48  
% 7.72/1.48  fof(f2,axiom,(
% 7.72/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f26,plain,(
% 7.72/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.72/1.48    inference(nnf_transformation,[],[f2])).
% 7.72/1.48  
% 7.72/1.48  fof(f30,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.72/1.48    inference(cnf_transformation,[],[f26])).
% 7.72/1.48  
% 7.72/1.48  fof(f10,axiom,(
% 7.72/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f39,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.72/1.48    inference(cnf_transformation,[],[f10])).
% 7.72/1.48  
% 7.72/1.48  fof(f51,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.72/1.48    inference(definition_unfolding,[],[f30,f39])).
% 7.72/1.48  
% 7.72/1.48  fof(f7,axiom,(
% 7.72/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f36,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.72/1.48    inference(cnf_transformation,[],[f7])).
% 7.72/1.48  
% 7.72/1.48  fof(f6,axiom,(
% 7.72/1.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f35,plain,(
% 7.72/1.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.72/1.48    inference(cnf_transformation,[],[f6])).
% 7.72/1.48  
% 7.72/1.48  fof(f12,axiom,(
% 7.72/1.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f41,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.72/1.48    inference(cnf_transformation,[],[f12])).
% 7.72/1.48  
% 7.72/1.48  fof(f52,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.72/1.48    inference(definition_unfolding,[],[f41,f39])).
% 7.72/1.48  
% 7.72/1.48  fof(f8,axiom,(
% 7.72/1.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f37,plain,(
% 7.72/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.72/1.48    inference(cnf_transformation,[],[f8])).
% 7.72/1.48  
% 7.72/1.48  fof(f9,axiom,(
% 7.72/1.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f38,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.72/1.48    inference(cnf_transformation,[],[f9])).
% 7.72/1.48  
% 7.72/1.48  fof(f4,axiom,(
% 7.72/1.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f17,plain,(
% 7.72/1.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) => r1_tarski(X0,X1))),
% 7.72/1.48    inference(unused_predicate_definition_removal,[],[f4])).
% 7.72/1.48  
% 7.72/1.48  fof(f19,plain,(
% 7.72/1.48    ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 7.72/1.48    inference(ennf_transformation,[],[f17])).
% 7.72/1.48  
% 7.72/1.48  fof(f33,plain,(
% 7.72/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.72/1.48    inference(cnf_transformation,[],[f19])).
% 7.72/1.48  
% 7.72/1.48  fof(f5,axiom,(
% 7.72/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f20,plain,(
% 7.72/1.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.72/1.48    inference(ennf_transformation,[],[f5])).
% 7.72/1.48  
% 7.72/1.48  fof(f34,plain,(
% 7.72/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.72/1.48    inference(cnf_transformation,[],[f20])).
% 7.72/1.48  
% 7.72/1.48  fof(f48,plain,(
% 7.72/1.48    r1_xboole_0(sK3,sK1)),
% 7.72/1.48    inference(cnf_transformation,[],[f28])).
% 7.72/1.48  
% 7.72/1.48  fof(f3,axiom,(
% 7.72/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.48  
% 7.72/1.48  fof(f18,plain,(
% 7.72/1.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.72/1.48    inference(ennf_transformation,[],[f3])).
% 7.72/1.48  
% 7.72/1.48  fof(f32,plain,(
% 7.72/1.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.72/1.48    inference(cnf_transformation,[],[f18])).
% 7.72/1.48  
% 7.72/1.48  fof(f49,plain,(
% 7.72/1.48    sK1 != sK2),
% 7.72/1.48    inference(cnf_transformation,[],[f28])).
% 7.72/1.48  
% 7.72/1.48  cnf(c_19,negated_conjecture,
% 7.72/1.48      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 7.72/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_10,plain,
% 7.72/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.72/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_0,plain,
% 7.72/1.48      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.72/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_278,negated_conjecture,
% 7.72/1.48      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 7.72/1.48      inference(theory_normalisation,[status(thm)],[c_19,c_10,c_0]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_591,plain,
% 7.72/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_23208,plain,
% 7.72/1.48      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_278,c_591]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_18,negated_conjecture,
% 7.72/1.48      ( r1_xboole_0(sK2,sK0) ),
% 7.72/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_517,plain,
% 7.72/1.48      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 7.72/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_2,plain,
% 7.72/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.72/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.72/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_524,plain,
% 7.72/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.72/1.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.72/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_15302,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_517,c_524]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_7,plain,
% 7.72/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.72/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_17415,plain,
% 7.72/1.48      ( k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_15302,c_7]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_6,plain,
% 7.72/1.48      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.72/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_11,plain,
% 7.72/1.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.72/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_281,plain,
% 7.72/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.72/1.48      inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_2340,plain,
% 7.72/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_281,c_7]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_17417,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 7.72/1.48      inference(demodulation,[status(thm)],[c_17415,c_6,c_2340]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_8,plain,
% 7.72/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.72/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_19834,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_17417,c_8]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26590,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK2,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_23208,c_19834]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_9,plain,
% 7.72/1.48      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.72/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_4,plain,
% 7.72/1.48      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.72/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_5,plain,
% 7.72/1.48      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.72/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_173,plain,
% 7.72/1.48      ( k4_xboole_0(X0,X1) != k1_xboole_0 | k2_xboole_0(X0,X1) = X1 ),
% 7.72/1.48      inference(resolution,[status(thm)],[c_4,c_5]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_1019,plain,
% 7.72/1.48      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_9,c_173]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_6145,plain,
% 7.72/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_0,c_1019]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26593,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_6145,c_19834]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26630,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,X0) ),
% 7.72/1.48      inference(light_normalisation,[status(thm)],[c_26593,c_19834]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26639,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK2,sK0))) = k4_xboole_0(sK2,sK1) ),
% 7.72/1.48      inference(demodulation,[status(thm)],[c_26590,c_26630]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_885,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_278,c_9]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_884,plain,
% 7.72/1.48      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_6,c_9]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_1360,plain,
% 7.72/1.48      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_884,c_7]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_1365,plain,
% 7.72/1.48      ( k2_xboole_0(X0,X0) = X0 ),
% 7.72/1.48      inference(light_normalisation,[status(thm)],[c_1360,c_6]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_1198,plain,
% 7.72/1.48      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_278,c_10]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_1497,plain,
% 7.72/1.48      ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_1198,c_10]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_2641,plain,
% 7.72/1.48      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK2,sK3) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_1365,c_1497]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_2652,plain,
% 7.72/1.48      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
% 7.72/1.48      inference(light_normalisation,[status(thm)],[c_2641,c_278]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_590,plain,
% 7.72/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_21122,plain,
% 7.72/1.48      ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_2652,c_590]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_21906,plain,
% 7.72/1.48      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_1019,c_21122]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_22017,plain,
% 7.72/1.48      ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 7.72/1.48      inference(light_normalisation,[status(thm)],[c_21906,c_2652]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_24432,plain,
% 7.72/1.48      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,sK0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_23208,c_22017]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26641,plain,
% 7.72/1.48      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 7.72/1.48      inference(light_normalisation,
% 7.72/1.48                [status(thm)],
% 7.72/1.48                [c_26639,c_885,c_24432]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26965,plain,
% 7.72/1.48      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_26641,c_7]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26968,plain,
% 7.72/1.48      ( k2_xboole_0(sK1,sK2) = sK1 ),
% 7.72/1.48      inference(demodulation,[status(thm)],[c_26965,c_6]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_882,plain,
% 7.72/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_2855,plain,
% 7.72/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_882,c_7]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_2860,plain,
% 7.72/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.72/1.48      inference(demodulation,[status(thm)],[c_2855,c_6]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_12480,plain,
% 7.72/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_0,c_2860]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_28320,plain,
% 7.72/1.48      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK1) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_26968,c_12480]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_15357,plain,
% 7.72/1.48      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,sK2) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_278,c_6145]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_2842,plain,
% 7.72/1.48      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_278,c_882]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_2893,plain,
% 7.72/1.48      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_2842,c_173]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_15541,plain,
% 7.72/1.48      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
% 7.72/1.48      inference(light_normalisation,[status(thm)],[c_15357,c_2893]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_17,negated_conjecture,
% 7.72/1.48      ( r1_xboole_0(sK3,sK1) ),
% 7.72/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_518,plain,
% 7.72/1.48      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 7.72/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_3,plain,
% 7.72/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.72/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_523,plain,
% 7.72/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 7.72/1.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.72/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_12451,plain,
% 7.72/1.48      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_518,c_523]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_15303,plain,
% 7.72/1.48      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_12451,c_524]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_18154,plain,
% 7.72/1.48      ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_15303,c_7]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_18156,plain,
% 7.72/1.48      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 7.72/1.48      inference(demodulation,[status(thm)],[c_18154,c_6,c_2340]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_20098,plain,
% 7.72/1.48      ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_18156,c_8]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26723,plain,
% 7.72/1.48      ( k4_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK1,sK2) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_15541,c_20098]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26793,plain,
% 7.72/1.48      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 7.72/1.48      inference(demodulation,[status(thm)],[c_26723,c_9]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26827,plain,
% 7.72/1.48      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
% 7.72/1.48      inference(superposition,[status(thm)],[c_26793,c_7]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_26829,plain,
% 7.72/1.48      ( k2_xboole_0(sK2,sK1) = sK2 ),
% 7.72/1.48      inference(demodulation,[status(thm)],[c_26827,c_6]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_28380,plain,
% 7.72/1.48      ( k2_xboole_0(sK1,sK1) = sK2 ),
% 7.72/1.48      inference(light_normalisation,[status(thm)],[c_28320,c_26829]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_28381,plain,
% 7.72/1.48      ( sK2 = sK1 ),
% 7.72/1.48      inference(demodulation,[status(thm)],[c_28380,c_1365]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_283,plain,( X0 = X0 ),theory(equality) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_729,plain,
% 7.72/1.48      ( sK1 = sK1 ),
% 7.72/1.48      inference(instantiation,[status(thm)],[c_283]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_284,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_634,plain,
% 7.72/1.48      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 7.72/1.48      inference(instantiation,[status(thm)],[c_284]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_728,plain,
% 7.72/1.48      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 7.72/1.48      inference(instantiation,[status(thm)],[c_634]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(c_16,negated_conjecture,
% 7.72/1.48      ( sK1 != sK2 ),
% 7.72/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.72/1.48  
% 7.72/1.48  cnf(contradiction,plain,
% 7.72/1.48      ( $false ),
% 7.72/1.48      inference(minisat,[status(thm)],[c_28381,c_729,c_728,c_16]) ).
% 7.72/1.48  
% 7.72/1.48  
% 7.72/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.72/1.48  
% 7.72/1.48  ------                               Statistics
% 7.72/1.48  
% 7.72/1.48  ------ Selected
% 7.72/1.48  
% 7.72/1.48  total_time:                             0.736
% 7.72/1.48  
%------------------------------------------------------------------------------
