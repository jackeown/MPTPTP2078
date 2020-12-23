%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:54 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  179 (5375 expanded)
%              Number of clauses        :  146 (2293 expanded)
%              Number of leaves         :   11 (1336 expanded)
%              Depth                    :   27
%              Number of atoms          :  218 (7300 expanded)
%              Number of equality atoms :  172 (5145 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f27,f27])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f30,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_63,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_128,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | k2_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_63,c_11])).

cnf(c_129,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_176,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_117,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) = k1_xboole_0
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_63,c_8])).

cnf(c_118,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_117])).

cnf(c_274,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_118])).

cnf(c_377,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_176,c_5,c_274])).

cnf(c_387,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_7,c_377])).

cnf(c_12525,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_129,c_387])).

cnf(c_13563,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_12525,c_5])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_110,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_111,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_110])).

cnf(c_180,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_633,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_111,c_180])).

cnf(c_171,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_172,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_171,c_5])).

cnf(c_198,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_172])).

cnf(c_277,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_198,c_118])).

cnf(c_681,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_633,c_277])).

cnf(c_169,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_305,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_169,c_1])).

cnf(c_309,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_305,c_5,c_118])).

cnf(c_911,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X0),sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK0),X0) ),
    inference(superposition,[status(thm)],[c_681,c_309])).

cnf(c_1634,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),X0) ),
    inference(superposition,[status(thm)],[c_911,c_5])).

cnf(c_906,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_172,c_681])).

cnf(c_926,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_906,c_377])).

cnf(c_3446,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_926,c_5])).

cnf(c_3719,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3446,c_309])).

cnf(c_191,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_194,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_191,c_7])).

cnf(c_190,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_1943,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_194,c_190])).

cnf(c_3738,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) = sK2 ),
    inference(demodulation,[status(thm)],[c_3719,c_7,c_1943])).

cnf(c_3739,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_3738,c_172,c_274])).

cnf(c_4066,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),sK2) = k2_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_1634,c_1634,c_3739])).

cnf(c_4070,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),sK2) = k2_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4066])).

cnf(c_13609,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_13563,c_4070])).

cnf(c_3744,plain,
    ( k2_xboole_0(sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_3739,c_3446])).

cnf(c_13615,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_13609,c_3744])).

cnf(c_441,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_309])).

cnf(c_18307,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_13615,c_441])).

cnf(c_3722,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_3446,c_6])).

cnf(c_3894,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3722,c_906,c_3739])).

cnf(c_445,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK2),sK0),k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_129,c_309])).

cnf(c_526,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_445,c_5])).

cnf(c_187,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_7,c_7])).

cnf(c_195,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_187,c_7])).

cnf(c_2541,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK0))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_526,c_195])).

cnf(c_2810,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2541,c_274])).

cnf(c_2948,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2810])).

cnf(c_3117,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK2)),X0)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_2948,c_180])).

cnf(c_2960,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK0)),X0)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK0),k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_2810,c_180])).

cnf(c_183,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_196,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_183,c_7])).

cnf(c_2977,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)),X0)) = k4_xboole_0(k2_xboole_0(sK2,sK0),X0) ),
    inference(demodulation,[status(thm)],[c_2960,c_7,c_196,c_198])).

cnf(c_3035,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_196])).

cnf(c_3130,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK2),X0) = k4_xboole_0(k2_xboole_0(sK2,sK0),X0) ),
    inference(demodulation,[status(thm)],[c_3117,c_7,c_198,c_2977,c_3035])).

cnf(c_13600,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_13563,c_190])).

cnf(c_18005,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK2),sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_3130,c_13600])).

cnf(c_5710,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_3130,c_377])).

cnf(c_5765,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK2),sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_5710,c_3739])).

cnf(c_18073,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK0,sK1)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK0,sK1)),sK0) ),
    inference(light_normalisation,[status(thm)],[c_18005,c_5765])).

cnf(c_185,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_111,c_7])).

cnf(c_448,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),X0),sK0),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k4_xboole_0(sK0,sK2),X0) ),
    inference(superposition,[status(thm)],[c_185,c_309])).

cnf(c_480,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),X0),sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_448,c_277])).

cnf(c_388,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_111,c_377])).

cnf(c_498,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_388,c_5])).

cnf(c_528,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_498,c_309])).

cnf(c_541,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))) = sK0 ),
    inference(demodulation,[status(thm)],[c_528,c_7])).

cnf(c_542,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_541,c_172,c_274])).

cnf(c_1567,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),sK0),k1_xboole_0) = k2_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_480,c_480,c_542])).

cnf(c_1592,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,X0),sK0) = k2_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_1567,c_5])).

cnf(c_2188,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK0),sK0) = k2_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1592])).

cnf(c_2651,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK0,sK0))) = k4_xboole_0(X0,k2_xboole_0(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_2188,c_195])).

cnf(c_545,plain,
    ( k2_xboole_0(sK0,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_542,c_498])).

cnf(c_2658,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,sK0)) = k4_xboole_0(X0,k2_xboole_0(sK0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2651,c_545])).

cnf(c_5731,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(X0,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_3130,c_2658])).

cnf(c_3034,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(sK0,X1)) = k4_xboole_0(k2_xboole_0(sK0,X0),k2_xboole_0(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_2188,c_196])).

cnf(c_3102,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,X0),k2_xboole_0(sK0,X1)) = k4_xboole_0(X0,k2_xboole_0(sK0,X1)) ),
    inference(demodulation,[status(thm)],[c_3034,c_196])).

cnf(c_5743,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_5731,c_3102,c_3130])).

cnf(c_465,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_309,c_7])).

cnf(c_15035,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_194,c_465])).

cnf(c_15036,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0),k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_190,c_465])).

cnf(c_15367,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0)))),X3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_15036,c_7,c_1943])).

cnf(c_15368,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_15035,c_15367])).

cnf(c_13599,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X0,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_13563,c_194])).

cnf(c_17845,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X0,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_169,c_13599])).

cnf(c_15017,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_465])).

cnf(c_17979,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_17845,c_15017])).

cnf(c_18074,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_18073,c_5743,c_15368,c_17979])).

cnf(c_1067,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_274,c_190])).

cnf(c_1239,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1067,c_7,c_172])).

cnf(c_4224,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_1239])).

cnf(c_6657,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_377,c_4224])).

cnf(c_1076,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_172,c_190])).

cnf(c_1229,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1076,c_7,c_277])).

cnf(c_6870,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6657,c_6,c_1229])).

cnf(c_6995,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_6870])).

cnf(c_12553,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_6995,c_387])).

cnf(c_186,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_129,c_7])).

cnf(c_217,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_186])).

cnf(c_2578,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_195,c_217])).

cnf(c_236,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_217,c_7])).

cnf(c_238,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_236,c_7,c_195])).

cnf(c_352,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_238,c_277])).

cnf(c_358,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_352])).

cnf(c_2597,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2578,c_358])).

cnf(c_386,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_6,c_377])).

cnf(c_3254,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2597,c_386])).

cnf(c_460,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_274,c_309])).

cnf(c_3329,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3254,c_5,c_198,c_460])).

cnf(c_5806,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3329])).

cnf(c_8343,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_5806,c_386])).

cnf(c_3065,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_196,c_169])).

cnf(c_3082,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3065,c_118])).

cnf(c_8405,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_8343,c_5,c_3082])).

cnf(c_8353,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5806,c_441])).

cnf(c_8400,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8353,c_3082])).

cnf(c_8406,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_8405,c_8400])).

cnf(c_12754,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_12553,c_7,c_8406])).

cnf(c_5809,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_198,c_3329])).

cnf(c_5877,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5809,c_198])).

cnf(c_12755,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_12754,c_5877])).

cnf(c_15211,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_465,c_3130])).

cnf(c_5714,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_3130,c_196])).

cnf(c_15216,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_15211,c_542,c_5714])).

cnf(c_18075,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_18074,c_3739,c_12755,c_15216])).

cnf(c_18337,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18307,c_3894,c_13563,c_18075])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_61,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_123,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_61,c_9])).

cnf(c_124,plain,
    ( k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_123])).

cnf(c_18376,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18337,c_124])).

cnf(c_18377,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_18376])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:52:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.47/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/1.51  
% 7.47/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.47/1.51  
% 7.47/1.51  ------  iProver source info
% 7.47/1.51  
% 7.47/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.47/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.47/1.51  git: non_committed_changes: false
% 7.47/1.51  git: last_make_outside_of_git: false
% 7.47/1.51  
% 7.47/1.51  ------ 
% 7.47/1.51  
% 7.47/1.51  ------ Input Options
% 7.47/1.51  
% 7.47/1.51  --out_options                           all
% 7.47/1.51  --tptp_safe_out                         true
% 7.47/1.51  --problem_path                          ""
% 7.47/1.51  --include_path                          ""
% 7.47/1.51  --clausifier                            res/vclausify_rel
% 7.47/1.51  --clausifier_options                    --mode clausify
% 7.47/1.51  --stdin                                 false
% 7.47/1.51  --stats_out                             all
% 7.47/1.51  
% 7.47/1.51  ------ General Options
% 7.47/1.51  
% 7.47/1.51  --fof                                   false
% 7.47/1.51  --time_out_real                         305.
% 7.47/1.51  --time_out_virtual                      -1.
% 7.47/1.51  --symbol_type_check                     false
% 7.47/1.51  --clausify_out                          false
% 7.47/1.51  --sig_cnt_out                           false
% 7.47/1.51  --trig_cnt_out                          false
% 7.47/1.51  --trig_cnt_out_tolerance                1.
% 7.47/1.51  --trig_cnt_out_sk_spl                   false
% 7.47/1.51  --abstr_cl_out                          false
% 7.47/1.51  
% 7.47/1.51  ------ Global Options
% 7.47/1.51  
% 7.47/1.51  --schedule                              default
% 7.47/1.51  --add_important_lit                     false
% 7.47/1.51  --prop_solver_per_cl                    1000
% 7.47/1.51  --min_unsat_core                        false
% 7.47/1.51  --soft_assumptions                      false
% 7.47/1.51  --soft_lemma_size                       3
% 7.47/1.51  --prop_impl_unit_size                   0
% 7.47/1.51  --prop_impl_unit                        []
% 7.47/1.51  --share_sel_clauses                     true
% 7.47/1.51  --reset_solvers                         false
% 7.47/1.51  --bc_imp_inh                            [conj_cone]
% 7.47/1.51  --conj_cone_tolerance                   3.
% 7.47/1.51  --extra_neg_conj                        none
% 7.47/1.51  --large_theory_mode                     true
% 7.47/1.51  --prolific_symb_bound                   200
% 7.47/1.51  --lt_threshold                          2000
% 7.47/1.51  --clause_weak_htbl                      true
% 7.47/1.51  --gc_record_bc_elim                     false
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing Options
% 7.47/1.51  
% 7.47/1.51  --preprocessing_flag                    true
% 7.47/1.51  --time_out_prep_mult                    0.1
% 7.47/1.51  --splitting_mode                        input
% 7.47/1.51  --splitting_grd                         true
% 7.47/1.51  --splitting_cvd                         false
% 7.47/1.51  --splitting_cvd_svl                     false
% 7.47/1.51  --splitting_nvd                         32
% 7.47/1.51  --sub_typing                            true
% 7.47/1.51  --prep_gs_sim                           true
% 7.47/1.51  --prep_unflatten                        true
% 7.47/1.51  --prep_res_sim                          true
% 7.47/1.51  --prep_upred                            true
% 7.47/1.51  --prep_sem_filter                       exhaustive
% 7.47/1.51  --prep_sem_filter_out                   false
% 7.47/1.51  --pred_elim                             true
% 7.47/1.51  --res_sim_input                         true
% 7.47/1.51  --eq_ax_congr_red                       true
% 7.47/1.51  --pure_diseq_elim                       true
% 7.47/1.51  --brand_transform                       false
% 7.47/1.51  --non_eq_to_eq                          false
% 7.47/1.51  --prep_def_merge                        true
% 7.47/1.51  --prep_def_merge_prop_impl              false
% 7.47/1.51  --prep_def_merge_mbd                    true
% 7.47/1.51  --prep_def_merge_tr_red                 false
% 7.47/1.51  --prep_def_merge_tr_cl                  false
% 7.47/1.51  --smt_preprocessing                     true
% 7.47/1.51  --smt_ac_axioms                         fast
% 7.47/1.51  --preprocessed_out                      false
% 7.47/1.51  --preprocessed_stats                    false
% 7.47/1.51  
% 7.47/1.51  ------ Abstraction refinement Options
% 7.47/1.51  
% 7.47/1.51  --abstr_ref                             []
% 7.47/1.51  --abstr_ref_prep                        false
% 7.47/1.51  --abstr_ref_until_sat                   false
% 7.47/1.51  --abstr_ref_sig_restrict                funpre
% 7.47/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.51  --abstr_ref_under                       []
% 7.47/1.51  
% 7.47/1.51  ------ SAT Options
% 7.47/1.51  
% 7.47/1.51  --sat_mode                              false
% 7.47/1.51  --sat_fm_restart_options                ""
% 7.47/1.51  --sat_gr_def                            false
% 7.47/1.51  --sat_epr_types                         true
% 7.47/1.51  --sat_non_cyclic_types                  false
% 7.47/1.51  --sat_finite_models                     false
% 7.47/1.51  --sat_fm_lemmas                         false
% 7.47/1.51  --sat_fm_prep                           false
% 7.47/1.51  --sat_fm_uc_incr                        true
% 7.47/1.51  --sat_out_model                         small
% 7.47/1.51  --sat_out_clauses                       false
% 7.47/1.51  
% 7.47/1.51  ------ QBF Options
% 7.47/1.51  
% 7.47/1.51  --qbf_mode                              false
% 7.47/1.51  --qbf_elim_univ                         false
% 7.47/1.51  --qbf_dom_inst                          none
% 7.47/1.51  --qbf_dom_pre_inst                      false
% 7.47/1.51  --qbf_sk_in                             false
% 7.47/1.51  --qbf_pred_elim                         true
% 7.47/1.51  --qbf_split                             512
% 7.47/1.51  
% 7.47/1.51  ------ BMC1 Options
% 7.47/1.51  
% 7.47/1.51  --bmc1_incremental                      false
% 7.47/1.51  --bmc1_axioms                           reachable_all
% 7.47/1.51  --bmc1_min_bound                        0
% 7.47/1.51  --bmc1_max_bound                        -1
% 7.47/1.51  --bmc1_max_bound_default                -1
% 7.47/1.51  --bmc1_symbol_reachability              true
% 7.47/1.51  --bmc1_property_lemmas                  false
% 7.47/1.51  --bmc1_k_induction                      false
% 7.47/1.51  --bmc1_non_equiv_states                 false
% 7.47/1.51  --bmc1_deadlock                         false
% 7.47/1.51  --bmc1_ucm                              false
% 7.47/1.51  --bmc1_add_unsat_core                   none
% 7.47/1.51  --bmc1_unsat_core_children              false
% 7.47/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.51  --bmc1_out_stat                         full
% 7.47/1.51  --bmc1_ground_init                      false
% 7.47/1.51  --bmc1_pre_inst_next_state              false
% 7.47/1.51  --bmc1_pre_inst_state                   false
% 7.47/1.51  --bmc1_pre_inst_reach_state             false
% 7.47/1.51  --bmc1_out_unsat_core                   false
% 7.47/1.51  --bmc1_aig_witness_out                  false
% 7.47/1.51  --bmc1_verbose                          false
% 7.47/1.51  --bmc1_dump_clauses_tptp                false
% 7.47/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.51  --bmc1_dump_file                        -
% 7.47/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.51  --bmc1_ucm_extend_mode                  1
% 7.47/1.51  --bmc1_ucm_init_mode                    2
% 7.47/1.51  --bmc1_ucm_cone_mode                    none
% 7.47/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.51  --bmc1_ucm_relax_model                  4
% 7.47/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.51  --bmc1_ucm_layered_model                none
% 7.47/1.51  --bmc1_ucm_max_lemma_size               10
% 7.47/1.51  
% 7.47/1.51  ------ AIG Options
% 7.47/1.51  
% 7.47/1.51  --aig_mode                              false
% 7.47/1.51  
% 7.47/1.51  ------ Instantiation Options
% 7.47/1.51  
% 7.47/1.51  --instantiation_flag                    true
% 7.47/1.51  --inst_sos_flag                         false
% 7.47/1.51  --inst_sos_phase                        true
% 7.47/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel_side                     num_symb
% 7.47/1.51  --inst_solver_per_active                1400
% 7.47/1.51  --inst_solver_calls_frac                1.
% 7.47/1.51  --inst_passive_queue_type               priority_queues
% 7.47/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.51  --inst_passive_queues_freq              [25;2]
% 7.47/1.51  --inst_dismatching                      true
% 7.47/1.51  --inst_eager_unprocessed_to_passive     true
% 7.47/1.51  --inst_prop_sim_given                   true
% 7.47/1.51  --inst_prop_sim_new                     false
% 7.47/1.51  --inst_subs_new                         false
% 7.47/1.51  --inst_eq_res_simp                      false
% 7.47/1.51  --inst_subs_given                       false
% 7.47/1.51  --inst_orphan_elimination               true
% 7.47/1.51  --inst_learning_loop_flag               true
% 7.47/1.51  --inst_learning_start                   3000
% 7.47/1.51  --inst_learning_factor                  2
% 7.47/1.51  --inst_start_prop_sim_after_learn       3
% 7.47/1.51  --inst_sel_renew                        solver
% 7.47/1.51  --inst_lit_activity_flag                true
% 7.47/1.51  --inst_restr_to_given                   false
% 7.47/1.51  --inst_activity_threshold               500
% 7.47/1.51  --inst_out_proof                        true
% 7.47/1.51  
% 7.47/1.51  ------ Resolution Options
% 7.47/1.51  
% 7.47/1.51  --resolution_flag                       true
% 7.47/1.51  --res_lit_sel                           adaptive
% 7.47/1.51  --res_lit_sel_side                      none
% 7.47/1.51  --res_ordering                          kbo
% 7.47/1.51  --res_to_prop_solver                    active
% 7.47/1.51  --res_prop_simpl_new                    false
% 7.47/1.51  --res_prop_simpl_given                  true
% 7.47/1.51  --res_passive_queue_type                priority_queues
% 7.47/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.51  --res_passive_queues_freq               [15;5]
% 7.47/1.51  --res_forward_subs                      full
% 7.47/1.51  --res_backward_subs                     full
% 7.47/1.51  --res_forward_subs_resolution           true
% 7.47/1.51  --res_backward_subs_resolution          true
% 7.47/1.51  --res_orphan_elimination                true
% 7.47/1.51  --res_time_limit                        2.
% 7.47/1.51  --res_out_proof                         true
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Options
% 7.47/1.51  
% 7.47/1.51  --superposition_flag                    true
% 7.47/1.51  --sup_passive_queue_type                priority_queues
% 7.47/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.51  --demod_completeness_check              fast
% 7.47/1.51  --demod_use_ground                      true
% 7.47/1.51  --sup_to_prop_solver                    passive
% 7.47/1.51  --sup_prop_simpl_new                    true
% 7.47/1.51  --sup_prop_simpl_given                  true
% 7.47/1.51  --sup_fun_splitting                     false
% 7.47/1.51  --sup_smt_interval                      50000
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Simplification Setup
% 7.47/1.51  
% 7.47/1.51  --sup_indices_passive                   []
% 7.47/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.51  --sup_full_bw                           [BwDemod]
% 7.47/1.51  --sup_immed_triv                        [TrivRules]
% 7.47/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.51  --sup_immed_bw_main                     []
% 7.47/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.51  
% 7.47/1.51  ------ Combination Options
% 7.47/1.51  
% 7.47/1.51  --comb_res_mult                         3
% 7.47/1.51  --comb_sup_mult                         2
% 7.47/1.51  --comb_inst_mult                        10
% 7.47/1.51  
% 7.47/1.51  ------ Debug Options
% 7.47/1.51  
% 7.47/1.51  --dbg_backtrace                         false
% 7.47/1.51  --dbg_dump_prop_clauses                 false
% 7.47/1.51  --dbg_dump_prop_clauses_file            -
% 7.47/1.51  --dbg_out_stat                          false
% 7.47/1.51  ------ Parsing...
% 7.47/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.51  ------ Proving...
% 7.47/1.51  ------ Problem Properties 
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  clauses                                 11
% 7.47/1.51  conjectures                             0
% 7.47/1.51  EPR                                     0
% 7.47/1.51  Horn                                    11
% 7.47/1.51  unary                                   11
% 7.47/1.51  binary                                  0
% 7.47/1.51  lits                                    11
% 7.47/1.51  lits eq                                 11
% 7.47/1.51  fd_pure                                 0
% 7.47/1.51  fd_pseudo                               0
% 7.47/1.51  fd_cond                                 0
% 7.47/1.51  fd_pseudo_cond                          0
% 7.47/1.51  AC symbols                              0
% 7.47/1.51  
% 7.47/1.51  ------ Schedule UEQ
% 7.47/1.51  
% 7.47/1.51  ------ pure equality problem: resolution off 
% 7.47/1.51  
% 7.47/1.51  ------ Option_UEQ Time Limit: Unbounded
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  ------ 
% 7.47/1.51  Current options:
% 7.47/1.51  ------ 
% 7.47/1.51  
% 7.47/1.51  ------ Input Options
% 7.47/1.51  
% 7.47/1.51  --out_options                           all
% 7.47/1.51  --tptp_safe_out                         true
% 7.47/1.51  --problem_path                          ""
% 7.47/1.51  --include_path                          ""
% 7.47/1.51  --clausifier                            res/vclausify_rel
% 7.47/1.51  --clausifier_options                    --mode clausify
% 7.47/1.51  --stdin                                 false
% 7.47/1.51  --stats_out                             all
% 7.47/1.51  
% 7.47/1.51  ------ General Options
% 7.47/1.51  
% 7.47/1.51  --fof                                   false
% 7.47/1.51  --time_out_real                         305.
% 7.47/1.51  --time_out_virtual                      -1.
% 7.47/1.51  --symbol_type_check                     false
% 7.47/1.51  --clausify_out                          false
% 7.47/1.51  --sig_cnt_out                           false
% 7.47/1.51  --trig_cnt_out                          false
% 7.47/1.51  --trig_cnt_out_tolerance                1.
% 7.47/1.51  --trig_cnt_out_sk_spl                   false
% 7.47/1.51  --abstr_cl_out                          false
% 7.47/1.51  
% 7.47/1.51  ------ Global Options
% 7.47/1.51  
% 7.47/1.51  --schedule                              default
% 7.47/1.51  --add_important_lit                     false
% 7.47/1.51  --prop_solver_per_cl                    1000
% 7.47/1.51  --min_unsat_core                        false
% 7.47/1.51  --soft_assumptions                      false
% 7.47/1.51  --soft_lemma_size                       3
% 7.47/1.51  --prop_impl_unit_size                   0
% 7.47/1.51  --prop_impl_unit                        []
% 7.47/1.51  --share_sel_clauses                     true
% 7.47/1.51  --reset_solvers                         false
% 7.47/1.51  --bc_imp_inh                            [conj_cone]
% 7.47/1.51  --conj_cone_tolerance                   3.
% 7.47/1.51  --extra_neg_conj                        none
% 7.47/1.51  --large_theory_mode                     true
% 7.47/1.51  --prolific_symb_bound                   200
% 7.47/1.51  --lt_threshold                          2000
% 7.47/1.51  --clause_weak_htbl                      true
% 7.47/1.51  --gc_record_bc_elim                     false
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing Options
% 7.47/1.51  
% 7.47/1.51  --preprocessing_flag                    true
% 7.47/1.51  --time_out_prep_mult                    0.1
% 7.47/1.51  --splitting_mode                        input
% 7.47/1.51  --splitting_grd                         true
% 7.47/1.51  --splitting_cvd                         false
% 7.47/1.51  --splitting_cvd_svl                     false
% 7.47/1.51  --splitting_nvd                         32
% 7.47/1.51  --sub_typing                            true
% 7.47/1.51  --prep_gs_sim                           true
% 7.47/1.51  --prep_unflatten                        true
% 7.47/1.51  --prep_res_sim                          true
% 7.47/1.51  --prep_upred                            true
% 7.47/1.51  --prep_sem_filter                       exhaustive
% 7.47/1.51  --prep_sem_filter_out                   false
% 7.47/1.51  --pred_elim                             true
% 7.47/1.51  --res_sim_input                         true
% 7.47/1.51  --eq_ax_congr_red                       true
% 7.47/1.51  --pure_diseq_elim                       true
% 7.47/1.51  --brand_transform                       false
% 7.47/1.51  --non_eq_to_eq                          false
% 7.47/1.51  --prep_def_merge                        true
% 7.47/1.51  --prep_def_merge_prop_impl              false
% 7.47/1.51  --prep_def_merge_mbd                    true
% 7.47/1.51  --prep_def_merge_tr_red                 false
% 7.47/1.51  --prep_def_merge_tr_cl                  false
% 7.47/1.51  --smt_preprocessing                     true
% 7.47/1.51  --smt_ac_axioms                         fast
% 7.47/1.51  --preprocessed_out                      false
% 7.47/1.51  --preprocessed_stats                    false
% 7.47/1.51  
% 7.47/1.51  ------ Abstraction refinement Options
% 7.47/1.51  
% 7.47/1.51  --abstr_ref                             []
% 7.47/1.51  --abstr_ref_prep                        false
% 7.47/1.51  --abstr_ref_until_sat                   false
% 7.47/1.51  --abstr_ref_sig_restrict                funpre
% 7.47/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.51  --abstr_ref_under                       []
% 7.47/1.51  
% 7.47/1.51  ------ SAT Options
% 7.47/1.51  
% 7.47/1.51  --sat_mode                              false
% 7.47/1.51  --sat_fm_restart_options                ""
% 7.47/1.51  --sat_gr_def                            false
% 7.47/1.51  --sat_epr_types                         true
% 7.47/1.51  --sat_non_cyclic_types                  false
% 7.47/1.51  --sat_finite_models                     false
% 7.47/1.51  --sat_fm_lemmas                         false
% 7.47/1.51  --sat_fm_prep                           false
% 7.47/1.51  --sat_fm_uc_incr                        true
% 7.47/1.51  --sat_out_model                         small
% 7.47/1.51  --sat_out_clauses                       false
% 7.47/1.51  
% 7.47/1.51  ------ QBF Options
% 7.47/1.51  
% 7.47/1.51  --qbf_mode                              false
% 7.47/1.51  --qbf_elim_univ                         false
% 7.47/1.51  --qbf_dom_inst                          none
% 7.47/1.51  --qbf_dom_pre_inst                      false
% 7.47/1.51  --qbf_sk_in                             false
% 7.47/1.51  --qbf_pred_elim                         true
% 7.47/1.51  --qbf_split                             512
% 7.47/1.51  
% 7.47/1.51  ------ BMC1 Options
% 7.47/1.51  
% 7.47/1.51  --bmc1_incremental                      false
% 7.47/1.51  --bmc1_axioms                           reachable_all
% 7.47/1.51  --bmc1_min_bound                        0
% 7.47/1.51  --bmc1_max_bound                        -1
% 7.47/1.51  --bmc1_max_bound_default                -1
% 7.47/1.51  --bmc1_symbol_reachability              true
% 7.47/1.51  --bmc1_property_lemmas                  false
% 7.47/1.51  --bmc1_k_induction                      false
% 7.47/1.51  --bmc1_non_equiv_states                 false
% 7.47/1.51  --bmc1_deadlock                         false
% 7.47/1.51  --bmc1_ucm                              false
% 7.47/1.51  --bmc1_add_unsat_core                   none
% 7.47/1.51  --bmc1_unsat_core_children              false
% 7.47/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.51  --bmc1_out_stat                         full
% 7.47/1.51  --bmc1_ground_init                      false
% 7.47/1.51  --bmc1_pre_inst_next_state              false
% 7.47/1.51  --bmc1_pre_inst_state                   false
% 7.47/1.51  --bmc1_pre_inst_reach_state             false
% 7.47/1.51  --bmc1_out_unsat_core                   false
% 7.47/1.51  --bmc1_aig_witness_out                  false
% 7.47/1.51  --bmc1_verbose                          false
% 7.47/1.51  --bmc1_dump_clauses_tptp                false
% 7.47/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.51  --bmc1_dump_file                        -
% 7.47/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.51  --bmc1_ucm_extend_mode                  1
% 7.47/1.51  --bmc1_ucm_init_mode                    2
% 7.47/1.51  --bmc1_ucm_cone_mode                    none
% 7.47/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.51  --bmc1_ucm_relax_model                  4
% 7.47/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.51  --bmc1_ucm_layered_model                none
% 7.47/1.51  --bmc1_ucm_max_lemma_size               10
% 7.47/1.51  
% 7.47/1.51  ------ AIG Options
% 7.47/1.51  
% 7.47/1.51  --aig_mode                              false
% 7.47/1.51  
% 7.47/1.51  ------ Instantiation Options
% 7.47/1.51  
% 7.47/1.51  --instantiation_flag                    false
% 7.47/1.51  --inst_sos_flag                         false
% 7.47/1.51  --inst_sos_phase                        true
% 7.47/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel_side                     num_symb
% 7.47/1.51  --inst_solver_per_active                1400
% 7.47/1.51  --inst_solver_calls_frac                1.
% 7.47/1.51  --inst_passive_queue_type               priority_queues
% 7.47/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.51  --inst_passive_queues_freq              [25;2]
% 7.47/1.51  --inst_dismatching                      true
% 7.47/1.51  --inst_eager_unprocessed_to_passive     true
% 7.47/1.51  --inst_prop_sim_given                   true
% 7.47/1.51  --inst_prop_sim_new                     false
% 7.47/1.51  --inst_subs_new                         false
% 7.47/1.51  --inst_eq_res_simp                      false
% 7.47/1.51  --inst_subs_given                       false
% 7.47/1.51  --inst_orphan_elimination               true
% 7.47/1.51  --inst_learning_loop_flag               true
% 7.47/1.51  --inst_learning_start                   3000
% 7.47/1.51  --inst_learning_factor                  2
% 7.47/1.51  --inst_start_prop_sim_after_learn       3
% 7.47/1.51  --inst_sel_renew                        solver
% 7.47/1.51  --inst_lit_activity_flag                true
% 7.47/1.51  --inst_restr_to_given                   false
% 7.47/1.51  --inst_activity_threshold               500
% 7.47/1.51  --inst_out_proof                        true
% 7.47/1.51  
% 7.47/1.51  ------ Resolution Options
% 7.47/1.51  
% 7.47/1.51  --resolution_flag                       false
% 7.47/1.51  --res_lit_sel                           adaptive
% 7.47/1.51  --res_lit_sel_side                      none
% 7.47/1.51  --res_ordering                          kbo
% 7.47/1.51  --res_to_prop_solver                    active
% 7.47/1.51  --res_prop_simpl_new                    false
% 7.47/1.51  --res_prop_simpl_given                  true
% 7.47/1.51  --res_passive_queue_type                priority_queues
% 7.47/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.51  --res_passive_queues_freq               [15;5]
% 7.47/1.51  --res_forward_subs                      full
% 7.47/1.51  --res_backward_subs                     full
% 7.47/1.51  --res_forward_subs_resolution           true
% 7.47/1.51  --res_backward_subs_resolution          true
% 7.47/1.51  --res_orphan_elimination                true
% 7.47/1.51  --res_time_limit                        2.
% 7.47/1.51  --res_out_proof                         true
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Options
% 7.47/1.51  
% 7.47/1.51  --superposition_flag                    true
% 7.47/1.51  --sup_passive_queue_type                priority_queues
% 7.47/1.51  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.51  --demod_completeness_check              fast
% 7.47/1.51  --demod_use_ground                      true
% 7.47/1.51  --sup_to_prop_solver                    active
% 7.47/1.51  --sup_prop_simpl_new                    false
% 7.47/1.51  --sup_prop_simpl_given                  false
% 7.47/1.51  --sup_fun_splitting                     true
% 7.47/1.51  --sup_smt_interval                      10000
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Simplification Setup
% 7.47/1.51  
% 7.47/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.47/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_full_triv                         [TrivRules]
% 7.47/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.47/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.47/1.51  --sup_immed_triv                        [TrivRules]
% 7.47/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_immed_bw_main                     []
% 7.47/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.47/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.47/1.51  
% 7.47/1.51  ------ Combination Options
% 7.47/1.51  
% 7.47/1.51  --comb_res_mult                         1
% 7.47/1.51  --comb_sup_mult                         1
% 7.47/1.51  --comb_inst_mult                        1000000
% 7.47/1.51  
% 7.47/1.51  ------ Debug Options
% 7.47/1.51  
% 7.47/1.51  --dbg_backtrace                         false
% 7.47/1.51  --dbg_dump_prop_clauses                 false
% 7.47/1.51  --dbg_dump_prop_clauses_file            -
% 7.47/1.51  --dbg_out_stat                          false
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  ------ Proving...
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  % SZS status Theorem for theBenchmark.p
% 7.47/1.51  
% 7.47/1.51   Resolution empty clause
% 7.47/1.51  
% 7.47/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.47/1.51  
% 7.47/1.51  fof(f4,axiom,(
% 7.47/1.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f16,plain,(
% 7.47/1.51    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.47/1.51    inference(nnf_transformation,[],[f4])).
% 7.47/1.51  
% 7.47/1.51  fof(f23,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f16])).
% 7.47/1.51  
% 7.47/1.51  fof(f10,conjecture,(
% 7.47/1.51    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f11,negated_conjecture,(
% 7.47/1.51    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 7.47/1.51    inference(negated_conjecture,[],[f10])).
% 7.47/1.51  
% 7.47/1.51  fof(f14,plain,(
% 7.47/1.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 7.47/1.51    inference(ennf_transformation,[],[f11])).
% 7.47/1.51  
% 7.47/1.51  fof(f15,plain,(
% 7.47/1.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.47/1.51    inference(flattening,[],[f14])).
% 7.47/1.51  
% 7.47/1.51  fof(f17,plain,(
% 7.47/1.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 7.47/1.51    introduced(choice_axiom,[])).
% 7.47/1.51  
% 7.47/1.51  fof(f18,plain,(
% 7.47/1.51    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 7.47/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 7.47/1.51  
% 7.47/1.51  fof(f29,plain,(
% 7.47/1.51    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 7.47/1.51    inference(cnf_transformation,[],[f18])).
% 7.47/1.51  
% 7.47/1.51  fof(f7,axiom,(
% 7.47/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f26,plain,(
% 7.47/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f7])).
% 7.47/1.51  
% 7.47/1.51  fof(f6,axiom,(
% 7.47/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f25,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f6])).
% 7.47/1.51  
% 7.47/1.51  fof(f2,axiom,(
% 7.47/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f20,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f2])).
% 7.47/1.51  
% 7.47/1.51  fof(f8,axiom,(
% 7.47/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f27,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.47/1.51    inference(cnf_transformation,[],[f8])).
% 7.47/1.51  
% 7.47/1.51  fof(f32,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.47/1.51    inference(definition_unfolding,[],[f20,f27,f27])).
% 7.47/1.51  
% 7.47/1.51  fof(f5,axiom,(
% 7.47/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f24,plain,(
% 7.47/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.47/1.51    inference(cnf_transformation,[],[f5])).
% 7.47/1.51  
% 7.47/1.51  fof(f1,axiom,(
% 7.47/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f19,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f1])).
% 7.47/1.51  
% 7.47/1.51  fof(f9,axiom,(
% 7.47/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f28,plain,(
% 7.47/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.47/1.51    inference(cnf_transformation,[],[f9])).
% 7.47/1.51  
% 7.47/1.51  fof(f3,axiom,(
% 7.47/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f12,plain,(
% 7.47/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.47/1.51    inference(unused_predicate_definition_removal,[],[f3])).
% 7.47/1.51  
% 7.47/1.51  fof(f13,plain,(
% 7.47/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 7.47/1.51    inference(ennf_transformation,[],[f12])).
% 7.47/1.51  
% 7.47/1.51  fof(f21,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f13])).
% 7.47/1.51  
% 7.47/1.51  fof(f33,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.47/1.51    inference(definition_unfolding,[],[f21,f27])).
% 7.47/1.51  
% 7.47/1.51  fof(f30,plain,(
% 7.47/1.51    r1_xboole_0(sK0,sK2)),
% 7.47/1.51    inference(cnf_transformation,[],[f18])).
% 7.47/1.51  
% 7.47/1.51  fof(f22,plain,(
% 7.47/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f16])).
% 7.47/1.51  
% 7.47/1.51  fof(f31,plain,(
% 7.47/1.51    ~r1_tarski(sK0,sK1)),
% 7.47/1.51    inference(cnf_transformation,[],[f18])).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3,plain,
% 7.47/1.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f23]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_63,plain,
% 7.47/1.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.47/1.51      inference(prop_impl,[status(thm)],[c_3]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_11,negated_conjecture,
% 7.47/1.51      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 7.47/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_128,plain,
% 7.47/1.51      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.47/1.51      | k2_xboole_0(sK1,sK2) != X1
% 7.47/1.51      | sK0 != X0 ),
% 7.47/1.51      inference(resolution_lifted,[status(thm)],[c_63,c_11]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_129,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 7.47/1.51      inference(unflattening,[status(thm)],[c_128]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.47/1.51      inference(cnf_transformation,[],[f26]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f25]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.47/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_176,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f24]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_0,plain,
% 7.47/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.47/1.51      inference(cnf_transformation,[],[f19]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8,plain,
% 7.47/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.47/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_117,plain,
% 7.47/1.51      ( X0 != X1
% 7.47/1.51      | k4_xboole_0(X1,X2) = k1_xboole_0
% 7.47/1.51      | k2_xboole_0(X0,X3) != X2 ),
% 7.47/1.51      inference(resolution_lifted,[status(thm)],[c_63,c_8]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_118,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.47/1.51      inference(unflattening,[status(thm)],[c_117]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_274,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_118]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_377,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_176,c_5,c_274]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_387,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = X2 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7,c_377]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_12525,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_xboole_0) = sK2 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_129,c_387]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_13563,plain,
% 7.47/1.51      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = sK2 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_12525,c_5]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2,plain,
% 7.47/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.47/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_10,negated_conjecture,
% 7.47/1.51      ( r1_xboole_0(sK0,sK2) ),
% 7.47/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_110,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.47/1.51      | sK2 != X1
% 7.47/1.51      | sK0 != X0 ),
% 7.47/1.51      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_111,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 7.47/1.51      inference(unflattening,[status(thm)],[c_110]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_180,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_633,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_111,c_180]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_171,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_172,plain,
% 7.47/1.51      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_171,c_5]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_198,plain,
% 7.47/1.51      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_172]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_277,plain,
% 7.47/1.51      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_198,c_118]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_681,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k1_xboole_0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_633,c_277]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_169,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_305,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_169,c_1]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_309,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_305,c_5,c_118]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_911,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X0),sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK0),X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_681,c_309]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1634,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_911,c_5]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_906,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_172,c_681]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_926,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_906,c_377]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3446,plain,
% 7.47/1.51      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_926,c_5]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3719,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)) = sK2 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3446,c_309]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_191,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_194,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_191,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_190,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1943,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_194,c_190]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3738,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) = sK2 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_3719,c_7,c_1943]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3739,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_3738,c_172,c_274]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_4066,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(sK2,X0),sK2) = k2_xboole_0(sK2,X0) ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_1634,c_1634,c_3739]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_4070,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(X0,sK2),sK2) = k2_xboole_0(sK2,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_4066]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_13609,plain,
% 7.47/1.51      ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,sK2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_13563,c_4070]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3744,plain,
% 7.47/1.51      ( k2_xboole_0(sK2,sK2) = sK2 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_3739,c_3446]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_13615,plain,
% 7.47/1.51      ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = sK2 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_13609,c_3744]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_441,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_6,c_309]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_18307,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_13615,c_441]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3722,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3446,c_6]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3894,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_3722,c_906,c_3739]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_445,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK2),sK0),k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_129,c_309]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_526,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k2_xboole_0(sK1,sK2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_445,c_5]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_187,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_195,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_187,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2541,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK0))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_526,c_195]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2810,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2541,c_274]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2948,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_2810]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3117,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK2)),X0)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0),X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2948,c_180]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2960,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK0)),X0)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK0),k1_xboole_0),X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2810,c_180]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_183,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_196,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_183,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2977,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)),X0)) = k4_xboole_0(k2_xboole_0(sK2,sK0),X0) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_2960,c_7,c_196,c_198]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3035,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_196]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3130,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK0,sK2),X0) = k4_xboole_0(k2_xboole_0(sK2,sK0),X0) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_3117,c_7,c_198,c_2977,c_3035]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_13600,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_13563,c_190]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_18005,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK2),sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK0,sK1)))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3130,c_13600]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5710,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)) = sK0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3130,c_377]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5765,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK0,sK2),sK2) = sK0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_5710,c_3739]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_18073,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK0,sK1)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK0,sK1)),sK0) ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_18005,c_5765]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_185,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_111,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_448,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),X0),sK0),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k4_xboole_0(sK0,sK2),X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_185,c_309]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_480,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),X0),sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,sK2),X0) ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_448,c_277]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_388,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_111,c_377]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_498,plain,
% 7.47/1.51      ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_388,c_5]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_528,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) = sK0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_498,c_309]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_541,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))) = sK0 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_528,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_542,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_541,c_172,c_274]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1567,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),sK0),k1_xboole_0) = k2_xboole_0(sK0,X0) ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_480,c_480,c_542]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1592,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(sK0,X0),sK0) = k2_xboole_0(sK0,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_1567,c_5]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2188,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(X0,sK0),sK0) = k2_xboole_0(sK0,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_1592]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2651,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK0,sK0))) = k4_xboole_0(X0,k2_xboole_0(sK0,X1)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2188,c_195]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_545,plain,
% 7.47/1.51      ( k2_xboole_0(sK0,sK0) = sK0 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_542,c_498]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2658,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,sK0)) = k4_xboole_0(X0,k2_xboole_0(sK0,X1)) ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_2651,c_545]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5731,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(X0,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,X0)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3130,c_2658]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3034,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(sK0,X1)) = k4_xboole_0(k2_xboole_0(sK0,X0),k2_xboole_0(sK0,X1)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2188,c_196]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3102,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK0,X0),k2_xboole_0(sK0,X1)) = k4_xboole_0(X0,k2_xboole_0(sK0,X1)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_3034,c_196]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5743,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_5731,c_3102,c_3130]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_465,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_309,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_15035,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_194,c_465]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_15036,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0),k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_190,c_465]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_15367,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0)))),X3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_15036,c_7,c_1943]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_15368,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_15035,c_15367]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_13599,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X0,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_13563,c_194]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_17845,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X0,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK0,sK1)))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_169,c_13599]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_15017,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X2) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_465]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_17979,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_17845,c_15017]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_18074,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_18073,c_5743,c_15368,c_17979]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1067,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_274,c_190]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1239,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_1067,c_7,c_172]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_4224,plain,
% 7.47/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_1,c_1239]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6657,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_377,c_4224]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1076,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_172,c_190]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1229,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_1076,c_7,c_277]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6870,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_6657,c_6,c_1229]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6995,plain,
% 7.47/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_6870]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_12553,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),X0),k1_xboole_0) = X0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_6995,c_387]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_186,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_129,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_217,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_186]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2578,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_195,c_217]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_236,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_217,c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_238,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_236,c_7,c_195]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_352,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),X1)) = k1_xboole_0 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_238,c_277]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_358,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_352]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2597,plain,
% 7.47/1.51      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_2578,c_358]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_386,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_6,c_377]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3254,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2597,c_386]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_460,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_274,c_309]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3329,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_3254,c_5,c_198,c_460]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5806,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_0,c_3329]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8343,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_5806,c_386]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3065,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_196,c_169]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3082,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_3065,c_118]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8405,plain,
% 7.47/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_8343,c_5,c_3082]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8353,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_5806,c_441]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8400,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_8353,c_3082]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8406,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_8405,c_8400]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_12754,plain,
% 7.47/1.51      ( k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X1))) = X0 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_12553,c_7,c_8406]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5809,plain,
% 7.47/1.51      ( k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_198,c_3329]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5877,plain,
% 7.47/1.51      ( k2_xboole_0(X0,X0) = X0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_5809,c_198]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_12755,plain,
% 7.47/1.51      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_12754,c_5877]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_15211,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(sK2,X0) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_465,c_3130]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_5714,plain,
% 7.47/1.51      ( k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3130,c_196]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_15216,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_15211,c_542,c_5714]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_18075,plain,
% 7.47/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = sK2 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_18074,c_3739,c_12755,c_15216]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_18337,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 7.47/1.51      inference(light_normalisation,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_18307,c_3894,c_13563,c_18075]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_4,plain,
% 7.47/1.51      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f22]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_61,plain,
% 7.47/1.51      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.47/1.51      inference(prop_impl,[status(thm)],[c_4]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_9,negated_conjecture,
% 7.47/1.51      ( ~ r1_tarski(sK0,sK1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_123,plain,
% 7.47/1.51      ( k4_xboole_0(X0,X1) != k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 7.47/1.51      inference(resolution_lifted,[status(thm)],[c_61,c_9]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_124,plain,
% 7.47/1.51      ( k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
% 7.47/1.51      inference(unflattening,[status(thm)],[c_123]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_18376,plain,
% 7.47/1.51      ( k1_xboole_0 != k1_xboole_0 ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_18337,c_124]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_18377,plain,
% 7.47/1.51      ( $false ),
% 7.47/1.51      inference(equality_resolution_simp,[status(thm)],[c_18376]) ).
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.47/1.51  
% 7.47/1.51  ------                               Statistics
% 7.47/1.51  
% 7.47/1.51  ------ General
% 7.47/1.51  
% 7.47/1.51  abstr_ref_over_cycles:                  0
% 7.47/1.51  abstr_ref_under_cycles:                 0
% 7.47/1.51  gc_basic_clause_elim:                   0
% 7.47/1.51  forced_gc_time:                         0
% 7.47/1.51  parsing_time:                           0.024
% 7.47/1.51  unif_index_cands_time:                  0.
% 7.47/1.51  unif_index_add_time:                    0.
% 7.47/1.51  orderings_time:                         0.
% 7.47/1.51  out_proof_time:                         0.009
% 7.47/1.51  total_time:                             0.92
% 7.47/1.51  num_of_symbols:                         39
% 7.47/1.51  num_of_terms:                           36999
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing
% 7.47/1.51  
% 7.47/1.51  num_of_splits:                          0
% 7.47/1.51  num_of_split_atoms:                     0
% 7.47/1.51  num_of_reused_defs:                     0
% 7.47/1.51  num_eq_ax_congr_red:                    0
% 7.47/1.51  num_of_sem_filtered_clauses:            0
% 7.47/1.51  num_of_subtypes:                        0
% 7.47/1.51  monotx_restored_types:                  0
% 7.47/1.51  sat_num_of_epr_types:                   0
% 7.47/1.51  sat_num_of_non_cyclic_types:            0
% 7.47/1.51  sat_guarded_non_collapsed_types:        0
% 7.47/1.51  num_pure_diseq_elim:                    0
% 7.47/1.51  simp_replaced_by:                       0
% 7.47/1.51  res_preprocessed:                       38
% 7.47/1.51  prep_upred:                             0
% 7.47/1.51  prep_unflattend:                        9
% 7.47/1.51  smt_new_axioms:                         0
% 7.47/1.51  pred_elim_cands:                        0
% 7.47/1.51  pred_elim:                              2
% 7.47/1.51  pred_elim_cl:                           1
% 7.47/1.51  pred_elim_cycles:                       3
% 7.47/1.51  merged_defs:                            2
% 7.47/1.51  merged_defs_ncl:                        0
% 7.47/1.51  bin_hyper_res:                          2
% 7.47/1.51  prep_cycles:                            3
% 7.47/1.51  pred_elim_time:                         0.001
% 7.47/1.51  splitting_time:                         0.
% 7.47/1.51  sem_filter_time:                        0.
% 7.47/1.51  monotx_time:                            0.
% 7.47/1.51  subtype_inf_time:                       0.
% 7.47/1.51  
% 7.47/1.51  ------ Problem properties
% 7.47/1.51  
% 7.47/1.51  clauses:                                11
% 7.47/1.51  conjectures:                            0
% 7.47/1.51  epr:                                    0
% 7.47/1.51  horn:                                   11
% 7.47/1.51  ground:                                 4
% 7.47/1.51  unary:                                  11
% 7.47/1.51  binary:                                 0
% 7.47/1.51  lits:                                   11
% 7.47/1.51  lits_eq:                                11
% 7.47/1.51  fd_pure:                                0
% 7.47/1.51  fd_pseudo:                              0
% 7.47/1.51  fd_cond:                                0
% 7.47/1.51  fd_pseudo_cond:                         0
% 7.47/1.51  ac_symbols:                             0
% 7.47/1.51  
% 7.47/1.51  ------ Propositional Solver
% 7.47/1.51  
% 7.47/1.51  prop_solver_calls:                      17
% 7.47/1.51  prop_fast_solver_calls:                 101
% 7.47/1.51  smt_solver_calls:                       0
% 7.47/1.51  smt_fast_solver_calls:                  0
% 7.47/1.51  prop_num_of_clauses:                    453
% 7.47/1.51  prop_preprocess_simplified:             574
% 7.47/1.51  prop_fo_subsumed:                       0
% 7.47/1.51  prop_solver_time:                       0.
% 7.47/1.51  smt_solver_time:                        0.
% 7.47/1.51  smt_fast_solver_time:                   0.
% 7.47/1.51  prop_fast_solver_time:                  0.
% 7.47/1.51  prop_unsat_core_time:                   0.
% 7.47/1.51  
% 7.47/1.51  ------ QBF
% 7.47/1.51  
% 7.47/1.51  qbf_q_res:                              0
% 7.47/1.51  qbf_num_tautologies:                    0
% 7.47/1.51  qbf_prep_cycles:                        0
% 7.47/1.51  
% 7.47/1.51  ------ BMC1
% 7.47/1.51  
% 7.47/1.51  bmc1_current_bound:                     -1
% 7.47/1.51  bmc1_last_solved_bound:                 -1
% 7.47/1.51  bmc1_unsat_core_size:                   -1
% 7.47/1.51  bmc1_unsat_core_parents_size:           -1
% 7.47/1.51  bmc1_merge_next_fun:                    0
% 7.47/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.47/1.51  
% 7.47/1.51  ------ Instantiation
% 7.47/1.51  
% 7.47/1.51  inst_num_of_clauses:                    0
% 7.47/1.51  inst_num_in_passive:                    0
% 7.47/1.51  inst_num_in_active:                     0
% 7.47/1.51  inst_num_in_unprocessed:                0
% 7.47/1.51  inst_num_of_loops:                      0
% 7.47/1.51  inst_num_of_learning_restarts:          0
% 7.47/1.51  inst_num_moves_active_passive:          0
% 7.47/1.51  inst_lit_activity:                      0
% 7.47/1.51  inst_lit_activity_moves:                0
% 7.47/1.51  inst_num_tautologies:                   0
% 7.47/1.51  inst_num_prop_implied:                  0
% 7.47/1.51  inst_num_existing_simplified:           0
% 7.47/1.51  inst_num_eq_res_simplified:             0
% 7.47/1.51  inst_num_child_elim:                    0
% 7.47/1.51  inst_num_of_dismatching_blockings:      0
% 7.47/1.51  inst_num_of_non_proper_insts:           0
% 7.47/1.51  inst_num_of_duplicates:                 0
% 7.47/1.51  inst_inst_num_from_inst_to_res:         0
% 7.47/1.51  inst_dismatching_checking_time:         0.
% 7.47/1.51  
% 7.47/1.51  ------ Resolution
% 7.47/1.51  
% 7.47/1.51  res_num_of_clauses:                     0
% 7.47/1.51  res_num_in_passive:                     0
% 7.47/1.51  res_num_in_active:                      0
% 7.47/1.51  res_num_of_loops:                       41
% 7.47/1.51  res_forward_subset_subsumed:            0
% 7.47/1.51  res_backward_subset_subsumed:           0
% 7.47/1.51  res_forward_subsumed:                   0
% 7.47/1.51  res_backward_subsumed:                  0
% 7.47/1.51  res_forward_subsumption_resolution:     0
% 7.47/1.51  res_backward_subsumption_resolution:    0
% 7.47/1.51  res_clause_to_clause_subsumption:       42913
% 7.47/1.51  res_orphan_elimination:                 0
% 7.47/1.51  res_tautology_del:                      5
% 7.47/1.51  res_num_eq_res_simplified:              1
% 7.47/1.51  res_num_sel_changes:                    0
% 7.47/1.51  res_moves_from_active_to_pass:          0
% 7.47/1.51  
% 7.47/1.51  ------ Superposition
% 7.47/1.51  
% 7.47/1.51  sup_time_total:                         0.
% 7.47/1.51  sup_time_generating:                    0.
% 7.47/1.51  sup_time_sim_full:                      0.
% 7.47/1.51  sup_time_sim_immed:                     0.
% 7.47/1.51  
% 7.47/1.51  sup_num_of_clauses:                     2984
% 7.47/1.51  sup_num_in_active:                      162
% 7.47/1.51  sup_num_in_passive:                     2822
% 7.47/1.51  sup_num_of_loops:                       254
% 7.47/1.51  sup_fw_superposition:                   6092
% 7.47/1.51  sup_bw_superposition:                   5225
% 7.47/1.51  sup_immediate_simplified:               6435
% 7.47/1.51  sup_given_eliminated:                   23
% 7.47/1.51  comparisons_done:                       0
% 7.47/1.51  comparisons_avoided:                    0
% 7.47/1.51  
% 7.47/1.51  ------ Simplifications
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  sim_fw_subset_subsumed:                 0
% 7.47/1.51  sim_bw_subset_subsumed:                 0
% 7.47/1.51  sim_fw_subsumed:                        1559
% 7.47/1.51  sim_bw_subsumed:                        100
% 7.47/1.51  sim_fw_subsumption_res:                 0
% 7.47/1.51  sim_bw_subsumption_res:                 0
% 7.47/1.51  sim_tautology_del:                      0
% 7.47/1.51  sim_eq_tautology_del:                   2053
% 7.47/1.51  sim_eq_res_simp:                        0
% 7.47/1.51  sim_fw_demodulated:                     4129
% 7.47/1.51  sim_bw_demodulated:                     132
% 7.47/1.51  sim_light_normalised:                   2471
% 7.47/1.51  sim_joinable_taut:                      0
% 7.47/1.51  sim_joinable_simp:                      0
% 7.47/1.51  sim_ac_normalised:                      0
% 7.47/1.51  sim_smt_subsumption:                    0
% 7.47/1.51  
%------------------------------------------------------------------------------
