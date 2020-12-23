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
% DateTime   : Thu Dec  3 11:26:13 EST 2020

% Result     : Theorem 39.50s
% Output     : CNFRefutation 39.50s
% Verified   : 
% Statistics : Number of formulae       :  120 (1043 expanded)
%              Number of clauses        :   84 ( 407 expanded)
%              Number of leaves         :   14 ( 278 expanded)
%              Depth                    :   21
%              Number of atoms          :  133 (1284 expanded)
%              Number of equality atoms :  120 (1061 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f32,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f31,f23])).

fof(f36,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
    inference(definition_unfolding,[],[f33,f23,f34,f23,f23])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_96,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_378,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_96])).

cnf(c_6,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_57,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_6,c_8,c_1,c_4,c_0])).

cnf(c_1611,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_378,c_57])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_46,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_47,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_46])).

cnf(c_90,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK2)) = k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_47,c_57])).

cnf(c_91,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK2)) = k3_xboole_0(X0,k5_xboole_0(sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_90,c_47])).

cnf(c_92,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_91,c_9])).

cnf(c_3,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_58,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_3,c_8,c_1,c_4,c_0])).

cnf(c_272,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_58])).

cnf(c_274,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_58])).

cnf(c_1655,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1611,c_9,c_92,c_272,c_274])).

cnf(c_7204,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1655,c_274])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7335,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7204,c_7])).

cnf(c_67,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_738,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k3_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_47,c_67])).

cnf(c_991,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_0,c_738])).

cnf(c_286,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_58])).

cnf(c_8633,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK2,k3_xboole_0(sK1,X0))) = k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_991,c_286])).

cnf(c_276,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK1,k5_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_47,c_58])).

cnf(c_97,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_47,c_4])).

cnf(c_277,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(k3_xboole_0(sK1,X0),X1)) = k3_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_97,c_58])).

cnf(c_646,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK2,k3_xboole_0(sK1,X0))) = k5_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_277])).

cnf(c_666,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,k5_xboole_0(sK2,X0))) = k5_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_646,c_276])).

cnf(c_284,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_58])).

cnf(c_667,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,k5_xboole_0(sK2,X0))) = k3_xboole_0(X0,k5_xboole_0(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_666,c_284])).

cnf(c_8804,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(sK1,X0)) = k3_xboole_0(X0,k5_xboole_0(sK2,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_8633,c_276,c_667])).

cnf(c_48906,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),sK2),sK1) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),k5_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_7335,c_8804])).

cnf(c_48912,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),sK2) = k3_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_7335,c_991])).

cnf(c_49110,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_48912,c_47])).

cnf(c_49116,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_48906,c_49110])).

cnf(c_51039,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_49116,c_286])).

cnf(c_142,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_97,c_57])).

cnf(c_143,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_142,c_47])).

cnf(c_148,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_143])).

cnf(c_206,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_47,c_148])).

cnf(c_214,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_206,c_2,c_9])).

cnf(c_222,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_214])).

cnf(c_337,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(sK2,sK1),X0)) = k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_222,c_58])).

cnf(c_76,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_351,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,X0)) = k3_xboole_0(k5_xboole_0(sK2,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_337,c_76])).

cnf(c_107,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_112,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_107,c_76])).

cnf(c_72,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_32284,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_112,c_72])).

cnf(c_430,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2,c_276])).

cnf(c_70,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_4637,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(sK1,X1))) = k5_xboole_0(X0,k3_xboole_0(sK1,k5_xboole_0(sK2,X1))) ),
    inference(superposition,[status(thm)],[c_276,c_70])).

cnf(c_5375,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_430,c_4637])).

cnf(c_5491,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK2,sK1))) = k5_xboole_0(X0,sK1) ),
    inference(demodulation,[status(thm)],[c_5375,c_2,c_112])).

cnf(c_36044,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_5491])).

cnf(c_433,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK2,X0)),X1) ),
    inference(superposition,[status(thm)],[c_276,c_8])).

cnf(c_494,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK1,sK1),X0)) = k5_xboole_0(k5_xboole_0(sK2,sK1),X0) ),
    inference(superposition,[status(thm)],[c_430,c_433])).

cnf(c_523,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,X0)) = k5_xboole_0(k5_xboole_0(sK2,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_494,c_2])).

cnf(c_36231,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_36044,c_7,c_523])).

cnf(c_36258,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(X0,sK1)) = k5_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_36231,c_70])).

cnf(c_51108,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(X0,k5_xboole_0(X0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51039,c_9,c_351,c_32284,c_36258])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_56,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_8,c_1,c_4,c_0])).

cnf(c_66,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_56,c_47])).

cnf(c_73,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_0,c_66])).

cnf(c_74,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_73,c_57])).

cnf(c_75,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_1,c_74])).

cnf(c_6890,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_75,c_272,c_274])).

cnf(c_4629,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_70])).

cnf(c_4680,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4629,c_7])).

cnf(c_5733,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_4680,c_72])).

cnf(c_6891,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_6890,c_5733])).

cnf(c_6892,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_6891,c_274])).

cnf(c_125537,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_51108,c_6892])).

cnf(c_125538,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_125537,c_76])).

cnf(c_125539,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_125538])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:03:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.50/5.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.50/5.48  
% 39.50/5.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.50/5.48  
% 39.50/5.48  ------  iProver source info
% 39.50/5.48  
% 39.50/5.48  git: date: 2020-06-30 10:37:57 +0100
% 39.50/5.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.50/5.48  git: non_committed_changes: false
% 39.50/5.48  git: last_make_outside_of_git: false
% 39.50/5.48  
% 39.50/5.48  ------ 
% 39.50/5.48  
% 39.50/5.48  ------ Input Options
% 39.50/5.48  
% 39.50/5.48  --out_options                           all
% 39.50/5.48  --tptp_safe_out                         true
% 39.50/5.48  --problem_path                          ""
% 39.50/5.48  --include_path                          ""
% 39.50/5.48  --clausifier                            res/vclausify_rel
% 39.50/5.48  --clausifier_options                    ""
% 39.50/5.48  --stdin                                 false
% 39.50/5.48  --stats_out                             all
% 39.50/5.48  
% 39.50/5.48  ------ General Options
% 39.50/5.48  
% 39.50/5.48  --fof                                   false
% 39.50/5.48  --time_out_real                         305.
% 39.50/5.48  --time_out_virtual                      -1.
% 39.50/5.48  --symbol_type_check                     false
% 39.50/5.48  --clausify_out                          false
% 39.50/5.48  --sig_cnt_out                           false
% 39.50/5.48  --trig_cnt_out                          false
% 39.50/5.48  --trig_cnt_out_tolerance                1.
% 39.50/5.48  --trig_cnt_out_sk_spl                   false
% 39.50/5.48  --abstr_cl_out                          false
% 39.50/5.48  
% 39.50/5.48  ------ Global Options
% 39.50/5.48  
% 39.50/5.48  --schedule                              default
% 39.50/5.48  --add_important_lit                     false
% 39.50/5.48  --prop_solver_per_cl                    1000
% 39.50/5.48  --min_unsat_core                        false
% 39.50/5.48  --soft_assumptions                      false
% 39.50/5.48  --soft_lemma_size                       3
% 39.50/5.48  --prop_impl_unit_size                   0
% 39.50/5.48  --prop_impl_unit                        []
% 39.50/5.48  --share_sel_clauses                     true
% 39.50/5.48  --reset_solvers                         false
% 39.50/5.48  --bc_imp_inh                            [conj_cone]
% 39.50/5.48  --conj_cone_tolerance                   3.
% 39.50/5.48  --extra_neg_conj                        none
% 39.50/5.48  --large_theory_mode                     true
% 39.50/5.48  --prolific_symb_bound                   200
% 39.50/5.48  --lt_threshold                          2000
% 39.50/5.48  --clause_weak_htbl                      true
% 39.50/5.48  --gc_record_bc_elim                     false
% 39.50/5.48  
% 39.50/5.48  ------ Preprocessing Options
% 39.50/5.48  
% 39.50/5.48  --preprocessing_flag                    true
% 39.50/5.48  --time_out_prep_mult                    0.1
% 39.50/5.48  --splitting_mode                        input
% 39.50/5.48  --splitting_grd                         true
% 39.50/5.48  --splitting_cvd                         false
% 39.50/5.48  --splitting_cvd_svl                     false
% 39.50/5.48  --splitting_nvd                         32
% 39.50/5.48  --sub_typing                            true
% 39.50/5.48  --prep_gs_sim                           true
% 39.50/5.48  --prep_unflatten                        true
% 39.50/5.48  --prep_res_sim                          true
% 39.50/5.48  --prep_upred                            true
% 39.50/5.48  --prep_sem_filter                       exhaustive
% 39.50/5.48  --prep_sem_filter_out                   false
% 39.50/5.48  --pred_elim                             true
% 39.50/5.48  --res_sim_input                         true
% 39.50/5.48  --eq_ax_congr_red                       true
% 39.50/5.48  --pure_diseq_elim                       true
% 39.50/5.48  --brand_transform                       false
% 39.50/5.48  --non_eq_to_eq                          false
% 39.50/5.48  --prep_def_merge                        true
% 39.50/5.48  --prep_def_merge_prop_impl              false
% 39.50/5.48  --prep_def_merge_mbd                    true
% 39.50/5.48  --prep_def_merge_tr_red                 false
% 39.50/5.48  --prep_def_merge_tr_cl                  false
% 39.50/5.48  --smt_preprocessing                     true
% 39.50/5.48  --smt_ac_axioms                         fast
% 39.50/5.48  --preprocessed_out                      false
% 39.50/5.48  --preprocessed_stats                    false
% 39.50/5.48  
% 39.50/5.48  ------ Abstraction refinement Options
% 39.50/5.48  
% 39.50/5.48  --abstr_ref                             []
% 39.50/5.48  --abstr_ref_prep                        false
% 39.50/5.48  --abstr_ref_until_sat                   false
% 39.50/5.48  --abstr_ref_sig_restrict                funpre
% 39.50/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.50/5.48  --abstr_ref_under                       []
% 39.50/5.48  
% 39.50/5.48  ------ SAT Options
% 39.50/5.48  
% 39.50/5.48  --sat_mode                              false
% 39.50/5.48  --sat_fm_restart_options                ""
% 39.50/5.48  --sat_gr_def                            false
% 39.50/5.48  --sat_epr_types                         true
% 39.50/5.48  --sat_non_cyclic_types                  false
% 39.50/5.48  --sat_finite_models                     false
% 39.50/5.48  --sat_fm_lemmas                         false
% 39.50/5.48  --sat_fm_prep                           false
% 39.50/5.48  --sat_fm_uc_incr                        true
% 39.50/5.48  --sat_out_model                         small
% 39.50/5.48  --sat_out_clauses                       false
% 39.50/5.48  
% 39.50/5.48  ------ QBF Options
% 39.50/5.48  
% 39.50/5.48  --qbf_mode                              false
% 39.50/5.48  --qbf_elim_univ                         false
% 39.50/5.48  --qbf_dom_inst                          none
% 39.50/5.48  --qbf_dom_pre_inst                      false
% 39.50/5.48  --qbf_sk_in                             false
% 39.50/5.48  --qbf_pred_elim                         true
% 39.50/5.48  --qbf_split                             512
% 39.50/5.48  
% 39.50/5.48  ------ BMC1 Options
% 39.50/5.48  
% 39.50/5.48  --bmc1_incremental                      false
% 39.50/5.48  --bmc1_axioms                           reachable_all
% 39.50/5.48  --bmc1_min_bound                        0
% 39.50/5.48  --bmc1_max_bound                        -1
% 39.50/5.48  --bmc1_max_bound_default                -1
% 39.50/5.48  --bmc1_symbol_reachability              true
% 39.50/5.48  --bmc1_property_lemmas                  false
% 39.50/5.48  --bmc1_k_induction                      false
% 39.50/5.48  --bmc1_non_equiv_states                 false
% 39.50/5.48  --bmc1_deadlock                         false
% 39.50/5.48  --bmc1_ucm                              false
% 39.50/5.48  --bmc1_add_unsat_core                   none
% 39.50/5.48  --bmc1_unsat_core_children              false
% 39.50/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.50/5.48  --bmc1_out_stat                         full
% 39.50/5.48  --bmc1_ground_init                      false
% 39.50/5.48  --bmc1_pre_inst_next_state              false
% 39.50/5.48  --bmc1_pre_inst_state                   false
% 39.50/5.48  --bmc1_pre_inst_reach_state             false
% 39.50/5.48  --bmc1_out_unsat_core                   false
% 39.50/5.48  --bmc1_aig_witness_out                  false
% 39.50/5.48  --bmc1_verbose                          false
% 39.50/5.48  --bmc1_dump_clauses_tptp                false
% 39.50/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.50/5.48  --bmc1_dump_file                        -
% 39.50/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.50/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.50/5.48  --bmc1_ucm_extend_mode                  1
% 39.50/5.48  --bmc1_ucm_init_mode                    2
% 39.50/5.48  --bmc1_ucm_cone_mode                    none
% 39.50/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.50/5.48  --bmc1_ucm_relax_model                  4
% 39.50/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.50/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.50/5.48  --bmc1_ucm_layered_model                none
% 39.50/5.48  --bmc1_ucm_max_lemma_size               10
% 39.50/5.48  
% 39.50/5.48  ------ AIG Options
% 39.50/5.48  
% 39.50/5.48  --aig_mode                              false
% 39.50/5.48  
% 39.50/5.48  ------ Instantiation Options
% 39.50/5.48  
% 39.50/5.48  --instantiation_flag                    true
% 39.50/5.48  --inst_sos_flag                         true
% 39.50/5.48  --inst_sos_phase                        true
% 39.50/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.50/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.50/5.48  --inst_lit_sel_side                     num_symb
% 39.50/5.48  --inst_solver_per_active                1400
% 39.50/5.48  --inst_solver_calls_frac                1.
% 39.50/5.48  --inst_passive_queue_type               priority_queues
% 39.50/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.50/5.48  --inst_passive_queues_freq              [25;2]
% 39.50/5.48  --inst_dismatching                      true
% 39.50/5.48  --inst_eager_unprocessed_to_passive     true
% 39.50/5.48  --inst_prop_sim_given                   true
% 39.50/5.48  --inst_prop_sim_new                     false
% 39.50/5.48  --inst_subs_new                         false
% 39.50/5.48  --inst_eq_res_simp                      false
% 39.50/5.48  --inst_subs_given                       false
% 39.50/5.48  --inst_orphan_elimination               true
% 39.50/5.48  --inst_learning_loop_flag               true
% 39.50/5.48  --inst_learning_start                   3000
% 39.50/5.48  --inst_learning_factor                  2
% 39.50/5.48  --inst_start_prop_sim_after_learn       3
% 39.50/5.48  --inst_sel_renew                        solver
% 39.50/5.48  --inst_lit_activity_flag                true
% 39.50/5.48  --inst_restr_to_given                   false
% 39.50/5.48  --inst_activity_threshold               500
% 39.50/5.48  --inst_out_proof                        true
% 39.50/5.48  
% 39.50/5.48  ------ Resolution Options
% 39.50/5.48  
% 39.50/5.48  --resolution_flag                       true
% 39.50/5.48  --res_lit_sel                           adaptive
% 39.50/5.48  --res_lit_sel_side                      none
% 39.50/5.48  --res_ordering                          kbo
% 39.50/5.48  --res_to_prop_solver                    active
% 39.50/5.48  --res_prop_simpl_new                    false
% 39.50/5.48  --res_prop_simpl_given                  true
% 39.50/5.48  --res_passive_queue_type                priority_queues
% 39.50/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.50/5.48  --res_passive_queues_freq               [15;5]
% 39.50/5.48  --res_forward_subs                      full
% 39.50/5.48  --res_backward_subs                     full
% 39.50/5.48  --res_forward_subs_resolution           true
% 39.50/5.48  --res_backward_subs_resolution          true
% 39.50/5.48  --res_orphan_elimination                true
% 39.50/5.48  --res_time_limit                        2.
% 39.50/5.48  --res_out_proof                         true
% 39.50/5.48  
% 39.50/5.48  ------ Superposition Options
% 39.50/5.48  
% 39.50/5.48  --superposition_flag                    true
% 39.50/5.48  --sup_passive_queue_type                priority_queues
% 39.50/5.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.50/5.48  --sup_passive_queues_freq               [8;1;4]
% 39.50/5.48  --demod_completeness_check              fast
% 39.50/5.48  --demod_use_ground                      true
% 39.50/5.48  --sup_to_prop_solver                    passive
% 39.50/5.48  --sup_prop_simpl_new                    true
% 39.50/5.48  --sup_prop_simpl_given                  true
% 39.50/5.48  --sup_fun_splitting                     true
% 39.50/5.48  --sup_smt_interval                      50000
% 39.50/5.48  
% 39.50/5.48  ------ Superposition Simplification Setup
% 39.50/5.48  
% 39.50/5.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.50/5.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.50/5.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.50/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.50/5.48  --sup_full_triv                         [TrivRules;PropSubs]
% 39.50/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.50/5.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.50/5.48  --sup_immed_triv                        [TrivRules]
% 39.50/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.50/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.50/5.48  --sup_immed_bw_main                     []
% 39.50/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.50/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.50/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.50/5.48  --sup_input_bw                          []
% 39.50/5.48  
% 39.50/5.48  ------ Combination Options
% 39.50/5.48  
% 39.50/5.48  --comb_res_mult                         3
% 39.50/5.48  --comb_sup_mult                         2
% 39.50/5.48  --comb_inst_mult                        10
% 39.50/5.48  
% 39.50/5.48  ------ Debug Options
% 39.50/5.48  
% 39.50/5.48  --dbg_backtrace                         false
% 39.50/5.48  --dbg_dump_prop_clauses                 false
% 39.50/5.48  --dbg_dump_prop_clauses_file            -
% 39.50/5.48  --dbg_out_stat                          false
% 39.50/5.48  ------ Parsing...
% 39.50/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.50/5.48  
% 39.50/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.50/5.48  
% 39.50/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.50/5.48  
% 39.50/5.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.50/5.48  ------ Proving...
% 39.50/5.48  ------ Problem Properties 
% 39.50/5.48  
% 39.50/5.48  
% 39.50/5.48  clauses                                 11
% 39.50/5.48  conjectures                             1
% 39.50/5.48  EPR                                     0
% 39.50/5.48  Horn                                    11
% 39.50/5.48  unary                                   11
% 39.50/5.48  binary                                  0
% 39.50/5.48  lits                                    11
% 39.50/5.48  lits eq                                 11
% 39.50/5.48  fd_pure                                 0
% 39.50/5.48  fd_pseudo                               0
% 39.50/5.48  fd_cond                                 0
% 39.50/5.48  fd_pseudo_cond                          0
% 39.50/5.48  AC symbols                              2
% 39.50/5.48  
% 39.50/5.48  ------ Schedule UEQ
% 39.50/5.48  
% 39.50/5.48  ------ pure equality problem: resolution off 
% 39.50/5.48  
% 39.50/5.48  ------ Option_UEQ Time Limit: Unbounded
% 39.50/5.48  
% 39.50/5.48  
% 39.50/5.48  ------ 
% 39.50/5.48  Current options:
% 39.50/5.48  ------ 
% 39.50/5.48  
% 39.50/5.48  ------ Input Options
% 39.50/5.48  
% 39.50/5.48  --out_options                           all
% 39.50/5.48  --tptp_safe_out                         true
% 39.50/5.48  --problem_path                          ""
% 39.50/5.48  --include_path                          ""
% 39.50/5.48  --clausifier                            res/vclausify_rel
% 39.50/5.48  --clausifier_options                    ""
% 39.50/5.48  --stdin                                 false
% 39.50/5.48  --stats_out                             all
% 39.50/5.48  
% 39.50/5.48  ------ General Options
% 39.50/5.48  
% 39.50/5.48  --fof                                   false
% 39.50/5.48  --time_out_real                         305.
% 39.50/5.48  --time_out_virtual                      -1.
% 39.50/5.48  --symbol_type_check                     false
% 39.50/5.48  --clausify_out                          false
% 39.50/5.48  --sig_cnt_out                           false
% 39.50/5.48  --trig_cnt_out                          false
% 39.50/5.48  --trig_cnt_out_tolerance                1.
% 39.50/5.48  --trig_cnt_out_sk_spl                   false
% 39.50/5.48  --abstr_cl_out                          false
% 39.50/5.48  
% 39.50/5.48  ------ Global Options
% 39.50/5.48  
% 39.50/5.48  --schedule                              default
% 39.50/5.48  --add_important_lit                     false
% 39.50/5.48  --prop_solver_per_cl                    1000
% 39.50/5.48  --min_unsat_core                        false
% 39.50/5.48  --soft_assumptions                      false
% 39.50/5.48  --soft_lemma_size                       3
% 39.50/5.48  --prop_impl_unit_size                   0
% 39.50/5.48  --prop_impl_unit                        []
% 39.50/5.48  --share_sel_clauses                     true
% 39.50/5.48  --reset_solvers                         false
% 39.50/5.48  --bc_imp_inh                            [conj_cone]
% 39.50/5.48  --conj_cone_tolerance                   3.
% 39.50/5.48  --extra_neg_conj                        none
% 39.50/5.48  --large_theory_mode                     true
% 39.50/5.48  --prolific_symb_bound                   200
% 39.50/5.48  --lt_threshold                          2000
% 39.50/5.48  --clause_weak_htbl                      true
% 39.50/5.48  --gc_record_bc_elim                     false
% 39.50/5.48  
% 39.50/5.48  ------ Preprocessing Options
% 39.50/5.48  
% 39.50/5.48  --preprocessing_flag                    true
% 39.50/5.48  --time_out_prep_mult                    0.1
% 39.50/5.48  --splitting_mode                        input
% 39.50/5.48  --splitting_grd                         true
% 39.50/5.48  --splitting_cvd                         false
% 39.50/5.48  --splitting_cvd_svl                     false
% 39.50/5.48  --splitting_nvd                         32
% 39.50/5.48  --sub_typing                            true
% 39.50/5.48  --prep_gs_sim                           true
% 39.50/5.48  --prep_unflatten                        true
% 39.50/5.48  --prep_res_sim                          true
% 39.50/5.48  --prep_upred                            true
% 39.50/5.48  --prep_sem_filter                       exhaustive
% 39.50/5.48  --prep_sem_filter_out                   false
% 39.50/5.48  --pred_elim                             true
% 39.50/5.48  --res_sim_input                         true
% 39.50/5.48  --eq_ax_congr_red                       true
% 39.50/5.48  --pure_diseq_elim                       true
% 39.50/5.48  --brand_transform                       false
% 39.50/5.48  --non_eq_to_eq                          false
% 39.50/5.48  --prep_def_merge                        true
% 39.50/5.48  --prep_def_merge_prop_impl              false
% 39.50/5.48  --prep_def_merge_mbd                    true
% 39.50/5.48  --prep_def_merge_tr_red                 false
% 39.50/5.48  --prep_def_merge_tr_cl                  false
% 39.50/5.48  --smt_preprocessing                     true
% 39.50/5.48  --smt_ac_axioms                         fast
% 39.50/5.48  --preprocessed_out                      false
% 39.50/5.48  --preprocessed_stats                    false
% 39.50/5.48  
% 39.50/5.48  ------ Abstraction refinement Options
% 39.50/5.48  
% 39.50/5.48  --abstr_ref                             []
% 39.50/5.48  --abstr_ref_prep                        false
% 39.50/5.48  --abstr_ref_until_sat                   false
% 39.50/5.48  --abstr_ref_sig_restrict                funpre
% 39.50/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.50/5.48  --abstr_ref_under                       []
% 39.50/5.48  
% 39.50/5.48  ------ SAT Options
% 39.50/5.48  
% 39.50/5.48  --sat_mode                              false
% 39.50/5.48  --sat_fm_restart_options                ""
% 39.50/5.48  --sat_gr_def                            false
% 39.50/5.48  --sat_epr_types                         true
% 39.50/5.48  --sat_non_cyclic_types                  false
% 39.50/5.48  --sat_finite_models                     false
% 39.50/5.48  --sat_fm_lemmas                         false
% 39.50/5.48  --sat_fm_prep                           false
% 39.50/5.48  --sat_fm_uc_incr                        true
% 39.50/5.48  --sat_out_model                         small
% 39.50/5.48  --sat_out_clauses                       false
% 39.50/5.48  
% 39.50/5.48  ------ QBF Options
% 39.50/5.48  
% 39.50/5.48  --qbf_mode                              false
% 39.50/5.48  --qbf_elim_univ                         false
% 39.50/5.48  --qbf_dom_inst                          none
% 39.50/5.48  --qbf_dom_pre_inst                      false
% 39.50/5.48  --qbf_sk_in                             false
% 39.50/5.48  --qbf_pred_elim                         true
% 39.50/5.48  --qbf_split                             512
% 39.50/5.48  
% 39.50/5.48  ------ BMC1 Options
% 39.50/5.48  
% 39.50/5.48  --bmc1_incremental                      false
% 39.50/5.48  --bmc1_axioms                           reachable_all
% 39.50/5.48  --bmc1_min_bound                        0
% 39.50/5.48  --bmc1_max_bound                        -1
% 39.50/5.48  --bmc1_max_bound_default                -1
% 39.50/5.48  --bmc1_symbol_reachability              true
% 39.50/5.48  --bmc1_property_lemmas                  false
% 39.50/5.48  --bmc1_k_induction                      false
% 39.50/5.48  --bmc1_non_equiv_states                 false
% 39.50/5.48  --bmc1_deadlock                         false
% 39.50/5.48  --bmc1_ucm                              false
% 39.50/5.48  --bmc1_add_unsat_core                   none
% 39.50/5.48  --bmc1_unsat_core_children              false
% 39.50/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.50/5.48  --bmc1_out_stat                         full
% 39.50/5.48  --bmc1_ground_init                      false
% 39.50/5.48  --bmc1_pre_inst_next_state              false
% 39.50/5.48  --bmc1_pre_inst_state                   false
% 39.50/5.48  --bmc1_pre_inst_reach_state             false
% 39.50/5.48  --bmc1_out_unsat_core                   false
% 39.50/5.48  --bmc1_aig_witness_out                  false
% 39.50/5.48  --bmc1_verbose                          false
% 39.50/5.48  --bmc1_dump_clauses_tptp                false
% 39.50/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.50/5.48  --bmc1_dump_file                        -
% 39.50/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.50/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.50/5.48  --bmc1_ucm_extend_mode                  1
% 39.50/5.48  --bmc1_ucm_init_mode                    2
% 39.50/5.48  --bmc1_ucm_cone_mode                    none
% 39.50/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.50/5.48  --bmc1_ucm_relax_model                  4
% 39.50/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.50/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.50/5.48  --bmc1_ucm_layered_model                none
% 39.50/5.48  --bmc1_ucm_max_lemma_size               10
% 39.50/5.48  
% 39.50/5.48  ------ AIG Options
% 39.50/5.48  
% 39.50/5.48  --aig_mode                              false
% 39.50/5.48  
% 39.50/5.48  ------ Instantiation Options
% 39.50/5.48  
% 39.50/5.48  --instantiation_flag                    false
% 39.50/5.48  --inst_sos_flag                         true
% 39.50/5.48  --inst_sos_phase                        true
% 39.50/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.50/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.50/5.48  --inst_lit_sel_side                     num_symb
% 39.50/5.48  --inst_solver_per_active                1400
% 39.50/5.48  --inst_solver_calls_frac                1.
% 39.50/5.48  --inst_passive_queue_type               priority_queues
% 39.50/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.50/5.48  --inst_passive_queues_freq              [25;2]
% 39.50/5.48  --inst_dismatching                      true
% 39.50/5.48  --inst_eager_unprocessed_to_passive     true
% 39.50/5.48  --inst_prop_sim_given                   true
% 39.50/5.48  --inst_prop_sim_new                     false
% 39.50/5.48  --inst_subs_new                         false
% 39.50/5.48  --inst_eq_res_simp                      false
% 39.50/5.48  --inst_subs_given                       false
% 39.50/5.48  --inst_orphan_elimination               true
% 39.50/5.48  --inst_learning_loop_flag               true
% 39.50/5.48  --inst_learning_start                   3000
% 39.50/5.48  --inst_learning_factor                  2
% 39.50/5.48  --inst_start_prop_sim_after_learn       3
% 39.50/5.48  --inst_sel_renew                        solver
% 39.50/5.48  --inst_lit_activity_flag                true
% 39.50/5.48  --inst_restr_to_given                   false
% 39.50/5.48  --inst_activity_threshold               500
% 39.50/5.48  --inst_out_proof                        true
% 39.50/5.48  
% 39.50/5.48  ------ Resolution Options
% 39.50/5.48  
% 39.50/5.48  --resolution_flag                       false
% 39.50/5.48  --res_lit_sel                           adaptive
% 39.50/5.48  --res_lit_sel_side                      none
% 39.50/5.48  --res_ordering                          kbo
% 39.50/5.48  --res_to_prop_solver                    active
% 39.50/5.48  --res_prop_simpl_new                    false
% 39.50/5.48  --res_prop_simpl_given                  true
% 39.50/5.48  --res_passive_queue_type                priority_queues
% 39.50/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.50/5.48  --res_passive_queues_freq               [15;5]
% 39.50/5.48  --res_forward_subs                      full
% 39.50/5.48  --res_backward_subs                     full
% 39.50/5.48  --res_forward_subs_resolution           true
% 39.50/5.48  --res_backward_subs_resolution          true
% 39.50/5.48  --res_orphan_elimination                true
% 39.50/5.48  --res_time_limit                        2.
% 39.50/5.48  --res_out_proof                         true
% 39.50/5.48  
% 39.50/5.48  ------ Superposition Options
% 39.50/5.48  
% 39.50/5.48  --superposition_flag                    true
% 39.50/5.48  --sup_passive_queue_type                priority_queues
% 39.50/5.48  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.50/5.48  --sup_passive_queues_freq               [8;1;4]
% 39.50/5.48  --demod_completeness_check              fast
% 39.50/5.48  --demod_use_ground                      true
% 39.50/5.48  --sup_to_prop_solver                    active
% 39.50/5.48  --sup_prop_simpl_new                    false
% 39.50/5.48  --sup_prop_simpl_given                  false
% 39.50/5.48  --sup_fun_splitting                     true
% 39.50/5.48  --sup_smt_interval                      10000
% 39.50/5.48  
% 39.50/5.48  ------ Superposition Simplification Setup
% 39.50/5.48  
% 39.50/5.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.50/5.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.50/5.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.50/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.50/5.48  --sup_full_triv                         [TrivRules]
% 39.50/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.50/5.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.50/5.48  --sup_immed_triv                        [TrivRules]
% 39.50/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.50/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.50/5.48  --sup_immed_bw_main                     []
% 39.50/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.50/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.50/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.50/5.48  --sup_input_bw                          [BwDemod;BwSubsumption]
% 39.50/5.48  
% 39.50/5.48  ------ Combination Options
% 39.50/5.48  
% 39.50/5.48  --comb_res_mult                         1
% 39.50/5.48  --comb_sup_mult                         1
% 39.50/5.48  --comb_inst_mult                        1000000
% 39.50/5.48  
% 39.50/5.48  ------ Debug Options
% 39.50/5.48  
% 39.50/5.48  --dbg_backtrace                         false
% 39.50/5.48  --dbg_dump_prop_clauses                 false
% 39.50/5.48  --dbg_dump_prop_clauses_file            -
% 39.50/5.48  --dbg_out_stat                          false
% 39.50/5.48  
% 39.50/5.48  
% 39.50/5.48  
% 39.50/5.48  
% 39.50/5.48  ------ Proving...
% 39.50/5.48  
% 39.50/5.48  
% 39.50/5.48  % SZS status Theorem for theBenchmark.p
% 39.50/5.48  
% 39.50/5.48   Resolution empty clause
% 39.50/5.48  
% 39.50/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 39.50/5.48  
% 39.50/5.48  fof(f1,axiom,(
% 39.50/5.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f20,plain,(
% 39.50/5.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.50/5.48    inference(cnf_transformation,[],[f1])).
% 39.50/5.48  
% 39.50/5.48  fof(f3,axiom,(
% 39.50/5.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f15,plain,(
% 39.50/5.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 39.50/5.48    inference(rectify,[],[f3])).
% 39.50/5.48  
% 39.50/5.48  fof(f22,plain,(
% 39.50/5.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 39.50/5.48    inference(cnf_transformation,[],[f15])).
% 39.50/5.48  
% 39.50/5.48  fof(f6,axiom,(
% 39.50/5.48    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f25,plain,(
% 39.50/5.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 39.50/5.48    inference(cnf_transformation,[],[f6])).
% 39.50/5.48  
% 39.50/5.48  fof(f8,axiom,(
% 39.50/5.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f27,plain,(
% 39.50/5.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 39.50/5.48    inference(cnf_transformation,[],[f8])).
% 39.50/5.48  
% 39.50/5.48  fof(f4,axiom,(
% 39.50/5.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f23,plain,(
% 39.50/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 39.50/5.48    inference(cnf_transformation,[],[f4])).
% 39.50/5.48  
% 39.50/5.48  fof(f35,plain,(
% 39.50/5.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 39.50/5.48    inference(definition_unfolding,[],[f27,f23,f23])).
% 39.50/5.48  
% 39.50/5.48  fof(f10,axiom,(
% 39.50/5.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f29,plain,(
% 39.50/5.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 39.50/5.48    inference(cnf_transformation,[],[f10])).
% 39.50/5.48  
% 39.50/5.48  fof(f2,axiom,(
% 39.50/5.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f21,plain,(
% 39.50/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 39.50/5.48    inference(cnf_transformation,[],[f2])).
% 39.50/5.48  
% 39.50/5.48  fof(f11,axiom,(
% 39.50/5.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f30,plain,(
% 39.50/5.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 39.50/5.48    inference(cnf_transformation,[],[f11])).
% 39.50/5.48  
% 39.50/5.48  fof(f7,axiom,(
% 39.50/5.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f16,plain,(
% 39.50/5.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.50/5.48    inference(ennf_transformation,[],[f7])).
% 39.50/5.48  
% 39.50/5.48  fof(f26,plain,(
% 39.50/5.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.50/5.48    inference(cnf_transformation,[],[f16])).
% 39.50/5.48  
% 39.50/5.48  fof(f13,conjecture,(
% 39.50/5.48    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f14,negated_conjecture,(
% 39.50/5.48    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 39.50/5.48    inference(negated_conjecture,[],[f13])).
% 39.50/5.48  
% 39.50/5.48  fof(f17,plain,(
% 39.50/5.48    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 39.50/5.48    inference(ennf_transformation,[],[f14])).
% 39.50/5.48  
% 39.50/5.48  fof(f18,plain,(
% 39.50/5.48    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 39.50/5.48    introduced(choice_axiom,[])).
% 39.50/5.48  
% 39.50/5.48  fof(f19,plain,(
% 39.50/5.48    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 39.50/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 39.50/5.48  
% 39.50/5.48  fof(f32,plain,(
% 39.50/5.48    r1_tarski(sK2,sK1)),
% 39.50/5.48    inference(cnf_transformation,[],[f19])).
% 39.50/5.48  
% 39.50/5.48  fof(f5,axiom,(
% 39.50/5.48    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f24,plain,(
% 39.50/5.48    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 39.50/5.48    inference(cnf_transformation,[],[f5])).
% 39.50/5.48  
% 39.50/5.48  fof(f9,axiom,(
% 39.50/5.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f28,plain,(
% 39.50/5.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.50/5.48    inference(cnf_transformation,[],[f9])).
% 39.50/5.48  
% 39.50/5.48  fof(f33,plain,(
% 39.50/5.48    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 39.50/5.48    inference(cnf_transformation,[],[f19])).
% 39.50/5.48  
% 39.50/5.48  fof(f12,axiom,(
% 39.50/5.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 39.50/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.48  
% 39.50/5.48  fof(f31,plain,(
% 39.50/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 39.50/5.48    inference(cnf_transformation,[],[f12])).
% 39.50/5.48  
% 39.50/5.48  fof(f34,plain,(
% 39.50/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 39.50/5.48    inference(definition_unfolding,[],[f31,f23])).
% 39.50/5.48  
% 39.50/5.48  fof(f36,plain,(
% 39.50/5.48    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),
% 39.50/5.48    inference(definition_unfolding,[],[f33,f23,f34,f23,f23])).
% 39.50/5.48  
% 39.50/5.48  cnf(c_0,plain,
% 39.50/5.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 39.50/5.48      inference(cnf_transformation,[],[f20]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_2,plain,
% 39.50/5.48      ( k3_xboole_0(X0,X0) = X0 ),
% 39.50/5.48      inference(cnf_transformation,[],[f22]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_4,plain,
% 39.50/5.48      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 39.50/5.48      inference(cnf_transformation,[],[f25]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_96,plain,
% 39.50/5.48      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_378,plain,
% 39.50/5.48      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_0,c_96]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_6,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 39.50/5.48      inference(cnf_transformation,[],[f35]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_8,plain,
% 39.50/5.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 39.50/5.48      inference(cnf_transformation,[],[f29]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_1,plain,
% 39.50/5.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 39.50/5.48      inference(cnf_transformation,[],[f21]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_57,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 39.50/5.48      inference(theory_normalisation,[status(thm)],[c_6,c_8,c_1,c_4,c_0]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_1611,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_378,c_57]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_9,plain,
% 39.50/5.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.50/5.48      inference(cnf_transformation,[],[f30]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_5,plain,
% 39.50/5.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 39.50/5.48      inference(cnf_transformation,[],[f26]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_11,negated_conjecture,
% 39.50/5.48      ( r1_tarski(sK2,sK1) ),
% 39.50/5.48      inference(cnf_transformation,[],[f32]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_46,plain,
% 39.50/5.48      ( k3_xboole_0(X0,X1) = X0 | sK1 != X1 | sK2 != X0 ),
% 39.50/5.48      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_47,plain,
% 39.50/5.48      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 39.50/5.48      inference(unflattening,[status(thm)],[c_46]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_90,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK2)) = k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_47,c_57]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_91,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK2)) = k3_xboole_0(X0,k5_xboole_0(sK2,sK2)) ),
% 39.50/5.48      inference(light_normalisation,[status(thm)],[c_90,c_47]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_92,plain,
% 39.50/5.48      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_91,c_9]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_3,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 39.50/5.48      inference(cnf_transformation,[],[f24]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_58,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 39.50/5.48      inference(theory_normalisation,[status(thm)],[c_3,c_8,c_1,c_4,c_0]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_272,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_0,c_58]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_274,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_2,c_58]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_1655,plain,
% 39.50/5.48      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0))) = k1_xboole_0 ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_1611,c_9,c_92,c_272,c_274]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_7204,plain,
% 39.50/5.48      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0)))) = k5_xboole_0(X0,k1_xboole_0) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_1655,c_274]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_7,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.50/5.48      inference(cnf_transformation,[],[f28]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_7335,plain,
% 39.50/5.48      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0)))) = X0 ),
% 39.50/5.48      inference(light_normalisation,[status(thm)],[c_7204,c_7]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_67,plain,
% 39.50/5.48      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_738,plain,
% 39.50/5.48      ( k3_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k3_xboole_0(X0,sK2) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_47,c_67]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_991,plain,
% 39.50/5.48      ( k3_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(X0,sK2) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_0,c_738]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_286,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k5_xboole_0(X0,X1)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_2,c_58]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_8633,plain,
% 39.50/5.48      ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK2,k3_xboole_0(sK1,X0))) = k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(sK1,X0)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_991,c_286]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_276,plain,
% 39.50/5.48      ( k5_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK1,k5_xboole_0(sK2,X0)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_47,c_58]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_97,plain,
% 39.50/5.48      ( k3_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK2,X0) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_47,c_4]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_277,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(k3_xboole_0(sK1,X0),X1)) = k3_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK2,X1)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_97,c_58]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_646,plain,
% 39.50/5.48      ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK2,k3_xboole_0(sK1,X0))) = k5_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(sK1,X0)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_2,c_277]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_666,plain,
% 39.50/5.48      ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,k5_xboole_0(sK2,X0))) = k5_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(sK1,X0)) ),
% 39.50/5.48      inference(light_normalisation,[status(thm)],[c_646,c_276]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_284,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_0,c_58]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_667,plain,
% 39.50/5.48      ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,k5_xboole_0(sK2,X0))) = k3_xboole_0(X0,k5_xboole_0(sK2,sK1)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_666,c_284]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_8804,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(sK1,X0)) = k3_xboole_0(X0,k5_xboole_0(sK2,sK1)) ),
% 39.50/5.48      inference(light_normalisation,[status(thm)],[c_8633,c_276,c_667]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_48906,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),sK2),sK1) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),k5_xboole_0(sK2,sK1)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_7335,c_8804]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_48912,plain,
% 39.50/5.48      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),sK2) = k3_xboole_0(sK2,sK1) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_7335,c_991]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_49110,plain,
% 39.50/5.48      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),sK2) = sK2 ),
% 39.50/5.48      inference(light_normalisation,[status(thm)],[c_48912,c_47]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_49116,plain,
% 39.50/5.48      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_48906,c_49110]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_51039,plain,
% 39.50/5.48      ( k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,k5_xboole_0(X0,sK1))),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_49116,c_286]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_142,plain,
% 39.50/5.48      ( k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_97,c_57]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_143,plain,
% 39.50/5.48      ( k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 39.50/5.48      inference(light_normalisation,[status(thm)],[c_142,c_47]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_148,plain,
% 39.50/5.48      ( k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_0,c_143]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_206,plain,
% 39.50/5.48      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_47,c_148]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_214,plain,
% 39.50/5.48      ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_206,c_2,c_9]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_222,plain,
% 39.50/5.48      ( k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_1,c_214]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_337,plain,
% 39.50/5.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(sK2,sK1),X0)) = k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,X0)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_222,c_58]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_76,plain,
% 39.50/5.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_351,plain,
% 39.50/5.48      ( k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,X0)) = k3_xboole_0(k5_xboole_0(sK2,sK1),X0) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_337,c_76]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_107,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_112,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_107,c_76]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_72,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_32284,plain,
% 39.50/5.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_112,c_72]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_430,plain,
% 39.50/5.48      ( k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_2,c_276]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_70,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_4637,plain,
% 39.50/5.48      ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(sK1,X1))) = k5_xboole_0(X0,k3_xboole_0(sK1,k5_xboole_0(sK2,X1))) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_276,c_70]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_5375,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK2,sK1))) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_430,c_4637]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_5491,plain,
% 39.50/5.48      ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK2,sK1))) = k5_xboole_0(X0,sK1) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_5375,c_2,c_112]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_36044,plain,
% 39.50/5.48      ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_9,c_5491]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_433,plain,
% 39.50/5.48      ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK2,X0)),X1) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_276,c_8]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_494,plain,
% 39.50/5.48      ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK1,sK1),X0)) = k5_xboole_0(k5_xboole_0(sK2,sK1),X0) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_430,c_433]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_523,plain,
% 39.50/5.48      ( k5_xboole_0(sK2,k5_xboole_0(sK1,X0)) = k5_xboole_0(k5_xboole_0(sK2,sK1),X0) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_494,c_2]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_36231,plain,
% 39.50/5.48      ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK1) = sK2 ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_36044,c_7,c_523]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_36258,plain,
% 39.50/5.48      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(X0,sK1)) = k5_xboole_0(X0,sK2) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_36231,c_70]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_51108,plain,
% 39.50/5.48      ( k3_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(X0,k5_xboole_0(X0,sK1))) = k1_xboole_0 ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_51039,c_9,c_351,c_32284,c_36258]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_10,negated_conjecture,
% 39.50/5.48      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
% 39.50/5.48      inference(cnf_transformation,[],[f36]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_56,negated_conjecture,
% 39.50/5.48      ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(theory_normalisation,[status(thm)],[c_10,c_8,c_1,c_4,c_0]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_66,plain,
% 39.50/5.48      ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(light_normalisation,[status(thm)],[c_56,c_47]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_73,plain,
% 39.50/5.48      ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_0,c_66]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_74,plain,
% 39.50/5.48      ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_73,c_57]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_75,plain,
% 39.50/5.48      ( k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_1,c_74]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_6890,plain,
% 39.50/5.48      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_75,c_272,c_274]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_4629,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_9,c_70]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_4680,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_4629,c_7]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_5733,plain,
% 39.50/5.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
% 39.50/5.48      inference(superposition,[status(thm)],[c_4680,c_72]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_6891,plain,
% 39.50/5.48      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_6890,c_5733]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_6892,plain,
% 39.50/5.48      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_6891,c_274]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_125537,plain,
% 39.50/5.48      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_51108,c_6892]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_125538,plain,
% 39.50/5.48      ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
% 39.50/5.48      inference(demodulation,[status(thm)],[c_125537,c_76]) ).
% 39.50/5.48  
% 39.50/5.48  cnf(c_125539,plain,
% 39.50/5.48      ( $false ),
% 39.50/5.48      inference(equality_resolution_simp,[status(thm)],[c_125538]) ).
% 39.50/5.48  
% 39.50/5.48  
% 39.50/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 39.50/5.48  
% 39.50/5.48  ------                               Statistics
% 39.50/5.48  
% 39.50/5.48  ------ General
% 39.50/5.48  
% 39.50/5.48  abstr_ref_over_cycles:                  0
% 39.50/5.48  abstr_ref_under_cycles:                 0
% 39.50/5.48  gc_basic_clause_elim:                   0
% 39.50/5.48  forced_gc_time:                         0
% 39.50/5.48  parsing_time:                           0.007
% 39.50/5.48  unif_index_cands_time:                  0.
% 39.50/5.48  unif_index_add_time:                    0.
% 39.50/5.48  orderings_time:                         0.
% 39.50/5.48  out_proof_time:                         0.007
% 39.50/5.48  total_time:                             4.944
% 39.50/5.48  num_of_symbols:                         38
% 39.50/5.48  num_of_terms:                           302354
% 39.50/5.48  
% 39.50/5.48  ------ Preprocessing
% 39.50/5.48  
% 39.50/5.48  num_of_splits:                          0
% 39.50/5.48  num_of_split_atoms:                     0
% 39.50/5.48  num_of_reused_defs:                     0
% 39.50/5.48  num_eq_ax_congr_red:                    0
% 39.50/5.48  num_of_sem_filtered_clauses:            0
% 39.50/5.48  num_of_subtypes:                        0
% 39.50/5.48  monotx_restored_types:                  0
% 39.50/5.48  sat_num_of_epr_types:                   0
% 39.50/5.48  sat_num_of_non_cyclic_types:            0
% 39.50/5.48  sat_guarded_non_collapsed_types:        0
% 39.50/5.48  num_pure_diseq_elim:                    0
% 39.50/5.48  simp_replaced_by:                       0
% 39.50/5.48  res_preprocessed:                       38
% 39.50/5.48  prep_upred:                             0
% 39.50/5.48  prep_unflattend:                        2
% 39.50/5.48  smt_new_axioms:                         0
% 39.50/5.48  pred_elim_cands:                        0
% 39.50/5.48  pred_elim:                              1
% 39.50/5.48  pred_elim_cl:                           1
% 39.50/5.48  pred_elim_cycles:                       2
% 39.50/5.48  merged_defs:                            0
% 39.50/5.48  merged_defs_ncl:                        0
% 39.50/5.48  bin_hyper_res:                          0
% 39.50/5.48  prep_cycles:                            3
% 39.50/5.48  pred_elim_time:                         0.
% 39.50/5.48  splitting_time:                         0.
% 39.50/5.48  sem_filter_time:                        0.
% 39.50/5.48  monotx_time:                            0.
% 39.50/5.48  subtype_inf_time:                       0.
% 39.50/5.48  
% 39.50/5.48  ------ Problem properties
% 39.50/5.48  
% 39.50/5.48  clauses:                                11
% 39.50/5.48  conjectures:                            1
% 39.50/5.48  epr:                                    0
% 39.50/5.48  horn:                                   11
% 39.50/5.48  ground:                                 2
% 39.50/5.48  unary:                                  11
% 39.50/5.48  binary:                                 0
% 39.50/5.48  lits:                                   11
% 39.50/5.48  lits_eq:                                11
% 39.50/5.48  fd_pure:                                0
% 39.50/5.48  fd_pseudo:                              0
% 39.50/5.48  fd_cond:                                0
% 39.50/5.48  fd_pseudo_cond:                         0
% 39.50/5.48  ac_symbols:                             2
% 39.50/5.48  
% 39.50/5.48  ------ Propositional Solver
% 39.50/5.48  
% 39.50/5.48  prop_solver_calls:                      17
% 39.50/5.48  prop_fast_solver_calls:                 91
% 39.50/5.48  smt_solver_calls:                       0
% 39.50/5.48  smt_fast_solver_calls:                  0
% 39.50/5.48  prop_num_of_clauses:                    741
% 39.50/5.48  prop_preprocess_simplified:             529
% 39.50/5.48  prop_fo_subsumed:                       0
% 39.50/5.48  prop_solver_time:                       0.
% 39.50/5.48  smt_solver_time:                        0.
% 39.50/5.48  smt_fast_solver_time:                   0.
% 39.50/5.48  prop_fast_solver_time:                  0.
% 39.50/5.48  prop_unsat_core_time:                   0.
% 39.50/5.48  
% 39.50/5.48  ------ QBF
% 39.50/5.48  
% 39.50/5.48  qbf_q_res:                              0
% 39.50/5.48  qbf_num_tautologies:                    0
% 39.50/5.48  qbf_prep_cycles:                        0
% 39.50/5.48  
% 39.50/5.48  ------ BMC1
% 39.50/5.48  
% 39.50/5.48  bmc1_current_bound:                     -1
% 39.50/5.48  bmc1_last_solved_bound:                 -1
% 39.50/5.48  bmc1_unsat_core_size:                   -1
% 39.50/5.48  bmc1_unsat_core_parents_size:           -1
% 39.50/5.48  bmc1_merge_next_fun:                    0
% 39.50/5.48  bmc1_unsat_core_clauses_time:           0.
% 39.50/5.48  
% 39.50/5.48  ------ Instantiation
% 39.50/5.48  
% 39.50/5.48  inst_num_of_clauses:                    0
% 39.50/5.48  inst_num_in_passive:                    0
% 39.50/5.48  inst_num_in_active:                     0
% 39.50/5.48  inst_num_in_unprocessed:                0
% 39.50/5.48  inst_num_of_loops:                      0
% 39.50/5.48  inst_num_of_learning_restarts:          0
% 39.50/5.48  inst_num_moves_active_passive:          0
% 39.50/5.48  inst_lit_activity:                      0
% 39.50/5.48  inst_lit_activity_moves:                0
% 39.50/5.48  inst_num_tautologies:                   0
% 39.50/5.48  inst_num_prop_implied:                  0
% 39.50/5.48  inst_num_existing_simplified:           0
% 39.50/5.48  inst_num_eq_res_simplified:             0
% 39.50/5.48  inst_num_child_elim:                    0
% 39.50/5.48  inst_num_of_dismatching_blockings:      0
% 39.50/5.48  inst_num_of_non_proper_insts:           0
% 39.50/5.48  inst_num_of_duplicates:                 0
% 39.50/5.48  inst_inst_num_from_inst_to_res:         0
% 39.50/5.48  inst_dismatching_checking_time:         0.
% 39.50/5.48  
% 39.50/5.48  ------ Resolution
% 39.50/5.48  
% 39.50/5.48  res_num_of_clauses:                     0
% 39.50/5.48  res_num_in_passive:                     0
% 39.50/5.48  res_num_in_active:                      0
% 39.50/5.48  res_num_of_loops:                       41
% 39.50/5.48  res_forward_subset_subsumed:            0
% 39.50/5.48  res_backward_subset_subsumed:           0
% 39.50/5.48  res_forward_subsumed:                   0
% 39.50/5.48  res_backward_subsumed:                  0
% 39.50/5.48  res_forward_subsumption_resolution:     0
% 39.50/5.48  res_backward_subsumption_resolution:    0
% 39.50/5.48  res_clause_to_clause_subsumption:       187979
% 39.50/5.48  res_orphan_elimination:                 0
% 39.50/5.48  res_tautology_del:                      0
% 39.50/5.48  res_num_eq_res_simplified:              0
% 39.50/5.48  res_num_sel_changes:                    0
% 39.50/5.48  res_moves_from_active_to_pass:          0
% 39.50/5.48  
% 39.50/5.48  ------ Superposition
% 39.50/5.48  
% 39.50/5.48  sup_time_total:                         0.
% 39.50/5.48  sup_time_generating:                    0.
% 39.50/5.48  sup_time_sim_full:                      0.
% 39.50/5.48  sup_time_sim_immed:                     0.
% 39.50/5.48  
% 39.50/5.48  sup_num_of_clauses:                     13657
% 39.50/5.48  sup_num_in_active:                      344
% 39.50/5.48  sup_num_in_passive:                     13313
% 39.50/5.48  sup_num_of_loops:                       379
% 39.50/5.48  sup_fw_superposition:                   30536
% 39.50/5.48  sup_bw_superposition:                   24278
% 39.50/5.48  sup_immediate_simplified:               43949
% 39.50/5.48  sup_given_eliminated:                   16
% 39.50/5.48  comparisons_done:                       0
% 39.50/5.48  comparisons_avoided:                    0
% 39.50/5.48  
% 39.50/5.48  ------ Simplifications
% 39.50/5.48  
% 39.50/5.48  
% 39.50/5.48  sim_fw_subset_subsumed:                 0
% 39.50/5.48  sim_bw_subset_subsumed:                 0
% 39.50/5.48  sim_fw_subsumed:                        2323
% 39.50/5.48  sim_bw_subsumed:                        172
% 39.50/5.48  sim_fw_subsumption_res:                 0
% 39.50/5.48  sim_bw_subsumption_res:                 0
% 39.50/5.48  sim_tautology_del:                      0
% 39.50/5.48  sim_eq_tautology_del:                   14084
% 39.50/5.48  sim_eq_res_simp:                        0
% 39.50/5.48  sim_fw_demodulated:                     47244
% 39.50/5.48  sim_bw_demodulated:                     619
% 39.50/5.48  sim_light_normalised:                   22406
% 39.50/5.48  sim_joinable_taut:                      552
% 39.50/5.48  sim_joinable_simp:                      0
% 39.50/5.48  sim_ac_normalised:                      0
% 39.50/5.48  sim_smt_subsumption:                    0
% 39.50/5.48  
%------------------------------------------------------------------------------
