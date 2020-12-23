%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:45 EST 2020

% Result     : CounterSatisfiable 51.21s
% Output     : Saturation 51.21s
% Verified   : 
% Statistics : Number of formulae       :  511 (636635 expanded)
%              Number of clauses        :  479 (163584 expanded)
%              Number of leaves         :   13 (199961 expanded)
%              Depth                    :   29
%              Number of atoms          :  553 (637109 expanded)
%              Number of equality atoms :  514 (636758 expanded)
%              Maximal formula depth    :    9 (   1 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f24,f24])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,
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

fof(f17,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).

fof(f27,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_64,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_63,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_58,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_103,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_194,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_103])).

cnf(c_226,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_194,c_103])).

cnf(c_441,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_226])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_94,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_108,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_94,c_5])).

cnf(c_207,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_108,c_103])).

cnf(c_218,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_207,c_3])).

cnf(c_277,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_94,c_218])).

cnf(c_965,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_441,c_277])).

cnf(c_202,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_94,c_103])).

cnf(c_220,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_202,c_108])).

cnf(c_221,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_220,c_3])).

cnf(c_250,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_94,c_221])).

cnf(c_602,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_226,c_250])).

cnf(c_213,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_103,c_103])).

cnf(c_707,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_213])).

cnf(c_1001,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_965,c_602,c_707])).

cnf(c_111,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_123,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_111,c_3])).

cnf(c_475,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_226,c_123])).

cnf(c_1798,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_475])).

cnf(c_668,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1,c_213])).

cnf(c_1164,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_668,c_441])).

cnf(c_4060,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1798,c_1164])).

cnf(c_1163,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_668,c_226])).

cnf(c_4087,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),X1) ),
    inference(superposition,[status(thm)],[c_1163,c_1164])).

cnf(c_929,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_103,c_441])).

cnf(c_1033,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_929,c_707])).

cnf(c_942,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_213,c_441])).

cnf(c_1018,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),X0) ),
    inference(demodulation,[status(thm)],[c_942,c_213,c_707])).

cnf(c_1034,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_1033,c_1018])).

cnf(c_3909,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1163,c_1798])).

cnf(c_4262,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_4087,c_1034,c_3909])).

cnf(c_4280,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(demodulation,[status(thm)],[c_4060,c_4262])).

cnf(c_476,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_226,c_94])).

cnf(c_3085,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1798,c_476])).

cnf(c_3135,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_3085,c_1798])).

cnf(c_4281,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_4280,c_1798,c_3135])).

cnf(c_478,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_226,c_277])).

cnf(c_515,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_226,c_478])).

cnf(c_529,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_515,c_226])).

cnf(c_2374,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_476,c_529])).

cnf(c_4282,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_4281,c_2374])).

cnf(c_105362,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1001,c_4282])).

cnf(c_473,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_226,c_218])).

cnf(c_479,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_473,c_226])).

cnf(c_2649,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_479])).

cnf(c_29630,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_476,c_2649])).

cnf(c_104028,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1001,c_29630])).

cnf(c_2427,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_529])).

cnf(c_3485,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2427,c_5])).

cnf(c_3493,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2427,c_475])).

cnf(c_3504,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_3485,c_2427,c_3493])).

cnf(c_91516,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_3504,c_226])).

cnf(c_91620,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(demodulation,[status(thm)],[c_91516,c_3504])).

cnf(c_964,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_441,c_478])).

cnf(c_1002,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_964,c_707])).

cnf(c_44986,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1002,c_1])).

cnf(c_14270,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1798,c_2374])).

cnf(c_14513,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_14270,c_2374])).

cnf(c_14514,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_14513,c_1033,c_1798])).

cnf(c_45010,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_44986,c_3909,c_14514])).

cnf(c_970,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_441,c_94])).

cnf(c_9133,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_970,c_226])).

cnf(c_474,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_226,c_108])).

cnf(c_1662,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_441,c_474])).

cnf(c_1700,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_1662,c_474])).

cnf(c_1155,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_668,c_478])).

cnf(c_1168,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_1155,c_668])).

cnf(c_1369,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_707,c_108])).

cnf(c_1701,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_1700,c_707,c_1168,c_1369])).

cnf(c_5597,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1701,c_5])).

cnf(c_270,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_94,c_218])).

cnf(c_7103,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_5597,c_270])).

cnf(c_471,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_226,c_277])).

cnf(c_480,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_471,c_226])).

cnf(c_5853,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1164,c_480])).

cnf(c_972,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_441,c_226])).

cnf(c_5886,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_972,c_480])).

cnf(c_3908,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1163,c_2427])).

cnf(c_3887,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1163,c_475])).

cnf(c_3938,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_3887,c_3908])).

cnf(c_5974,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_5886,c_3908,c_3938])).

cnf(c_6010,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_5853,c_480,c_5974])).

cnf(c_1151,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_668,c_103])).

cnf(c_1169,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_1151,c_668])).

cnf(c_983,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_441,c_1])).

cnf(c_984,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_983,c_5])).

cnf(c_985,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_984,c_707])).

cnf(c_978,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_441,c_5])).

cnf(c_992,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_978,c_707])).

cnf(c_1170,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_1169,c_707,c_985,c_992])).

cnf(c_4440,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1170,c_529])).

cnf(c_4466,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1170,c_2427])).

cnf(c_4499,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_4440,c_4466])).

cnf(c_4145,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1164,c_529])).

cnf(c_4170,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1164,c_529])).

cnf(c_4197,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_4145,c_4170])).

cnf(c_619,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_250,c_226])).

cnf(c_644,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_226,c_619])).

cnf(c_4198,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_4197,c_644])).

cnf(c_4500,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_4499,c_4198])).

cnf(c_6011,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_6010,c_4500])).

cnf(c_7232,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_7103,c_6011])).

cnf(c_9186,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_9133,c_7232])).

cnf(c_74267,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9186,c_441])).

cnf(c_4132,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1164,c_1798])).

cnf(c_74449,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_74267,c_4132,c_9186,c_14514,c_45010])).

cnf(c_91621,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_91620,c_45010,c_74449])).

cnf(c_3491,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2427,c_529])).

cnf(c_3497,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_3491,c_2427])).

cnf(c_87579,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_476,c_3497])).

cnf(c_1828,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_441,c_475])).

cnf(c_1886,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_1828,c_1002])).

cnf(c_1887,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_1886,c_707])).

cnf(c_83031,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_1887,c_1002])).

cnf(c_83456,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(demodulation,[status(thm)],[c_83031,c_1887])).

cnf(c_1371,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_707,c_94])).

cnf(c_1162,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_668,c_221])).

cnf(c_1165,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1162,c_3])).

cnf(c_1220,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_668,c_1165])).

cnf(c_1965,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_668,c_476])).

cnf(c_1827,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_668,c_475])).

cnf(c_1363,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_707,c_250])).

cnf(c_1888,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_1827,c_1168,c_1363])).

cnf(c_2099,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) ),
    inference(light_normalisation,[status(thm)],[c_1965,c_1888])).

cnf(c_2100,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_2099,c_5,c_1168])).

cnf(c_23781,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))))) ),
    inference(superposition,[status(thm)],[c_1220,c_2100])).

cnf(c_3867,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1163,c_479])).

cnf(c_1226,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1165,c_441])).

cnf(c_1249,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1226,c_108,c_218,c_277])).

cnf(c_1493,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1249,c_226])).

cnf(c_9606,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1001,c_1493])).

cnf(c_15554,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9606,c_9606])).

cnf(c_5893,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1798,c_480])).

cnf(c_5963,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(light_normalisation,[status(thm)],[c_5893,c_4262])).

cnf(c_5964,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_5963,c_1033,c_3504])).

cnf(c_15672,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_9606,c_5964])).

cnf(c_15594,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) ),
    inference(superposition,[status(thm)],[c_9606,c_644])).

cnf(c_15783,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) ),
    inference(demodulation,[status(thm)],[c_15594,c_15672])).

cnf(c_9654,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1001,c_226])).

cnf(c_9717,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_9654,c_7232])).

cnf(c_15784,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) ),
    inference(light_normalisation,[status(thm)],[c_15783,c_9717])).

cnf(c_14271,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_2427,c_2374])).

cnf(c_14510,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_14271,c_2374])).

cnf(c_14511,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_14510,c_9717])).

cnf(c_14512,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_14511,c_4282,c_9186])).

cnf(c_15785,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_15784,c_474,c_14512])).

cnf(c_15574,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
    inference(superposition,[status(thm)],[c_9606,c_1])).

cnf(c_3846,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1163,c_475])).

cnf(c_3868,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1163,c_529])).

cnf(c_3961,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_3846,c_3868])).

cnf(c_15817,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_15574,c_1369,c_3961])).

cnf(c_15862,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_15554,c_15672,c_15785,c_15817])).

cnf(c_1159,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_668,c_108])).

cnf(c_512,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_94,c_478])).

cnf(c_3018,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_512,c_1798])).

cnf(c_294,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_218,c_103])).

cnf(c_297,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_294,c_250])).

cnf(c_298,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_297,c_221])).

cnf(c_3210,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_3018,c_3,c_298])).

cnf(c_10047,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_1159,c_3210])).

cnf(c_10050,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_1159,c_270])).

cnf(c_10066,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_10050,c_7232])).

cnf(c_10069,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_10047,c_10066])).

cnf(c_15863,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_15862,c_3,c_10069])).

cnf(c_23852,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) ),
    inference(light_normalisation,[status(thm)],[c_23781,c_1369,c_3867,c_15863])).

cnf(c_8180,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
    inference(superposition,[status(thm)],[c_1164,c_644])).

cnf(c_8379,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
    inference(demodulation,[status(thm)],[c_8180,c_644])).

cnf(c_4107,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1164,c_529])).

cnf(c_4109,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
    inference(superposition,[status(thm)],[c_1164,c_476])).

cnf(c_4233,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_4109,c_1369])).

cnf(c_4234,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_4107,c_4170,c_4233])).

cnf(c_8380,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_8379,c_1369,c_4234])).

cnf(c_23853,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_23852,c_5,c_8380])).

cnf(c_50478,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_1371,c_23853])).

cnf(c_62223,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_985,c_4170])).

cnf(c_4153,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1164,c_668])).

cnf(c_4190,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_4153,c_5,c_1798,c_1888])).

cnf(c_10341,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_1369,c_668])).

cnf(c_1361,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_707,c_1165])).

cnf(c_4169,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1164,c_479])).

cnf(c_10385,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_10341,c_1361,c_4169,c_7232])).

cnf(c_16317,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_10385,c_476])).

cnf(c_1219,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_226,c_1165])).

cnf(c_4443,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1170,c_475])).

cnf(c_4497,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_4443,c_4466])).

cnf(c_16596,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_16317,c_5,c_1219,c_4497])).

cnf(c_4163,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X0) ),
    inference(superposition,[status(thm)],[c_1164,c_972])).

cnf(c_4183,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_4163,c_5,c_1033,c_1798])).

cnf(c_41205,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_16596,c_4183])).

cnf(c_41241,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(demodulation,[status(thm)],[c_41205,c_16596])).

cnf(c_9616,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) ),
    inference(superposition,[status(thm)],[c_1001,c_644])).

cnf(c_9157,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_970,c_529])).

cnf(c_9744,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
    inference(light_normalisation,[status(thm)],[c_9616,c_9157])).

cnf(c_5640,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1701,c_479])).

cnf(c_9745,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_9744,c_1369,c_5640])).

cnf(c_10736,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1371,c_1493])).

cnf(c_17022,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_10736,c_476])).

cnf(c_10737,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1371,c_479])).

cnf(c_17293,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) ),
    inference(light_normalisation,[status(thm)],[c_17022,c_10737,c_15672])).

cnf(c_17294,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_17293,c_1369,c_10737])).

cnf(c_1966,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_441,c_476])).

cnf(c_2097,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) ),
    inference(light_normalisation,[status(thm)],[c_1966,c_1888])).

cnf(c_2098,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_2097,c_5,c_1002])).

cnf(c_19757,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))))) ),
    inference(superposition,[status(thm)],[c_1798,c_2098])).

cnf(c_20402,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) ),
    inference(light_normalisation,[status(thm)],[c_19757,c_1798,c_9186,c_9717,c_14514,c_15785])).

cnf(c_15552,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9606,c_5])).

cnf(c_15864,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_15552,c_15672,c_15817])).

cnf(c_20403,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_20402,c_474,c_15864])).

cnf(c_29472,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1001,c_2649])).

cnf(c_41242,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_41241,c_9745,c_17294,c_20403,c_29472])).

cnf(c_62773,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_62223,c_992,c_4190,c_9186,c_41242])).

cnf(c_4467,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1170,c_1798])).

cnf(c_72924,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_4467,c_5974])).

cnf(c_73524,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_72924,c_992,c_9186,c_14514,c_45010])).

cnf(c_83457,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_83456,c_50478,c_62773,c_73524])).

cnf(c_1111,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_668])).

cnf(c_1200,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),X0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_1111,c_668])).

cnf(c_1201,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_1200,c_475])).

cnf(c_83175,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_1887,c_1201])).

cnf(c_83216,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(demodulation,[status(thm)],[c_83175,c_1887])).

cnf(c_83217,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_83216,c_50478,c_73524])).

cnf(c_83176,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1887,c_1170])).

cnf(c_83214,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(demodulation,[status(thm)],[c_83176,c_1887])).

cnf(c_83215,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_83214,c_10066,c_50478,c_73524])).

cnf(c_82763,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1001,c_1887])).

cnf(c_82764,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1170,c_1887])).

cnf(c_44478,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_9606,c_1002])).

cnf(c_45709,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_44478,c_15672])).

cnf(c_77823,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4170,c_45709])).

cnf(c_1365,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_707,c_478])).

cnf(c_1378,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_1365,c_707])).

cnf(c_47433,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1378,c_4183])).

cnf(c_47474,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(demodulation,[status(thm)],[c_47433,c_1378])).

cnf(c_47475,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_47474,c_1798,c_10066,c_14514,c_45010])).

cnf(c_74191,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) ),
    inference(superposition,[status(thm)],[c_9186,c_3909])).

cnf(c_74548,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_74191,c_4132,c_9186,c_14514,c_45010])).

cnf(c_78588,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_77823,c_1798,c_9186,c_9717,c_14514,c_47475,c_50478,c_74548])).

cnf(c_77824,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1378,c_45709])).

cnf(c_78587,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_77824,c_1798,c_9186,c_9717,c_10066,c_14514,c_47475,c_74548])).

cnf(c_3061,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_707,c_1798])).

cnf(c_3166,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(demodulation,[status(thm)],[c_3061,c_1798,c_3135])).

cnf(c_3167,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(light_normalisation,[status(thm)],[c_3166,c_1888])).

cnf(c_156,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_94,c_123])).

cnf(c_3168,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_3167,c_156])).

cnf(c_72968,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_3168,c_5974])).

cnf(c_73452,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_72968,c_3168,c_9186,c_14514,c_62773])).

cnf(c_3064,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_213,c_1798])).

cnf(c_3160,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(demodulation,[status(thm)],[c_3064,c_1798,c_3135])).

cnf(c_3161,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(light_normalisation,[status(thm)],[c_3160,c_1888])).

cnf(c_3162,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3161,c_156])).

cnf(c_72969,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3162,c_5974])).

cnf(c_45732,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1001,c_1168])).

cnf(c_73451,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_72969,c_3168,c_4190,c_14514,c_45732,c_62773])).

cnf(c_73151,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_5974,c_4183])).

cnf(c_73201,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(demodulation,[status(thm)],[c_73151,c_5974])).

cnf(c_73202,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_73201,c_4132,c_14514,c_17294,c_62773])).

cnf(c_956,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_441,c_226])).

cnf(c_962,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_441,c_250])).

cnf(c_1005,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_956,c_962])).

cnf(c_1006,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_1005,c_707])).

cnf(c_2579,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_476,c_479])).

cnf(c_70413,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1006,c_2579])).

cnf(c_70803,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(demodulation,[status(thm)],[c_70413,c_1006])).

cnf(c_62308,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
    inference(superposition,[status(thm)],[c_4170,c_3909])).

cnf(c_62642,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_62308,c_1798,c_9186,c_14514,c_50478])).

cnf(c_70804,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_70803,c_7232,c_45732,c_62642])).

cnf(c_10825,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1371,c_1798])).

cnf(c_67795,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10825,c_103])).

cnf(c_62222,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4467,c_4170])).

cnf(c_62774,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_62222,c_992,c_9186,c_14514,c_45010])).

cnf(c_62432,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_4170,c_972])).

cnf(c_62469,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_62432,c_1798,c_9186,c_14514,c_50478])).

cnf(c_50910,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_23853,c_1002])).

cnf(c_37173,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
    inference(superposition,[status(thm)],[c_10736,c_4467])).

cnf(c_37964,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_37173,c_1369,c_15863,c_29630])).

cnf(c_51193,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_50910,c_7232,c_9745,c_29472,c_37964])).

cnf(c_9087,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_970,c_1493])).

cnf(c_14947,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_9087,c_5964])).

cnf(c_46068,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_14947,c_1168])).

cnf(c_46534,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_46068,c_45010])).

cnf(c_46535,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_46534,c_2374,c_9186])).

cnf(c_46536,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_46535,c_9186])).

cnf(c_45729,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_1164,c_1168])).

cnf(c_44944,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1002,c_5])).

cnf(c_45098,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_44944,c_1002,c_45010])).

cnf(c_44480,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_970,c_1002])).

cnf(c_5093,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_2427,c_1493])).

cnf(c_5304,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_5093,c_4500])).

cnf(c_3805,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_2427,c_1163])).

cnf(c_3998,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(demodulation,[status(thm)],[c_3805,c_3961])).

cnf(c_2304,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_707,c_298])).

cnf(c_3999,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_3998,c_1798,c_2304,c_3135])).

cnf(c_5305,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_5304,c_3,c_5,c_3999])).

cnf(c_30464,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1164,c_5305])).

cnf(c_30292,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_9606,c_5305])).

cnf(c_31396,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_30292,c_15672])).

cnf(c_29473,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1170,c_2649])).

cnf(c_5030,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_441,c_1493])).

cnf(c_5362,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_5030,c_4190])).

cnf(c_5363,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_5362,c_3,c_5,c_4233])).

cnf(c_21737,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_5363,c_226])).

cnf(c_21815,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(demodulation,[status(thm)],[c_21737,c_5363])).

cnf(c_9123,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_970,c_475])).

cnf(c_9192,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_9123,c_9157])).

cnf(c_21816,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_21815,c_7232,c_9192])).

cnf(c_20005,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_2098,c_1])).

cnf(c_20032,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_20005,c_3909,c_14514])).

cnf(c_17839,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14947,c_10385])).

cnf(c_15619,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_9606,c_529])).

cnf(c_15757,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_15619,c_15672])).

cnf(c_15758,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_15757,c_9186,c_9717])).

cnf(c_14817,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_9087,c_476])).

cnf(c_9088,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_970,c_479])).

cnf(c_15120,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_14817,c_5,c_1219,c_9088])).

cnf(c_14937,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9087,c_1493])).

cnf(c_9147,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_970,c_441])).

cnf(c_9174,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_9147,c_5,c_3168,c_4190])).

cnf(c_13621,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_9174,c_226])).

cnf(c_13717,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_13621,c_9174])).

cnf(c_13718,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_13717,c_7232,c_9157])).

cnf(c_968,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_441,c_108])).

cnf(c_8618,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k1_xboole_0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_968,c_1219])).

cnf(c_8703,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(demodulation,[status(thm)],[c_8618,c_3,c_5,c_1219])).

cnf(c_12794,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_476,c_8703])).

cnf(c_10776,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1371,c_529])).

cnf(c_5012,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_441,c_1493])).

cnf(c_5383,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_5012,c_4190])).

cnf(c_5384,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_5383,c_3,c_474,c_2374])).

cnf(c_10875,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_10776,c_5384,c_9717])).

cnf(c_9156,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_970,c_479])).

cnf(c_9152,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_970,c_480])).

cnf(c_368,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) ),
    inference(superposition,[status(thm)],[c_156,c_103])).

cnf(c_380,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_368,c_298])).

cnf(c_8600,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) ),
    inference(superposition,[status(thm)],[c_968,c_380])).

cnf(c_2306,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_441,c_298])).

cnf(c_8715,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_8600,c_474,c_2306])).

cnf(c_8617,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_968,c_1493])).

cnf(c_8704,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8617,c_3,c_5])).

cnf(c_7100,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_5597,c_3210])).

cnf(c_7238,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_7100,c_7232])).

cnf(c_7123,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5597,c_1493])).

cnf(c_7120,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5597,c_1493])).

cnf(c_5575,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1701,c_1493])).

cnf(c_5685,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_5575,c_3,c_5])).

cnf(c_6208,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5685,c_529])).

cnf(c_6292,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_6208,c_3])).

cnf(c_6216,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0),k1_xboole_0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_5685,c_1219])).

cnf(c_6289,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(demodulation,[status(thm)],[c_6216,c_3,c_5,c_1219])).

cnf(c_6209,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5685,c_475])).

cnf(c_5826,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_972,c_480])).

cnf(c_5817,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1164,c_480])).

cnf(c_5618,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_1701,c_298])).

cnf(c_5648,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_5618,c_4190])).

cnf(c_5625,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1701,c_218])).

cnf(c_5645,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_5625,c_4190])).

cnf(c_5626,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1701,c_221])).

cnf(c_5586,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1701,c_476])).

cnf(c_4749,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) ),
    inference(superposition,[status(thm)],[c_1164,c_1219])).

cnf(c_4929,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4749,c_4500])).

cnf(c_4930,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_4929,c_3,c_474])).

cnf(c_4148,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1164,c_475])).

cnf(c_4194,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_4148,c_4170])).

cnf(c_3697,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_972,c_529])).

cnf(c_3721,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_972,c_529])).

cnf(c_3700,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_972,c_475])).

cnf(c_3741,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_3700,c_3721])).

cnf(c_3744,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_3697,c_3721,c_3741])).

cnf(c_3720,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_972,c_479])).

cnf(c_3480,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2427,c_441])).

cnf(c_3508,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_3480,c_3493,c_3504])).

cnf(c_3509,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_3508,c_1798,c_3135])).

cnf(c_3078,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1798,c_1798])).

cnf(c_3138,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_3078,c_3135])).

cnf(c_2681,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_668,c_479])).

cnf(c_2764,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_2681,c_1369,c_2100])).

cnf(c_2765,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_2764,c_270,c_619])).

cnf(c_3139,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_3138,c_2304,c_2427,c_2765])).

cnf(c_3095,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1798,c_213])).

cnf(c_3126,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(demodulation,[status(thm)],[c_3095,c_1798])).

cnf(c_3127,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_3126,c_213,c_1363,c_2427])).

cnf(c_3142,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_3139,c_3127])).

cnf(c_3093,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_1798,c_441])).

cnf(c_3128,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_3093,c_213,c_1363,c_2427])).

cnf(c_3141,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_3139,c_3128])).

cnf(c_3110,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1798,c_213])).

cnf(c_3119,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_3110,c_213,c_2427])).

cnf(c_3129,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_3128,c_3119])).

cnf(c_3140,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_3139,c_3129])).

cnf(c_1972,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_1249,c_476])).

cnf(c_2088,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_1972,c_5,c_218,c_474])).

cnf(c_2849,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_441,c_2088])).

cnf(c_2848,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_668,c_2088])).

cnf(c_2847,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_707,c_2088])).

cnf(c_2846,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_226,c_2088])).

cnf(c_2680,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_707,c_479])).

cnf(c_2766,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_2680,c_479])).

cnf(c_2767,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_2766,c_1888,c_2427])).

cnf(c_2456,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_707,c_529])).

cnf(c_2535,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_2456,c_529])).

cnf(c_2536,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_2535,c_1378,c_1888])).

cnf(c_2457,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_668,c_529])).

cnf(c_2533,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_2457,c_2100,c_2304])).

cnf(c_2534,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_2533,c_619,c_1888])).

cnf(c_2458,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_441,c_529])).

cnf(c_2531,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(light_normalisation,[status(thm)],[c_2458,c_2098])).

cnf(c_1678,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_474,c_512])).

cnf(c_1685,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_1678,c_602])).

cnf(c_2532,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_2531,c_619,c_1685])).

cnf(c_2305,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_668,c_298])).

cnf(c_1496,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1249,c_441])).

cnf(c_1495,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1249,c_668])).

cnf(c_1494,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_1249,c_707])).

cnf(c_1368,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_707,c_218])).

cnf(c_1376,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_1368,c_707])).

cnf(c_1370,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_707,c_123])).

cnf(c_1221,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_441,c_1165])).

cnf(c_1156,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_668,c_277])).

cnf(c_1167,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_1156,c_668])).

cnf(c_1158,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_668,c_218])).

cnf(c_1166,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_1158,c_668])).

cnf(c_1152,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_668,c_619])).

cnf(c_967,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_441,c_218])).

cnf(c_1000,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_967,c_707])).

cnf(c_976,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_441,c_226])).

cnf(c_993,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_976,c_707])).

cnf(c_994,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_993,c_226,c_644])).

cnf(c_969,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_441,c_123])).

cnf(c_961,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_441,c_619])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_73,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_74,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_73])).

cnf(c_106,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_74,c_5])).

cnf(c_126,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_106,c_3])).

cnf(c_200,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_126,c_103])).

cnf(c_113,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_74,c_5])).

cnf(c_119,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_113,c_74])).

cnf(c_120,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_119,c_3])).

cnf(c_223,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_200,c_120])).

cnf(c_224,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_223,c_3])).

cnf(c_230,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_224,c_1])).

cnf(c_231,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_230,c_120,c_126])).

cnf(c_324,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_231,c_108])).

cnf(c_326,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_324,c_3])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_68,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_69,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_68])).

cnf(c_95,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_69])).

cnf(c_114,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_95,c_5])).

cnf(c_117,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_114,c_95])).

cnf(c_118,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_117,c_3])).

cnf(c_162,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_118,c_108])).

cnf(c_172,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_162,c_3])).

cnf(c_164,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_120,c_108])).

cnf(c_171,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_164,c_3])).

cnf(c_112,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[status(thm)],[c_69,c_5])).

cnf(c_121,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_112,c_69])).

cnf(c_122,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_121,c_3])).

cnf(c_165,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_122,c_108])).

cnf(c_170,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_165,c_3])).

cnf(c_105,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_69,c_5])).

cnf(c_127,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_105,c_3])).

cnf(c_107,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_95,c_5])).

cnf(c_125,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_107,c_3])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_90,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_10])).

cnf(c_7,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 51.21/7.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.21/7.01  
% 51.21/7.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.21/7.01  
% 51.21/7.01  ------  iProver source info
% 51.21/7.01  
% 51.21/7.01  git: date: 2020-06-30 10:37:57 +0100
% 51.21/7.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.21/7.01  git: non_committed_changes: false
% 51.21/7.01  git: last_make_outside_of_git: false
% 51.21/7.01  
% 51.21/7.01  ------ 
% 51.21/7.01  
% 51.21/7.01  ------ Input Options
% 51.21/7.01  
% 51.21/7.01  --out_options                           all
% 51.21/7.01  --tptp_safe_out                         true
% 51.21/7.01  --problem_path                          ""
% 51.21/7.01  --include_path                          ""
% 51.21/7.01  --clausifier                            res/vclausify_rel
% 51.21/7.01  --clausifier_options                    --mode clausify
% 51.21/7.01  --stdin                                 false
% 51.21/7.01  --stats_out                             all
% 51.21/7.01  
% 51.21/7.01  ------ General Options
% 51.21/7.01  
% 51.21/7.01  --fof                                   false
% 51.21/7.01  --time_out_real                         305.
% 51.21/7.01  --time_out_virtual                      -1.
% 51.21/7.01  --symbol_type_check                     false
% 51.21/7.01  --clausify_out                          false
% 51.21/7.01  --sig_cnt_out                           false
% 51.21/7.01  --trig_cnt_out                          false
% 51.21/7.01  --trig_cnt_out_tolerance                1.
% 51.21/7.01  --trig_cnt_out_sk_spl                   false
% 51.21/7.01  --abstr_cl_out                          false
% 51.21/7.01  
% 51.21/7.01  ------ Global Options
% 51.21/7.01  
% 51.21/7.01  --schedule                              default
% 51.21/7.01  --add_important_lit                     false
% 51.21/7.01  --prop_solver_per_cl                    1000
% 51.21/7.01  --min_unsat_core                        false
% 51.21/7.01  --soft_assumptions                      false
% 51.21/7.01  --soft_lemma_size                       3
% 51.21/7.01  --prop_impl_unit_size                   0
% 51.21/7.01  --prop_impl_unit                        []
% 51.21/7.01  --share_sel_clauses                     true
% 51.21/7.01  --reset_solvers                         false
% 51.21/7.01  --bc_imp_inh                            [conj_cone]
% 51.21/7.01  --conj_cone_tolerance                   3.
% 51.21/7.01  --extra_neg_conj                        none
% 51.21/7.01  --large_theory_mode                     true
% 51.21/7.01  --prolific_symb_bound                   200
% 51.21/7.01  --lt_threshold                          2000
% 51.21/7.01  --clause_weak_htbl                      true
% 51.21/7.01  --gc_record_bc_elim                     false
% 51.21/7.01  
% 51.21/7.01  ------ Preprocessing Options
% 51.21/7.01  
% 51.21/7.01  --preprocessing_flag                    true
% 51.21/7.01  --time_out_prep_mult                    0.1
% 51.21/7.01  --splitting_mode                        input
% 51.21/7.01  --splitting_grd                         true
% 51.21/7.01  --splitting_cvd                         false
% 51.21/7.01  --splitting_cvd_svl                     false
% 51.21/7.01  --splitting_nvd                         32
% 51.21/7.01  --sub_typing                            true
% 51.21/7.01  --prep_gs_sim                           true
% 51.21/7.01  --prep_unflatten                        true
% 51.21/7.01  --prep_res_sim                          true
% 51.21/7.01  --prep_upred                            true
% 51.21/7.01  --prep_sem_filter                       exhaustive
% 51.21/7.01  --prep_sem_filter_out                   false
% 51.21/7.01  --pred_elim                             true
% 51.21/7.01  --res_sim_input                         true
% 51.21/7.01  --eq_ax_congr_red                       true
% 51.21/7.01  --pure_diseq_elim                       true
% 51.21/7.01  --brand_transform                       false
% 51.21/7.01  --non_eq_to_eq                          false
% 51.21/7.01  --prep_def_merge                        true
% 51.21/7.01  --prep_def_merge_prop_impl              false
% 51.21/7.01  --prep_def_merge_mbd                    true
% 51.21/7.01  --prep_def_merge_tr_red                 false
% 51.21/7.01  --prep_def_merge_tr_cl                  false
% 51.21/7.01  --smt_preprocessing                     true
% 51.21/7.01  --smt_ac_axioms                         fast
% 51.21/7.01  --preprocessed_out                      false
% 51.21/7.01  --preprocessed_stats                    false
% 51.21/7.01  
% 51.21/7.01  ------ Abstraction refinement Options
% 51.21/7.01  
% 51.21/7.01  --abstr_ref                             []
% 51.21/7.01  --abstr_ref_prep                        false
% 51.21/7.01  --abstr_ref_until_sat                   false
% 51.21/7.01  --abstr_ref_sig_restrict                funpre
% 51.21/7.01  --abstr_ref_af_restrict_to_split_sk     false
% 51.21/7.01  --abstr_ref_under                       []
% 51.21/7.01  
% 51.21/7.01  ------ SAT Options
% 51.21/7.01  
% 51.21/7.01  --sat_mode                              false
% 51.21/7.01  --sat_fm_restart_options                ""
% 51.21/7.01  --sat_gr_def                            false
% 51.21/7.01  --sat_epr_types                         true
% 51.21/7.01  --sat_non_cyclic_types                  false
% 51.21/7.01  --sat_finite_models                     false
% 51.21/7.01  --sat_fm_lemmas                         false
% 51.21/7.01  --sat_fm_prep                           false
% 51.21/7.01  --sat_fm_uc_incr                        true
% 51.21/7.01  --sat_out_model                         small
% 51.21/7.01  --sat_out_clauses                       false
% 51.21/7.01  
% 51.21/7.01  ------ QBF Options
% 51.21/7.01  
% 51.21/7.01  --qbf_mode                              false
% 51.21/7.01  --qbf_elim_univ                         false
% 51.21/7.01  --qbf_dom_inst                          none
% 51.21/7.01  --qbf_dom_pre_inst                      false
% 51.21/7.01  --qbf_sk_in                             false
% 51.21/7.01  --qbf_pred_elim                         true
% 51.21/7.01  --qbf_split                             512
% 51.21/7.01  
% 51.21/7.01  ------ BMC1 Options
% 51.21/7.01  
% 51.21/7.01  --bmc1_incremental                      false
% 51.21/7.01  --bmc1_axioms                           reachable_all
% 51.21/7.01  --bmc1_min_bound                        0
% 51.21/7.01  --bmc1_max_bound                        -1
% 51.21/7.01  --bmc1_max_bound_default                -1
% 51.21/7.01  --bmc1_symbol_reachability              true
% 51.21/7.01  --bmc1_property_lemmas                  false
% 51.21/7.01  --bmc1_k_induction                      false
% 51.21/7.01  --bmc1_non_equiv_states                 false
% 51.21/7.01  --bmc1_deadlock                         false
% 51.21/7.01  --bmc1_ucm                              false
% 51.21/7.01  --bmc1_add_unsat_core                   none
% 51.21/7.01  --bmc1_unsat_core_children              false
% 51.21/7.01  --bmc1_unsat_core_extrapolate_axioms    false
% 51.21/7.01  --bmc1_out_stat                         full
% 51.21/7.01  --bmc1_ground_init                      false
% 51.21/7.01  --bmc1_pre_inst_next_state              false
% 51.21/7.01  --bmc1_pre_inst_state                   false
% 51.21/7.01  --bmc1_pre_inst_reach_state             false
% 51.21/7.01  --bmc1_out_unsat_core                   false
% 51.21/7.01  --bmc1_aig_witness_out                  false
% 51.21/7.01  --bmc1_verbose                          false
% 51.21/7.01  --bmc1_dump_clauses_tptp                false
% 51.21/7.01  --bmc1_dump_unsat_core_tptp             false
% 51.21/7.01  --bmc1_dump_file                        -
% 51.21/7.01  --bmc1_ucm_expand_uc_limit              128
% 51.21/7.01  --bmc1_ucm_n_expand_iterations          6
% 51.21/7.01  --bmc1_ucm_extend_mode                  1
% 51.21/7.01  --bmc1_ucm_init_mode                    2
% 51.21/7.01  --bmc1_ucm_cone_mode                    none
% 51.21/7.01  --bmc1_ucm_reduced_relation_type        0
% 51.21/7.01  --bmc1_ucm_relax_model                  4
% 51.21/7.01  --bmc1_ucm_full_tr_after_sat            true
% 51.21/7.01  --bmc1_ucm_expand_neg_assumptions       false
% 51.21/7.01  --bmc1_ucm_layered_model                none
% 51.21/7.01  --bmc1_ucm_max_lemma_size               10
% 51.21/7.01  
% 51.21/7.01  ------ AIG Options
% 51.21/7.01  
% 51.21/7.01  --aig_mode                              false
% 51.21/7.01  
% 51.21/7.01  ------ Instantiation Options
% 51.21/7.01  
% 51.21/7.01  --instantiation_flag                    true
% 51.21/7.01  --inst_sos_flag                         false
% 51.21/7.01  --inst_sos_phase                        true
% 51.21/7.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.21/7.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.21/7.01  --inst_lit_sel_side                     num_symb
% 51.21/7.01  --inst_solver_per_active                1400
% 51.21/7.01  --inst_solver_calls_frac                1.
% 51.21/7.01  --inst_passive_queue_type               priority_queues
% 51.21/7.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.21/7.01  --inst_passive_queues_freq              [25;2]
% 51.21/7.01  --inst_dismatching                      true
% 51.21/7.01  --inst_eager_unprocessed_to_passive     true
% 51.21/7.01  --inst_prop_sim_given                   true
% 51.21/7.01  --inst_prop_sim_new                     false
% 51.21/7.01  --inst_subs_new                         false
% 51.21/7.01  --inst_eq_res_simp                      false
% 51.21/7.01  --inst_subs_given                       false
% 51.21/7.01  --inst_orphan_elimination               true
% 51.21/7.01  --inst_learning_loop_flag               true
% 51.21/7.01  --inst_learning_start                   3000
% 51.21/7.01  --inst_learning_factor                  2
% 51.21/7.01  --inst_start_prop_sim_after_learn       3
% 51.21/7.01  --inst_sel_renew                        solver
% 51.21/7.01  --inst_lit_activity_flag                true
% 51.21/7.01  --inst_restr_to_given                   false
% 51.21/7.01  --inst_activity_threshold               500
% 51.21/7.01  --inst_out_proof                        true
% 51.21/7.01  
% 51.21/7.01  ------ Resolution Options
% 51.21/7.01  
% 51.21/7.01  --resolution_flag                       true
% 51.21/7.01  --res_lit_sel                           adaptive
% 51.21/7.01  --res_lit_sel_side                      none
% 51.21/7.01  --res_ordering                          kbo
% 51.21/7.01  --res_to_prop_solver                    active
% 51.21/7.01  --res_prop_simpl_new                    false
% 51.21/7.01  --res_prop_simpl_given                  true
% 51.21/7.01  --res_passive_queue_type                priority_queues
% 51.21/7.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.21/7.01  --res_passive_queues_freq               [15;5]
% 51.21/7.01  --res_forward_subs                      full
% 51.21/7.01  --res_backward_subs                     full
% 51.21/7.01  --res_forward_subs_resolution           true
% 51.21/7.01  --res_backward_subs_resolution          true
% 51.21/7.01  --res_orphan_elimination                true
% 51.21/7.01  --res_time_limit                        2.
% 51.21/7.01  --res_out_proof                         true
% 51.21/7.01  
% 51.21/7.01  ------ Superposition Options
% 51.21/7.01  
% 51.21/7.01  --superposition_flag                    true
% 51.21/7.01  --sup_passive_queue_type                priority_queues
% 51.21/7.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.21/7.01  --sup_passive_queues_freq               [8;1;4]
% 51.21/7.01  --demod_completeness_check              fast
% 51.21/7.01  --demod_use_ground                      true
% 51.21/7.01  --sup_to_prop_solver                    passive
% 51.21/7.01  --sup_prop_simpl_new                    true
% 51.21/7.01  --sup_prop_simpl_given                  true
% 51.21/7.01  --sup_fun_splitting                     false
% 51.21/7.01  --sup_smt_interval                      50000
% 51.21/7.01  
% 51.21/7.01  ------ Superposition Simplification Setup
% 51.21/7.01  
% 51.21/7.01  --sup_indices_passive                   []
% 51.21/7.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.21/7.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.21/7.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.21/7.01  --sup_full_triv                         [TrivRules;PropSubs]
% 51.21/7.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.21/7.01  --sup_full_bw                           [BwDemod]
% 51.21/7.01  --sup_immed_triv                        [TrivRules]
% 51.21/7.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.21/7.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.21/7.01  --sup_immed_bw_main                     []
% 51.21/7.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.21/7.01  --sup_input_triv                        [Unflattening;TrivRules]
% 51.21/7.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.21/7.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.21/7.01  
% 51.21/7.01  ------ Combination Options
% 51.21/7.01  
% 51.21/7.01  --comb_res_mult                         3
% 51.21/7.01  --comb_sup_mult                         2
% 51.21/7.01  --comb_inst_mult                        10
% 51.21/7.01  
% 51.21/7.01  ------ Debug Options
% 51.21/7.01  
% 51.21/7.01  --dbg_backtrace                         false
% 51.21/7.01  --dbg_dump_prop_clauses                 false
% 51.21/7.01  --dbg_dump_prop_clauses_file            -
% 51.21/7.01  --dbg_out_stat                          false
% 51.21/7.01  ------ Parsing...
% 51.21/7.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.21/7.01  
% 51.21/7.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 51.21/7.01  
% 51.21/7.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.21/7.01  
% 51.21/7.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 51.21/7.01  ------ Proving...
% 51.21/7.01  ------ Problem Properties 
% 51.21/7.01  
% 51.21/7.01  
% 51.21/7.01  clauses                                 8
% 51.21/7.01  conjectures                             2
% 51.21/7.01  EPR                                     1
% 51.21/7.01  Horn                                    8
% 51.21/7.01  unary                                   8
% 51.21/7.01  binary                                  0
% 51.21/7.01  lits                                    8
% 51.21/7.01  lits eq                                 8
% 51.21/7.01  fd_pure                                 0
% 51.21/7.01  fd_pseudo                               0
% 51.21/7.01  fd_cond                                 0
% 51.21/7.01  fd_pseudo_cond                          0
% 51.21/7.01  AC symbols                              0
% 51.21/7.01  
% 51.21/7.01  ------ Schedule UEQ
% 51.21/7.01  
% 51.21/7.01  ------ pure equality problem: resolution off 
% 51.21/7.01  
% 51.21/7.01  ------ Option_UEQ Time Limit: Unbounded
% 51.21/7.01  
% 51.21/7.01  
% 51.21/7.01  ------ 
% 51.21/7.01  Current options:
% 51.21/7.01  ------ 
% 51.21/7.01  
% 51.21/7.01  ------ Input Options
% 51.21/7.01  
% 51.21/7.01  --out_options                           all
% 51.21/7.01  --tptp_safe_out                         true
% 51.21/7.01  --problem_path                          ""
% 51.21/7.01  --include_path                          ""
% 51.21/7.01  --clausifier                            res/vclausify_rel
% 51.21/7.01  --clausifier_options                    --mode clausify
% 51.21/7.01  --stdin                                 false
% 51.21/7.01  --stats_out                             all
% 51.21/7.01  
% 51.21/7.01  ------ General Options
% 51.21/7.01  
% 51.21/7.01  --fof                                   false
% 51.21/7.01  --time_out_real                         305.
% 51.21/7.01  --time_out_virtual                      -1.
% 51.21/7.01  --symbol_type_check                     false
% 51.21/7.01  --clausify_out                          false
% 51.21/7.01  --sig_cnt_out                           false
% 51.21/7.01  --trig_cnt_out                          false
% 51.21/7.01  --trig_cnt_out_tolerance                1.
% 51.21/7.01  --trig_cnt_out_sk_spl                   false
% 51.21/7.01  --abstr_cl_out                          false
% 51.21/7.01  
% 51.21/7.01  ------ Global Options
% 51.21/7.01  
% 51.21/7.01  --schedule                              default
% 51.21/7.01  --add_important_lit                     false
% 51.21/7.01  --prop_solver_per_cl                    1000
% 51.21/7.01  --min_unsat_core                        false
% 51.21/7.01  --soft_assumptions                      false
% 51.21/7.01  --soft_lemma_size                       3
% 51.21/7.01  --prop_impl_unit_size                   0
% 51.21/7.01  --prop_impl_unit                        []
% 51.21/7.01  --share_sel_clauses                     true
% 51.21/7.01  --reset_solvers                         false
% 51.21/7.01  --bc_imp_inh                            [conj_cone]
% 51.21/7.01  --conj_cone_tolerance                   3.
% 51.21/7.01  --extra_neg_conj                        none
% 51.21/7.01  --large_theory_mode                     true
% 51.21/7.01  --prolific_symb_bound                   200
% 51.21/7.01  --lt_threshold                          2000
% 51.21/7.01  --clause_weak_htbl                      true
% 51.21/7.01  --gc_record_bc_elim                     false
% 51.21/7.01  
% 51.21/7.01  ------ Preprocessing Options
% 51.21/7.01  
% 51.21/7.01  --preprocessing_flag                    true
% 51.21/7.01  --time_out_prep_mult                    0.1
% 51.21/7.01  --splitting_mode                        input
% 51.21/7.01  --splitting_grd                         true
% 51.21/7.01  --splitting_cvd                         false
% 51.21/7.01  --splitting_cvd_svl                     false
% 51.21/7.01  --splitting_nvd                         32
% 51.21/7.01  --sub_typing                            true
% 51.21/7.01  --prep_gs_sim                           true
% 51.21/7.01  --prep_unflatten                        true
% 51.21/7.01  --prep_res_sim                          true
% 51.21/7.01  --prep_upred                            true
% 51.21/7.01  --prep_sem_filter                       exhaustive
% 51.21/7.01  --prep_sem_filter_out                   false
% 51.21/7.01  --pred_elim                             true
% 51.21/7.01  --res_sim_input                         true
% 51.21/7.01  --eq_ax_congr_red                       true
% 51.21/7.01  --pure_diseq_elim                       true
% 51.21/7.01  --brand_transform                       false
% 51.21/7.01  --non_eq_to_eq                          false
% 51.21/7.01  --prep_def_merge                        true
% 51.21/7.01  --prep_def_merge_prop_impl              false
% 51.21/7.01  --prep_def_merge_mbd                    true
% 51.21/7.01  --prep_def_merge_tr_red                 false
% 51.21/7.01  --prep_def_merge_tr_cl                  false
% 51.21/7.01  --smt_preprocessing                     true
% 51.21/7.01  --smt_ac_axioms                         fast
% 51.21/7.01  --preprocessed_out                      false
% 51.21/7.01  --preprocessed_stats                    false
% 51.21/7.01  
% 51.21/7.01  ------ Abstraction refinement Options
% 51.21/7.01  
% 51.21/7.01  --abstr_ref                             []
% 51.21/7.01  --abstr_ref_prep                        false
% 51.21/7.01  --abstr_ref_until_sat                   false
% 51.21/7.01  --abstr_ref_sig_restrict                funpre
% 51.21/7.01  --abstr_ref_af_restrict_to_split_sk     false
% 51.21/7.01  --abstr_ref_under                       []
% 51.21/7.01  
% 51.21/7.01  ------ SAT Options
% 51.21/7.01  
% 51.21/7.01  --sat_mode                              false
% 51.21/7.01  --sat_fm_restart_options                ""
% 51.21/7.01  --sat_gr_def                            false
% 51.21/7.01  --sat_epr_types                         true
% 51.21/7.01  --sat_non_cyclic_types                  false
% 51.21/7.01  --sat_finite_models                     false
% 51.21/7.01  --sat_fm_lemmas                         false
% 51.21/7.01  --sat_fm_prep                           false
% 51.21/7.01  --sat_fm_uc_incr                        true
% 51.21/7.01  --sat_out_model                         small
% 51.21/7.01  --sat_out_clauses                       false
% 51.21/7.01  
% 51.21/7.01  ------ QBF Options
% 51.21/7.01  
% 51.21/7.01  --qbf_mode                              false
% 51.21/7.01  --qbf_elim_univ                         false
% 51.21/7.01  --qbf_dom_inst                          none
% 51.21/7.01  --qbf_dom_pre_inst                      false
% 51.21/7.01  --qbf_sk_in                             false
% 51.21/7.01  --qbf_pred_elim                         true
% 51.21/7.01  --qbf_split                             512
% 51.21/7.01  
% 51.21/7.01  ------ BMC1 Options
% 51.21/7.01  
% 51.21/7.01  --bmc1_incremental                      false
% 51.21/7.01  --bmc1_axioms                           reachable_all
% 51.21/7.01  --bmc1_min_bound                        0
% 51.21/7.01  --bmc1_max_bound                        -1
% 51.21/7.01  --bmc1_max_bound_default                -1
% 51.21/7.01  --bmc1_symbol_reachability              true
% 51.21/7.01  --bmc1_property_lemmas                  false
% 51.21/7.01  --bmc1_k_induction                      false
% 51.21/7.01  --bmc1_non_equiv_states                 false
% 51.21/7.01  --bmc1_deadlock                         false
% 51.21/7.01  --bmc1_ucm                              false
% 51.21/7.01  --bmc1_add_unsat_core                   none
% 51.21/7.01  --bmc1_unsat_core_children              false
% 51.21/7.01  --bmc1_unsat_core_extrapolate_axioms    false
% 51.21/7.01  --bmc1_out_stat                         full
% 51.21/7.01  --bmc1_ground_init                      false
% 51.21/7.01  --bmc1_pre_inst_next_state              false
% 51.21/7.01  --bmc1_pre_inst_state                   false
% 51.21/7.01  --bmc1_pre_inst_reach_state             false
% 51.21/7.01  --bmc1_out_unsat_core                   false
% 51.21/7.01  --bmc1_aig_witness_out                  false
% 51.21/7.01  --bmc1_verbose                          false
% 51.21/7.01  --bmc1_dump_clauses_tptp                false
% 51.21/7.01  --bmc1_dump_unsat_core_tptp             false
% 51.21/7.01  --bmc1_dump_file                        -
% 51.21/7.01  --bmc1_ucm_expand_uc_limit              128
% 51.21/7.01  --bmc1_ucm_n_expand_iterations          6
% 51.21/7.01  --bmc1_ucm_extend_mode                  1
% 51.21/7.01  --bmc1_ucm_init_mode                    2
% 51.21/7.01  --bmc1_ucm_cone_mode                    none
% 51.21/7.01  --bmc1_ucm_reduced_relation_type        0
% 51.21/7.01  --bmc1_ucm_relax_model                  4
% 51.21/7.01  --bmc1_ucm_full_tr_after_sat            true
% 51.21/7.01  --bmc1_ucm_expand_neg_assumptions       false
% 51.21/7.01  --bmc1_ucm_layered_model                none
% 51.21/7.01  --bmc1_ucm_max_lemma_size               10
% 51.21/7.01  
% 51.21/7.01  ------ AIG Options
% 51.21/7.01  
% 51.21/7.01  --aig_mode                              false
% 51.21/7.01  
% 51.21/7.01  ------ Instantiation Options
% 51.21/7.01  
% 51.21/7.01  --instantiation_flag                    false
% 51.21/7.01  --inst_sos_flag                         false
% 51.21/7.01  --inst_sos_phase                        true
% 51.21/7.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.21/7.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.21/7.01  --inst_lit_sel_side                     num_symb
% 51.21/7.01  --inst_solver_per_active                1400
% 51.21/7.01  --inst_solver_calls_frac                1.
% 51.21/7.01  --inst_passive_queue_type               priority_queues
% 51.21/7.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.21/7.01  --inst_passive_queues_freq              [25;2]
% 51.21/7.01  --inst_dismatching                      true
% 51.21/7.01  --inst_eager_unprocessed_to_passive     true
% 51.21/7.01  --inst_prop_sim_given                   true
% 51.21/7.01  --inst_prop_sim_new                     false
% 51.21/7.01  --inst_subs_new                         false
% 51.21/7.01  --inst_eq_res_simp                      false
% 51.21/7.01  --inst_subs_given                       false
% 51.21/7.01  --inst_orphan_elimination               true
% 51.21/7.01  --inst_learning_loop_flag               true
% 51.21/7.01  --inst_learning_start                   3000
% 51.21/7.01  --inst_learning_factor                  2
% 51.21/7.01  --inst_start_prop_sim_after_learn       3
% 51.21/7.01  --inst_sel_renew                        solver
% 51.21/7.01  --inst_lit_activity_flag                true
% 51.21/7.01  --inst_restr_to_given                   false
% 51.21/7.01  --inst_activity_threshold               500
% 51.21/7.01  --inst_out_proof                        true
% 51.21/7.01  
% 51.21/7.01  ------ Resolution Options
% 51.21/7.01  
% 51.21/7.01  --resolution_flag                       false
% 51.21/7.01  --res_lit_sel                           adaptive
% 51.21/7.01  --res_lit_sel_side                      none
% 51.21/7.01  --res_ordering                          kbo
% 51.21/7.01  --res_to_prop_solver                    active
% 51.21/7.01  --res_prop_simpl_new                    false
% 51.21/7.01  --res_prop_simpl_given                  true
% 51.21/7.01  --res_passive_queue_type                priority_queues
% 51.21/7.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.21/7.01  --res_passive_queues_freq               [15;5]
% 51.21/7.01  --res_forward_subs                      full
% 51.21/7.01  --res_backward_subs                     full
% 51.21/7.01  --res_forward_subs_resolution           true
% 51.21/7.01  --res_backward_subs_resolution          true
% 51.21/7.01  --res_orphan_elimination                true
% 51.21/7.01  --res_time_limit                        2.
% 51.21/7.01  --res_out_proof                         true
% 51.21/7.01  
% 51.21/7.01  ------ Superposition Options
% 51.21/7.01  
% 51.21/7.01  --superposition_flag                    true
% 51.21/7.01  --sup_passive_queue_type                priority_queues
% 51.21/7.01  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.21/7.01  --sup_passive_queues_freq               [8;1;4]
% 51.21/7.01  --demod_completeness_check              fast
% 51.21/7.01  --demod_use_ground                      true
% 51.21/7.01  --sup_to_prop_solver                    active
% 51.21/7.01  --sup_prop_simpl_new                    false
% 51.21/7.01  --sup_prop_simpl_given                  false
% 51.21/7.01  --sup_fun_splitting                     true
% 51.21/7.01  --sup_smt_interval                      10000
% 51.21/7.01  
% 51.21/7.01  ------ Superposition Simplification Setup
% 51.21/7.01  
% 51.21/7.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.21/7.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.21/7.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.21/7.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.21/7.01  --sup_full_triv                         [TrivRules]
% 51.21/7.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.21/7.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.21/7.01  --sup_immed_triv                        [TrivRules]
% 51.21/7.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.21/7.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.21/7.01  --sup_immed_bw_main                     []
% 51.21/7.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.21/7.01  --sup_input_triv                        [Unflattening;TrivRules]
% 51.21/7.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.21/7.01  --sup_input_bw                          [BwDemod;BwSubsumption]
% 51.21/7.01  
% 51.21/7.01  ------ Combination Options
% 51.21/7.01  
% 51.21/7.01  --comb_res_mult                         1
% 51.21/7.01  --comb_sup_mult                         1
% 51.21/7.01  --comb_inst_mult                        1000000
% 51.21/7.01  
% 51.21/7.01  ------ Debug Options
% 51.21/7.01  
% 51.21/7.01  --dbg_backtrace                         false
% 51.21/7.01  --dbg_dump_prop_clauses                 false
% 51.21/7.01  --dbg_dump_prop_clauses_file            -
% 51.21/7.01  --dbg_out_stat                          false
% 51.21/7.01  
% 51.21/7.01  
% 51.21/7.01  
% 51.21/7.01  
% 51.21/7.01  ------ Proving...
% 51.21/7.01  
% 51.21/7.01  
% 51.21/7.01  % SZS status CounterSatisfiable for theBenchmark.p
% 51.21/7.01  
% 51.21/7.01  % SZS output start Saturation for theBenchmark.p
% 51.21/7.01  
% 51.21/7.01  fof(f8,axiom,(
% 51.21/7.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f25,plain,(
% 51.21/7.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 51.21/7.01    inference(cnf_transformation,[],[f8])).
% 51.21/7.01  
% 51.21/7.01  fof(f5,axiom,(
% 51.21/7.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f13,plain,(
% 51.21/7.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 51.21/7.01    inference(ennf_transformation,[],[f5])).
% 51.21/7.01  
% 51.21/7.01  fof(f22,plain,(
% 51.21/7.01    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 51.21/7.01    inference(cnf_transformation,[],[f13])).
% 51.21/7.01  
% 51.21/7.01  fof(f2,axiom,(
% 51.21/7.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f19,plain,(
% 51.21/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.21/7.01    inference(cnf_transformation,[],[f2])).
% 51.21/7.01  
% 51.21/7.01  fof(f7,axiom,(
% 51.21/7.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f24,plain,(
% 51.21/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 51.21/7.01    inference(cnf_transformation,[],[f7])).
% 51.21/7.01  
% 51.21/7.01  fof(f30,plain,(
% 51.21/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 51.21/7.01    inference(definition_unfolding,[],[f19,f24,f24])).
% 51.21/7.01  
% 51.21/7.01  fof(f6,axiom,(
% 51.21/7.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f23,plain,(
% 51.21/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 51.21/7.01    inference(cnf_transformation,[],[f6])).
% 51.21/7.01  
% 51.21/7.01  fof(f32,plain,(
% 51.21/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 51.21/7.01    inference(definition_unfolding,[],[f23,f24])).
% 51.21/7.01  
% 51.21/7.01  fof(f4,axiom,(
% 51.21/7.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f21,plain,(
% 51.21/7.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.21/7.01    inference(cnf_transformation,[],[f4])).
% 51.21/7.01  
% 51.21/7.01  fof(f3,axiom,(
% 51.21/7.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f11,plain,(
% 51.21/7.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 51.21/7.01    inference(unused_predicate_definition_removal,[],[f3])).
% 51.21/7.01  
% 51.21/7.01  fof(f12,plain,(
% 51.21/7.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 51.21/7.01    inference(ennf_transformation,[],[f11])).
% 51.21/7.01  
% 51.21/7.01  fof(f20,plain,(
% 51.21/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 51.21/7.01    inference(cnf_transformation,[],[f12])).
% 51.21/7.01  
% 51.21/7.01  fof(f31,plain,(
% 51.21/7.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 51.21/7.01    inference(definition_unfolding,[],[f20,f24])).
% 51.21/7.01  
% 51.21/7.01  fof(f9,conjecture,(
% 51.21/7.01    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f10,negated_conjecture,(
% 51.21/7.01    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 51.21/7.01    inference(negated_conjecture,[],[f9])).
% 51.21/7.01  
% 51.21/7.01  fof(f14,plain,(
% 51.21/7.01    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 51.21/7.01    inference(ennf_transformation,[],[f10])).
% 51.21/7.01  
% 51.21/7.01  fof(f15,plain,(
% 51.21/7.01    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 51.21/7.01    inference(flattening,[],[f14])).
% 51.21/7.01  
% 51.21/7.01  fof(f16,plain,(
% 51.21/7.01    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 51.21/7.01    introduced(choice_axiom,[])).
% 51.21/7.01  
% 51.21/7.01  fof(f17,plain,(
% 51.21/7.01    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 51.21/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).
% 51.21/7.01  
% 51.21/7.01  fof(f27,plain,(
% 51.21/7.01    r1_xboole_0(sK2,sK0)),
% 51.21/7.01    inference(cnf_transformation,[],[f17])).
% 51.21/7.01  
% 51.21/7.01  fof(f28,plain,(
% 51.21/7.01    r1_xboole_0(sK3,sK1)),
% 51.21/7.01    inference(cnf_transformation,[],[f17])).
% 51.21/7.01  
% 51.21/7.01  fof(f1,axiom,(
% 51.21/7.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 51.21/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.21/7.01  
% 51.21/7.01  fof(f18,plain,(
% 51.21/7.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 51.21/7.01    inference(cnf_transformation,[],[f1])).
% 51.21/7.01  
% 51.21/7.01  fof(f26,plain,(
% 51.21/7.01    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 51.21/7.01    inference(cnf_transformation,[],[f17])).
% 51.21/7.01  
% 51.21/7.01  fof(f29,plain,(
% 51.21/7.01    sK1 != sK2),
% 51.21/7.01    inference(cnf_transformation,[],[f17])).
% 51.21/7.01  
% 51.21/7.01  cnf(c_64,plain,
% 51.21/7.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.21/7.01      theory(equality) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_63,plain,
% 51.21/7.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.21/7.01      theory(equality) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_58,plain,( X0_2 = X0_2 ),theory(equality) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_6,plain,
% 51.21/7.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(cnf_transformation,[],[f25]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4,plain,
% 51.21/7.01      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 51.21/7.01      inference(cnf_transformation,[],[f22]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.21/7.01      inference(cnf_transformation,[],[f30]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 51.21/7.01      inference(cnf_transformation,[],[f32]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_103,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_194,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_226,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_194,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_441,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.21/7.01      inference(cnf_transformation,[],[f21]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_94,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_108,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_94,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_207,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_108,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_218,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_207,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_277,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_94,c_218]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_965,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_277]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_202,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_94,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_220,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_202,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_221,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_220,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_250,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_94,c_221]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_602,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_250]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_213,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_103,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_707,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_213]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1001,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_965,c_602,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_111,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_123,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_111,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_475,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_123]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1798,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_668,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_213]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1164,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4060,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_1164]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1163,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4087,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1163,c_1164]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_929,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_103,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1033,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_929,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_942,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_213,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1018,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_942,c_213,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1034,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1033,c_1018]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3909,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1163,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4262,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_4087,c_1034,c_3909]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4280,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4060,c_4262]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_476,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_94]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3085,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3135,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3085,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4281,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_4280,c_1798,c_3135]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_478,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_277]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_515,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_478]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_529,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_515,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2374,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_476,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4282,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4281,c_2374]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_105362,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1001,c_4282]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_473,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_218]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_479,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_473,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2649,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_29630,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_476,c_2649]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_104028,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1001,c_29630]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2427,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3485,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_2427,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3493,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_2427,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3504,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3485,c_2427,c_3493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_91516,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_3504,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_91620,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_91516,c_3504]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_964,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_478]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1002,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_964,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_44986,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1002,c_1]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14270,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_2374]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14513,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_14270,c_2374]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14514,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_14513,c_1033,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_45010,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_44986,c_3909,c_14514]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_970,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_94]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9133,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_474,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1662,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_474]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1700,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1662,c_474]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1155,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_478]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1168,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1155,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1369,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1701,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1700,c_707,c_1168,c_1369]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5597,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1701,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_270,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_94,c_218]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_7103,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5597,c_270]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_471,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_277]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_480,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_471,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5853,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_480]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_972,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5886,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_972,c_480]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3908,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1163,c_2427]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3887,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1163,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3938,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3887,c_3908]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5974,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_5886,c_3908,c_3938]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_6010,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_5853,c_480,c_5974]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1151,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1169,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1151,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_983,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_1]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_984,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_983,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_985,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_984,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_978,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_992,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_978,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1170,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1169,c_707,c_985,c_992]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4440,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1170,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4466,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1170,c_2427]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4499,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4440,c_4466]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4145,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4170,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4197,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4145,c_4170]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_619,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_250,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_644,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_619]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4198,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4197,c_644]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4500,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_4499,c_4198]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_6011,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_6010,c_4500]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_7232,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_7103,c_6011]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9186,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_9133,c_7232]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_74267,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9186,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4132,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_74449,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_74267,c_4132,c_9186,c_14514,c_45010]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_91621,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_91620,c_45010,c_74449]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3491,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_2427,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3497,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3491,c_2427]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_87579,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_476,c_3497]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1828,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1886,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1828,c_1002]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1887,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1886,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83031,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1887,c_1002]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83456,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_83031,c_1887]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1371,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_94]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1162,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_221]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1165,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1162,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1220,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_1165]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1965,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1827,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1363,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_250]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1888,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1827,c_1168,c_1363]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2099,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1965,c_1888]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2100,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_2099,c_5,c_1168]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_23781,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1220,c_2100]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3867,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1163,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1226,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1165,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1249,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = k4_xboole_0(X0,X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1226,c_108,c_218,c_277]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1493,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1249,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9606,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1001,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15554,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9606,c_9606]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5893,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_480]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5963,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_5893,c_4262]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5964,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_5963,c_1033,c_3504]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15672,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9606,c_5964]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15594,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9606,c_644]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15783,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_15594,c_15672]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9654,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1001,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9717,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_9654,c_7232]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15784,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_15783,c_9717]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14271,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_2427,c_2374]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14510,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_14271,c_2374]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14511,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_14510,c_9717]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14512,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_14511,c_4282,c_9186]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15785,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_15784,c_474,c_14512]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15574,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9606,c_1]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3846,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1163,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3868,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1163,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3961,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3846,c_3868]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15817,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_15574,c_1369,c_3961]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15862,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_15554,c_15672,c_15785,c_15817]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1159,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_512,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = k4_xboole_0(X0,X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_94,c_478]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3018,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_512,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_294,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_218,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_297,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_294,c_250]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_298,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_297,c_221]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3210,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_3018,c_3,c_298]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10047,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1159,c_3210]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10050,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1159,c_270]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10066,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_10050,c_7232]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10069,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_10047,c_10066]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15863,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_15862,c_3,c_10069]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_23852,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_23781,c_1369,c_3867,c_15863]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8180,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_644]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8379,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_8180,c_644]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4107,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4109,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4233,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_4109,c_1369]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4234,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4107,c_4170,c_4233]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8380,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_8379,c_1369,c_4234]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_23853,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_23852,c_5,c_8380]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_50478,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1371,c_23853]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_62223,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_985,c_4170]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4153,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4190,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_4153,c_5,c_1798,c_1888]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10341,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1369,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1361,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_1165]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4169,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10385,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_10341,c_1361,c_4169,c_7232]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_16317,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_10385,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1219,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_1165]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4443,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1170,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4497,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4443,c_4466]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_16596,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_16317,c_5,c_1219,c_4497]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4163,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_972]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4183,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_4163,c_5,c_1033,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_41205,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_16596,c_4183]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_41241,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_41205,c_16596]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9616,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1001,c_644]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9157,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9744,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_9616,c_9157]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5640,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1701,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9745,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_9744,c_1369,c_5640]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10736,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1371,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_17022,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_10736,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10737,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1371,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_17293,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_17022,c_10737,c_15672]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_17294,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_17293,c_1369,c_10737]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1966,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2097,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1966,c_1888]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2098,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_2097,c_5,c_1002]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_19757,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_2098]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_20402,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_19757,c_1798,c_9186,c_9717,c_14514,c_15785]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15552,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9606,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15864,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_15552,c_15672,c_15817]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_20403,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_20402,c_474,c_15864]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_29472,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1001,c_2649]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_41242,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_41241,c_9745,c_17294,c_20403,c_29472]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_62773,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_62223,c_992,c_4190,c_9186,c_41242]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4467,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1170,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_72924,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_4467,c_5974]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_73524,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_72924,c_992,c_9186,c_14514,c_45010]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83457,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_83456,c_50478,c_62773,c_73524]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1111,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1200,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),X0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1111,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1201,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1200,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83175,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1887,c_1201]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83216,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_83175,c_1887]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83217,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_83216,c_50478,c_73524]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83176,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1887,c_1170]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83214,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_83176,c_1887]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_83215,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_83214,c_10066,c_50478,c_73524]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_82763,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1001,c_1887]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_82764,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1170,c_1887]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_44478,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9606,c_1002]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_45709,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_44478,c_15672]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_77823,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_4170,c_45709]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1365,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_478]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1378,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1365,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_47433,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1378,c_4183]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_47474,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_47433,c_1378]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_47475,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_47474,c_1798,c_10066,c_14514,c_45010]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_74191,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9186,c_3909]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_74548,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_74191,c_4132,c_9186,c_14514,c_45010]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_78588,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_77823,c_1798,c_9186,c_9717,c_14514,c_47475,c_50478,c_74548]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_77824,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1378,c_45709]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_78587,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_77824,c_1798,c_9186,c_9717,c_10066,c_14514,c_47475,c_74548]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3061,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3166,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3061,c_1798,c_3135]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3167,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_3166,c_1888]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_156,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_94,c_123]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3168,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3167,c_156]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_72968,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_3168,c_5974]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_73452,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_72968,c_3168,c_9186,c_14514,c_62773]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3064,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_213,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3160,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3064,c_1798,c_3135]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3161,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_3160,c_1888]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3162,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3161,c_156]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_72969,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_3162,c_5974]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_45732,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1001,c_1168]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_73451,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_72969,c_3168,c_4190,c_14514,c_45732,c_62773]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_73151,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5974,c_4183]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_73201,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_73151,c_5974]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_73202,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_73201,c_4132,c_14514,c_17294,c_62773]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_956,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_962,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_250]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1005,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_956,c_962]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1006,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1005,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2579,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_476,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_70413,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1006,c_2579]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_70803,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_70413,c_1006]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_62308,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_4170,c_3909]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_62642,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_62308,c_1798,c_9186,c_14514,c_50478]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_70804,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_70803,c_7232,c_45732,c_62642]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10825,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1371,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_67795,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_10825,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_62222,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_4467,c_4170]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_62774,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_62222,c_992,c_9186,c_14514,c_45010]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_62432,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_4170,c_972]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_62469,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_62432,c_1798,c_9186,c_14514,c_50478]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_50910,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_23853,c_1002]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_37173,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_10736,c_4467]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_37964,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_37173,c_1369,c_15863,c_29630]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_51193,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_50910,c_7232,c_9745,c_29472,c_37964]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9087,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14947,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9087,c_5964]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_46068,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_14947,c_1168]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_46534,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_46068,c_45010]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_46535,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_46534,c_2374,c_9186]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_46536,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_46535,c_9186]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_45729,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_1168]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_44944,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1002,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_45098,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_44944,c_1002,c_45010]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_44480,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_1002]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5093,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_2427,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5304,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k1_xboole_0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_5093,c_4500]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3805,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_2427,c_1163]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3998,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3805,c_3961]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2304,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_298]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3999,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_3998,c_1798,c_2304,c_3135]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5305,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_5304,c_3,c_5,c_3999]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_30464,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_5305]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_30292,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9606,c_5305]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_31396,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_30292,c_15672]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_29473,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1170,c_2649]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5030,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5362,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_5030,c_4190]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5363,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_5362,c_3,c_5,c_4233]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_21737,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5363,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_21815,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_21737,c_5363]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9123,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9192,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_9123,c_9157]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_21816,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_21815,c_7232,c_9192]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_20005,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_2098,c_1]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_20032,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_20005,c_3909,c_14514]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_17839,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_14947,c_10385]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15619,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9606,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15757,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_15619,c_15672]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15758,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_15757,c_9186,c_9717]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14817,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9087,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9088,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_15120,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_14817,c_5,c_1219,c_9088]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_14937,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9087,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9147,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9174,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_9147,c_5,c_3168,c_4190]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_13621,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_9174,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_13717,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_13621,c_9174]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_13718,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_13717,c_7232,c_9157]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_968,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8618,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k1_xboole_0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_968,c_1219]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8703,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_8618,c_3,c_5,c_1219]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_12794,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_476,c_8703]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10776,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1371,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5012,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5383,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))),k1_xboole_0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_5012,c_4190]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5384,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_5383,c_3,c_474,c_2374]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10875,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_10776,c_5384,c_9717]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9156,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9152,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_970,c_480]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_368,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_156,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_380,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_368,c_298]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8600,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_968,c_380]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2306,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_298]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8715,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_8600,c_474,c_2306]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8617,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_968,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8704,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_8617,c_3,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_7100,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5597,c_3210]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_7238,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_7100,c_7232]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_7123,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5597,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_7120,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5597,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5575,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1701,c_1493]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5685,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_5575,c_3,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_6208,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5685,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_6292,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_6208,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_6216,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0),k1_xboole_0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5685,c_1219]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_6289,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_6216,c_3,c_5,c_1219]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_6209,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_5685,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5826,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_972,c_480]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5817,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_480]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5618,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1701,c_298]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5648,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_5618,c_4190]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5625,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1701,c_218]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5645,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_5625,c_4190]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5626,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1701,c_221]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_5586,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1701,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4749,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_1219]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4929,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_4749,c_4500]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4930,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4929,c_3,c_474]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4148,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1164,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_4194,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_4148,c_4170]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3697,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_972,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3721,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_972,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3700,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_972,c_475]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3741,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3700,c_3721]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3744,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3697,c_3721,c_3741]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3720,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_972,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3480,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_2427,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3508,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3480,c_3493,c_3504]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3509,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_3508,c_1798,c_3135]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3078,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3138,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3078,c_3135]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2681,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2764,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_2681,c_1369,c_2100]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2765,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_2764,c_270,c_619]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3139,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(light_normalisation,
% 51.21/7.01                [status(thm)],
% 51.21/7.01                [c_3138,c_2304,c_2427,c_2765]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3095,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_213]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3126,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3095,c_1798]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3127,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_3126,c_213,c_1363,c_2427]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3142,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3139,c_3127]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3093,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3128,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_3093,c_213,c_1363,c_2427]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3141,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3139,c_3128]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3110,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1798,c_213]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3119,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_3110,c_213,c_2427]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3129,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3128,c_3119]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_3140,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_3139,c_3129]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1972,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1249,c_476]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2088,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1972,c_5,c_218,c_474]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2849,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_2088]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2848,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_2088]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2847,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_2088]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2846,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_226,c_2088]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2680,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2766,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_2680,c_479]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2767,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_2766,c_1888,c_2427]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2456,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2535,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_2456,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2536,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_2535,c_1378,c_1888]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2457,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2533,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_2457,c_2100,c_2304]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2534,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_2533,c_619,c_1888]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2458,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_529]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2531,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_2458,c_2098]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1678,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_474,c_512]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1685,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_1678,c_602]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2532,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_2531,c_619,c_1685]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2305,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_298]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1496,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1249,c_441]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1495,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1249,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1494,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1249,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1368,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_218]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1376,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1368,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1370,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_707,c_123]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1221,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_1165]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1156,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_277]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1167,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1156,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1158,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_218]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1166,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_1158,c_668]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1152,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_668,c_619]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_967,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_218]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_1000,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_967,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_976,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_226]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_993,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_976,c_707]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_994,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_993,c_226,c_644]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_969,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_123]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_961,plain,
% 51.21/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_441,c_619]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_2,plain,
% 51.21/7.01      ( ~ r1_xboole_0(X0,X1)
% 51.21/7.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 51.21/7.01      inference(cnf_transformation,[],[f31]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_9,negated_conjecture,
% 51.21/7.01      ( r1_xboole_0(sK2,sK0) ),
% 51.21/7.01      inference(cnf_transformation,[],[f27]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_73,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 51.21/7.01      | sK0 != X1
% 51.21/7.01      | sK2 != X0 ),
% 51.21/7.01      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_74,plain,
% 51.21/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 51.21/7.01      inference(unflattening,[status(thm)],[c_73]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_106,plain,
% 51.21/7.01      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_74,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_126,plain,
% 51.21/7.01      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_106,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_200,plain,
% 51.21/7.01      ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK0,sK2) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_126,c_103]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_113,plain,
% 51.21/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_74,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_119,plain,
% 51.21/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_113,c_74]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_120,plain,
% 51.21/7.01      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_119,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_223,plain,
% 51.21/7.01      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_200,c_120]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_224,plain,
% 51.21/7.01      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_223,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_230,plain,
% 51.21/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,sK0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_224,c_1]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_231,plain,
% 51.21/7.01      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_230,c_120,c_126]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_324,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_231,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_326,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_324,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_8,negated_conjecture,
% 51.21/7.01      ( r1_xboole_0(sK3,sK1) ),
% 51.21/7.01      inference(cnf_transformation,[],[f28]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_68,plain,
% 51.21/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 51.21/7.01      | sK3 != X0
% 51.21/7.01      | sK1 != X1 ),
% 51.21/7.01      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_69,plain,
% 51.21/7.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 51.21/7.01      inference(unflattening,[status(thm)],[c_68]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_95,plain,
% 51.21/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_1,c_69]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_114,plain,
% 51.21/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_95,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_117,plain,
% 51.21/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_114,c_95]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_118,plain,
% 51.21/7.01      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_117,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_162,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_118,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_172,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_162,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_164,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_120,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_171,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_164,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_112,plain,
% 51.21/7.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_69,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_121,plain,
% 51.21/7.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 51.21/7.01      inference(light_normalisation,[status(thm)],[c_112,c_69]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_122,plain,
% 51.21/7.01      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_121,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_165,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_122,c_108]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_170,plain,
% 51.21/7.01      ( k4_xboole_0(k1_xboole_0,sK3) = k1_xboole_0 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_165,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_105,plain,
% 51.21/7.01      ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_69,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_127,plain,
% 51.21/7.01      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_105,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_107,plain,
% 51.21/7.01      ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
% 51.21/7.01      inference(superposition,[status(thm)],[c_95,c_5]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_125,plain,
% 51.21/7.01      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 51.21/7.01      inference(demodulation,[status(thm)],[c_107,c_3]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_0,plain,
% 51.21/7.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 51.21/7.01      inference(cnf_transformation,[],[f18]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_10,negated_conjecture,
% 51.21/7.01      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 51.21/7.01      inference(cnf_transformation,[],[f26]) ).
% 51.21/7.01  
% 51.21/7.01  cnf(c_90,plain,
% 51.21/7.02      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 51.21/7.02      inference(demodulation,[status(thm)],[c_0,c_10]) ).
% 51.21/7.02  
% 51.21/7.02  cnf(c_7,negated_conjecture,
% 51.21/7.02      ( sK1 != sK2 ),
% 51.21/7.02      inference(cnf_transformation,[],[f29]) ).
% 51.21/7.02  
% 51.21/7.02  
% 51.21/7.02  % SZS output end Saturation for theBenchmark.p
% 51.21/7.02  
% 51.21/7.02  ------                               Statistics
% 51.21/7.02  
% 51.21/7.02  ------ General
% 51.21/7.02  
% 51.21/7.02  abstr_ref_over_cycles:                  0
% 51.21/7.02  abstr_ref_under_cycles:                 0
% 51.21/7.02  gc_basic_clause_elim:                   0
% 51.21/7.02  forced_gc_time:                         0
% 51.21/7.02  parsing_time:                           0.017
% 51.21/7.02  unif_index_cands_time:                  0.
% 51.21/7.02  unif_index_add_time:                    0.
% 51.21/7.02  orderings_time:                         0.
% 51.21/7.02  out_proof_time:                         0.
% 51.21/7.02  total_time:                             6.156
% 51.21/7.02  num_of_symbols:                         40
% 51.21/7.02  num_of_terms:                           183808
% 51.21/7.02  
% 51.21/7.02  ------ Preprocessing
% 51.21/7.02  
% 51.21/7.02  num_of_splits:                          0
% 51.21/7.02  num_of_split_atoms:                     0
% 51.21/7.02  num_of_reused_defs:                     0
% 51.21/7.02  num_eq_ax_congr_red:                    1
% 51.21/7.02  num_of_sem_filtered_clauses:            2
% 51.21/7.02  num_of_subtypes:                        0
% 51.21/7.02  monotx_restored_types:                  0
% 51.21/7.02  sat_num_of_epr_types:                   0
% 51.21/7.02  sat_num_of_non_cyclic_types:            0
% 51.21/7.02  sat_guarded_non_collapsed_types:        0
% 51.21/7.02  num_pure_diseq_elim:                    0
% 51.21/7.02  simp_replaced_by:                       0
% 51.21/7.02  res_preprocessed:                       31
% 51.21/7.02  prep_upred:                             0
% 51.21/7.02  prep_unflattend:                        4
% 51.21/7.02  smt_new_axioms:                         0
% 51.21/7.02  pred_elim_cands:                        0
% 51.21/7.02  pred_elim:                              1
% 51.21/7.02  pred_elim_cl:                           1
% 51.21/7.02  pred_elim_cycles:                       2
% 51.21/7.02  merged_defs:                            0
% 51.21/7.02  merged_defs_ncl:                        0
% 51.21/7.02  bin_hyper_res:                          0
% 51.21/7.02  prep_cycles:                            3
% 51.21/7.02  pred_elim_time:                         0.
% 51.21/7.02  splitting_time:                         0.
% 51.21/7.02  sem_filter_time:                        0.
% 51.21/7.02  monotx_time:                            0.
% 51.21/7.02  subtype_inf_time:                       0.
% 51.21/7.02  
% 51.21/7.02  ------ Problem properties
% 51.21/7.02  
% 51.21/7.02  clauses:                                8
% 51.21/7.02  conjectures:                            2
% 51.21/7.02  epr:                                    1
% 51.21/7.02  horn:                                   8
% 51.21/7.02  ground:                                 4
% 51.21/7.02  unary:                                  8
% 51.21/7.02  binary:                                 0
% 51.21/7.02  lits:                                   8
% 51.21/7.02  lits_eq:                                8
% 51.21/7.02  fd_pure:                                0
% 51.21/7.02  fd_pseudo:                              0
% 51.21/7.02  fd_cond:                                0
% 51.21/7.02  fd_pseudo_cond:                         0
% 51.21/7.02  ac_symbols:                             0
% 51.21/7.02  
% 51.21/7.02  ------ Propositional Solver
% 51.21/7.02  
% 51.21/7.02  prop_solver_calls:                      17
% 51.21/7.02  prop_fast_solver_calls:                 80
% 51.21/7.02  smt_solver_calls:                       0
% 51.21/7.02  smt_fast_solver_calls:                  0
% 51.21/7.02  prop_num_of_clauses:                    349
% 51.21/7.02  prop_preprocess_simplified:             562
% 51.21/7.02  prop_fo_subsumed:                       0
% 51.21/7.02  prop_solver_time:                       0.
% 51.21/7.02  smt_solver_time:                        0.
% 51.21/7.02  smt_fast_solver_time:                   0.
% 51.21/7.02  prop_fast_solver_time:                  0.
% 51.21/7.02  prop_unsat_core_time:                   0.
% 51.21/7.02  
% 51.21/7.02  ------ QBF
% 51.21/7.02  
% 51.21/7.02  qbf_q_res:                              0
% 51.21/7.02  qbf_num_tautologies:                    0
% 51.21/7.02  qbf_prep_cycles:                        0
% 51.21/7.02  
% 51.21/7.02  ------ BMC1
% 51.21/7.02  
% 51.21/7.02  bmc1_current_bound:                     -1
% 51.21/7.02  bmc1_last_solved_bound:                 -1
% 51.21/7.02  bmc1_unsat_core_size:                   -1
% 51.21/7.02  bmc1_unsat_core_parents_size:           -1
% 51.21/7.02  bmc1_merge_next_fun:                    0
% 51.21/7.02  bmc1_unsat_core_clauses_time:           0.
% 51.21/7.02  
% 51.21/7.02  ------ Instantiation
% 51.21/7.02  
% 51.21/7.02  inst_num_of_clauses:                    0
% 51.21/7.02  inst_num_in_passive:                    0
% 51.21/7.02  inst_num_in_active:                     0
% 51.21/7.02  inst_num_in_unprocessed:                0
% 51.21/7.02  inst_num_of_loops:                      0
% 51.21/7.02  inst_num_of_learning_restarts:          0
% 51.21/7.02  inst_num_moves_active_passive:          0
% 51.21/7.02  inst_lit_activity:                      0
% 51.21/7.02  inst_lit_activity_moves:                0
% 51.21/7.02  inst_num_tautologies:                   0
% 51.21/7.02  inst_num_prop_implied:                  0
% 51.21/7.02  inst_num_existing_simplified:           0
% 51.21/7.02  inst_num_eq_res_simplified:             0
% 51.21/7.02  inst_num_child_elim:                    0
% 51.21/7.02  inst_num_of_dismatching_blockings:      0
% 51.21/7.02  inst_num_of_non_proper_insts:           0
% 51.21/7.02  inst_num_of_duplicates:                 0
% 51.21/7.02  inst_inst_num_from_inst_to_res:         0
% 51.21/7.02  inst_dismatching_checking_time:         0.
% 51.21/7.02  
% 51.21/7.02  ------ Resolution
% 51.21/7.02  
% 51.21/7.02  res_num_of_clauses:                     0
% 51.21/7.02  res_num_in_passive:                     0
% 51.21/7.02  res_num_in_active:                      0
% 51.21/7.02  res_num_of_loops:                       34
% 51.21/7.02  res_forward_subset_subsumed:            0
% 51.21/7.02  res_backward_subset_subsumed:           0
% 51.21/7.02  res_forward_subsumed:                   0
% 51.21/7.02  res_backward_subsumed:                  0
% 51.21/7.02  res_forward_subsumption_resolution:     0
% 51.21/7.02  res_backward_subsumption_resolution:    0
% 51.21/7.02  res_clause_to_clause_subsumption:       102995
% 51.21/7.02  res_orphan_elimination:                 0
% 51.21/7.02  res_tautology_del:                      0
% 51.21/7.02  res_num_eq_res_simplified:              0
% 51.21/7.02  res_num_sel_changes:                    0
% 51.21/7.02  res_moves_from_active_to_pass:          0
% 51.21/7.02  
% 51.21/7.02  ------ Superposition
% 51.21/7.02  
% 51.21/7.02  sup_time_total:                         0.
% 51.21/7.02  sup_time_generating:                    0.
% 51.21/7.02  sup_time_sim_full:                      0.
% 51.21/7.02  sup_time_sim_immed:                     0.
% 51.21/7.02  
% 51.21/7.02  sup_num_of_clauses:                     265
% 51.21/7.02  sup_num_in_active:                      248
% 51.21/7.02  sup_num_in_passive:                     17
% 51.21/7.02  sup_num_of_loops:                       251
% 51.21/7.02  sup_fw_superposition:                   91953
% 51.21/7.02  sup_bw_superposition:                   52116
% 51.21/7.02  sup_immediate_simplified:               101432
% 51.21/7.02  sup_given_eliminated:                   0
% 51.21/7.02  comparisons_done:                       0
% 51.21/7.02  comparisons_avoided:                    0
% 51.21/7.02  
% 51.21/7.02  ------ Simplifications
% 51.21/7.02  
% 51.21/7.02  
% 51.21/7.02  sim_fw_subset_subsumed:                 0
% 51.21/7.02  sim_bw_subset_subsumed:                 0
% 51.21/7.02  sim_fw_subsumed:                        251
% 51.21/7.02  sim_bw_subsumed:                        4
% 51.21/7.02  sim_fw_subsumption_res:                 0
% 51.21/7.02  sim_bw_subsumption_res:                 0
% 51.21/7.02  sim_tautology_del:                      0
% 51.21/7.02  sim_eq_tautology_del:                   16620
% 51.21/7.02  sim_eq_res_simp:                        0
% 51.21/7.02  sim_fw_demodulated:                     78363
% 51.21/7.02  sim_bw_demodulated:                     14
% 51.21/7.02  sim_light_normalised:                   71585
% 51.21/7.02  sim_joinable_taut:                      0
% 51.21/7.02  sim_joinable_simp:                      0
% 51.21/7.02  sim_ac_normalised:                      0
% 51.21/7.02  sim_smt_subsumption:                    0
% 51.21/7.02  
%------------------------------------------------------------------------------
