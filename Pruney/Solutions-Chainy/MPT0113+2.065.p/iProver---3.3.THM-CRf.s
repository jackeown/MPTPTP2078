%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:53 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  108 (1655 expanded)
%              Number of clauses        :   72 ( 521 expanded)
%              Number of leaves         :   12 ( 488 expanded)
%              Depth                    :   24
%              Number of atoms          :  152 (1832 expanded)
%              Number of equality atoms :   86 (1571 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f25,f19,f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f26,f19,f19,f19])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f24,f19])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f29,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f29,f19])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f27,f19])).

fof(f30,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_230,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_231,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1298,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_230,c_231])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_610,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_28820,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1298,c_610])).

cnf(c_6,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_28828,plain,
    ( k2_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_1298,c_6])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_609,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_233,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_3])).

cnf(c_613,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_609,c_3,c_233])).

cnf(c_802,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_613,c_0])).

cnf(c_808,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_802,c_3,c_233])).

cnf(c_810,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_808,c_613])).

cnf(c_812,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k2_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_808,c_6])).

cnf(c_823,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_812,c_0,c_810])).

cnf(c_1064,plain,
    ( k3_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_808,c_823])).

cnf(c_1066,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1064,c_808])).

cnf(c_28960,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X2)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_28828,c_810,c_1066])).

cnf(c_28964,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_28820,c_1298,c_28960])).

cnf(c_28965,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28964,c_3,c_810])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_229,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1299,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_229,c_231])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_625,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_7105,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X0)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1299,c_625])).

cnf(c_622,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_5948,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) ),
    inference(superposition,[status(thm)],[c_1299,c_622])).

cnf(c_6010,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) ),
    inference(demodulation,[status(thm)],[c_5948,c_810,c_1066])).

cnf(c_7202,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X0)),k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7105,c_1299,c_6010])).

cnf(c_611,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_230])).

cnf(c_736,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_611])).

cnf(c_1302,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_736,c_231])).

cnf(c_7203,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7202,c_810,c_1302])).

cnf(c_628,plain,
    ( r1_tarski(k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_230])).

cnf(c_1363,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_628])).

cnf(c_1520,plain,
    ( r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1299,c_1363])).

cnf(c_1682,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) = k2_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1520,c_231])).

cnf(c_2025,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k2_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(sK0,k3_xboole_0(sK0,X1)))),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_1682,c_6])).

cnf(c_2029,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(sK0,k3_xboole_0(sK0,X1)))),k3_xboole_0(X0,sK0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2025,c_3,c_233,c_810])).

cnf(c_626,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))) = k2_xboole_0(k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)),k3_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_8348,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),sK0)),k3_xboole_0(k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),sK0)),X2)))) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_2029,c_626])).

cnf(c_8444,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_8348,c_3,c_233,c_810,c_1302,c_1682])).

cnf(c_8613,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8444,c_8])).

cnf(c_8787,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),X0) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_808,c_8613])).

cnf(c_8817,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8787,c_808,c_810])).

cnf(c_9670,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7203,c_8817])).

cnf(c_29405,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_28965,c_9670])).

cnf(c_29463,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29405,c_3,c_233,c_810])).

cnf(c_7,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_78,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_79,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_78])).

cnf(c_228,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_29691,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_29463,c_228])).

cnf(c_29907,plain,
    ( sK0 != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29691,c_233])).

cnf(c_29908,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_29907])).

cnf(c_275,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_324,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_325,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_255,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1)
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_307,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_308,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) != iProver_top
    | r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != iProver_top
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_11,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29908,c_325,c_308,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:58:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.65/2.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.65/2.05  
% 11.65/2.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/2.05  
% 11.65/2.05  ------  iProver source info
% 11.65/2.05  
% 11.65/2.05  git: date: 2020-06-30 10:37:57 +0100
% 11.65/2.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/2.05  git: non_committed_changes: false
% 11.65/2.05  git: last_make_outside_of_git: false
% 11.65/2.05  
% 11.65/2.05  ------ 
% 11.65/2.05  
% 11.65/2.05  ------ Input Options
% 11.65/2.05  
% 11.65/2.05  --out_options                           all
% 11.65/2.05  --tptp_safe_out                         true
% 11.65/2.05  --problem_path                          ""
% 11.65/2.05  --include_path                          ""
% 11.65/2.05  --clausifier                            res/vclausify_rel
% 11.65/2.05  --clausifier_options                    ""
% 11.65/2.05  --stdin                                 false
% 11.65/2.05  --stats_out                             all
% 11.65/2.05  
% 11.65/2.05  ------ General Options
% 11.65/2.05  
% 11.65/2.05  --fof                                   false
% 11.65/2.05  --time_out_real                         305.
% 11.65/2.05  --time_out_virtual                      -1.
% 11.65/2.05  --symbol_type_check                     false
% 11.65/2.05  --clausify_out                          false
% 11.65/2.05  --sig_cnt_out                           false
% 11.65/2.05  --trig_cnt_out                          false
% 11.65/2.05  --trig_cnt_out_tolerance                1.
% 11.65/2.05  --trig_cnt_out_sk_spl                   false
% 11.65/2.05  --abstr_cl_out                          false
% 11.65/2.05  
% 11.65/2.05  ------ Global Options
% 11.65/2.05  
% 11.65/2.05  --schedule                              default
% 11.65/2.05  --add_important_lit                     false
% 11.65/2.05  --prop_solver_per_cl                    1000
% 11.65/2.05  --min_unsat_core                        false
% 11.65/2.05  --soft_assumptions                      false
% 11.65/2.05  --soft_lemma_size                       3
% 11.65/2.05  --prop_impl_unit_size                   0
% 11.65/2.05  --prop_impl_unit                        []
% 11.65/2.05  --share_sel_clauses                     true
% 11.65/2.05  --reset_solvers                         false
% 11.65/2.05  --bc_imp_inh                            [conj_cone]
% 11.65/2.05  --conj_cone_tolerance                   3.
% 11.65/2.05  --extra_neg_conj                        none
% 11.65/2.05  --large_theory_mode                     true
% 11.65/2.05  --prolific_symb_bound                   200
% 11.65/2.05  --lt_threshold                          2000
% 11.65/2.05  --clause_weak_htbl                      true
% 11.65/2.05  --gc_record_bc_elim                     false
% 11.65/2.05  
% 11.65/2.05  ------ Preprocessing Options
% 11.65/2.05  
% 11.65/2.05  --preprocessing_flag                    true
% 11.65/2.05  --time_out_prep_mult                    0.1
% 11.65/2.05  --splitting_mode                        input
% 11.65/2.05  --splitting_grd                         true
% 11.65/2.05  --splitting_cvd                         false
% 11.65/2.05  --splitting_cvd_svl                     false
% 11.65/2.05  --splitting_nvd                         32
% 11.65/2.05  --sub_typing                            true
% 11.65/2.05  --prep_gs_sim                           true
% 11.65/2.05  --prep_unflatten                        true
% 11.65/2.05  --prep_res_sim                          true
% 11.65/2.05  --prep_upred                            true
% 11.65/2.05  --prep_sem_filter                       exhaustive
% 11.65/2.05  --prep_sem_filter_out                   false
% 11.65/2.05  --pred_elim                             true
% 11.65/2.05  --res_sim_input                         true
% 11.65/2.05  --eq_ax_congr_red                       true
% 11.65/2.05  --pure_diseq_elim                       true
% 11.65/2.05  --brand_transform                       false
% 11.65/2.05  --non_eq_to_eq                          false
% 11.65/2.05  --prep_def_merge                        true
% 11.65/2.05  --prep_def_merge_prop_impl              false
% 11.65/2.05  --prep_def_merge_mbd                    true
% 11.65/2.05  --prep_def_merge_tr_red                 false
% 11.65/2.05  --prep_def_merge_tr_cl                  false
% 11.65/2.05  --smt_preprocessing                     true
% 11.65/2.05  --smt_ac_axioms                         fast
% 11.65/2.05  --preprocessed_out                      false
% 11.65/2.05  --preprocessed_stats                    false
% 11.65/2.05  
% 11.65/2.05  ------ Abstraction refinement Options
% 11.65/2.05  
% 11.65/2.05  --abstr_ref                             []
% 11.65/2.05  --abstr_ref_prep                        false
% 11.65/2.05  --abstr_ref_until_sat                   false
% 11.65/2.05  --abstr_ref_sig_restrict                funpre
% 11.65/2.05  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.05  --abstr_ref_under                       []
% 11.65/2.05  
% 11.65/2.05  ------ SAT Options
% 11.65/2.05  
% 11.65/2.05  --sat_mode                              false
% 11.65/2.05  --sat_fm_restart_options                ""
% 11.65/2.05  --sat_gr_def                            false
% 11.65/2.05  --sat_epr_types                         true
% 11.65/2.05  --sat_non_cyclic_types                  false
% 11.65/2.05  --sat_finite_models                     false
% 11.65/2.05  --sat_fm_lemmas                         false
% 11.65/2.05  --sat_fm_prep                           false
% 11.65/2.05  --sat_fm_uc_incr                        true
% 11.65/2.05  --sat_out_model                         small
% 11.65/2.05  --sat_out_clauses                       false
% 11.65/2.05  
% 11.65/2.05  ------ QBF Options
% 11.65/2.05  
% 11.65/2.05  --qbf_mode                              false
% 11.65/2.05  --qbf_elim_univ                         false
% 11.65/2.05  --qbf_dom_inst                          none
% 11.65/2.05  --qbf_dom_pre_inst                      false
% 11.65/2.05  --qbf_sk_in                             false
% 11.65/2.05  --qbf_pred_elim                         true
% 11.65/2.05  --qbf_split                             512
% 11.65/2.05  
% 11.65/2.05  ------ BMC1 Options
% 11.65/2.05  
% 11.65/2.05  --bmc1_incremental                      false
% 11.65/2.05  --bmc1_axioms                           reachable_all
% 11.65/2.05  --bmc1_min_bound                        0
% 11.65/2.05  --bmc1_max_bound                        -1
% 11.65/2.05  --bmc1_max_bound_default                -1
% 11.65/2.05  --bmc1_symbol_reachability              true
% 11.65/2.05  --bmc1_property_lemmas                  false
% 11.65/2.05  --bmc1_k_induction                      false
% 11.65/2.05  --bmc1_non_equiv_states                 false
% 11.65/2.05  --bmc1_deadlock                         false
% 11.65/2.05  --bmc1_ucm                              false
% 11.65/2.05  --bmc1_add_unsat_core                   none
% 11.65/2.05  --bmc1_unsat_core_children              false
% 11.65/2.05  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.05  --bmc1_out_stat                         full
% 11.65/2.05  --bmc1_ground_init                      false
% 11.65/2.05  --bmc1_pre_inst_next_state              false
% 11.65/2.05  --bmc1_pre_inst_state                   false
% 11.65/2.05  --bmc1_pre_inst_reach_state             false
% 11.65/2.05  --bmc1_out_unsat_core                   false
% 11.65/2.05  --bmc1_aig_witness_out                  false
% 11.65/2.05  --bmc1_verbose                          false
% 11.65/2.05  --bmc1_dump_clauses_tptp                false
% 11.65/2.05  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.05  --bmc1_dump_file                        -
% 11.65/2.05  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.05  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.05  --bmc1_ucm_extend_mode                  1
% 11.65/2.05  --bmc1_ucm_init_mode                    2
% 11.65/2.05  --bmc1_ucm_cone_mode                    none
% 11.65/2.05  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.05  --bmc1_ucm_relax_model                  4
% 11.65/2.05  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.05  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.05  --bmc1_ucm_layered_model                none
% 11.65/2.05  --bmc1_ucm_max_lemma_size               10
% 11.65/2.05  
% 11.65/2.05  ------ AIG Options
% 11.65/2.05  
% 11.65/2.05  --aig_mode                              false
% 11.65/2.05  
% 11.65/2.05  ------ Instantiation Options
% 11.65/2.05  
% 11.65/2.05  --instantiation_flag                    true
% 11.65/2.05  --inst_sos_flag                         true
% 11.65/2.05  --inst_sos_phase                        true
% 11.65/2.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.05  --inst_lit_sel_side                     num_symb
% 11.65/2.05  --inst_solver_per_active                1400
% 11.65/2.05  --inst_solver_calls_frac                1.
% 11.65/2.05  --inst_passive_queue_type               priority_queues
% 11.65/2.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.05  --inst_passive_queues_freq              [25;2]
% 11.65/2.05  --inst_dismatching                      true
% 11.65/2.05  --inst_eager_unprocessed_to_passive     true
% 11.65/2.05  --inst_prop_sim_given                   true
% 11.65/2.05  --inst_prop_sim_new                     false
% 11.65/2.05  --inst_subs_new                         false
% 11.65/2.05  --inst_eq_res_simp                      false
% 11.65/2.05  --inst_subs_given                       false
% 11.65/2.05  --inst_orphan_elimination               true
% 11.65/2.05  --inst_learning_loop_flag               true
% 11.65/2.05  --inst_learning_start                   3000
% 11.65/2.05  --inst_learning_factor                  2
% 11.65/2.05  --inst_start_prop_sim_after_learn       3
% 11.65/2.05  --inst_sel_renew                        solver
% 11.65/2.05  --inst_lit_activity_flag                true
% 11.65/2.05  --inst_restr_to_given                   false
% 11.65/2.05  --inst_activity_threshold               500
% 11.65/2.05  --inst_out_proof                        true
% 11.65/2.05  
% 11.65/2.05  ------ Resolution Options
% 11.65/2.05  
% 11.65/2.05  --resolution_flag                       true
% 11.65/2.05  --res_lit_sel                           adaptive
% 11.65/2.05  --res_lit_sel_side                      none
% 11.65/2.05  --res_ordering                          kbo
% 11.65/2.05  --res_to_prop_solver                    active
% 11.65/2.05  --res_prop_simpl_new                    false
% 11.65/2.05  --res_prop_simpl_given                  true
% 11.65/2.05  --res_passive_queue_type                priority_queues
% 11.65/2.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.05  --res_passive_queues_freq               [15;5]
% 11.65/2.05  --res_forward_subs                      full
% 11.65/2.05  --res_backward_subs                     full
% 11.65/2.05  --res_forward_subs_resolution           true
% 11.65/2.05  --res_backward_subs_resolution          true
% 11.65/2.05  --res_orphan_elimination                true
% 11.65/2.05  --res_time_limit                        2.
% 11.65/2.05  --res_out_proof                         true
% 11.65/2.05  
% 11.65/2.05  ------ Superposition Options
% 11.65/2.05  
% 11.65/2.05  --superposition_flag                    true
% 11.65/2.05  --sup_passive_queue_type                priority_queues
% 11.65/2.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.05  --sup_passive_queues_freq               [8;1;4]
% 11.65/2.05  --demod_completeness_check              fast
% 11.65/2.05  --demod_use_ground                      true
% 11.65/2.05  --sup_to_prop_solver                    passive
% 11.65/2.05  --sup_prop_simpl_new                    true
% 11.65/2.05  --sup_prop_simpl_given                  true
% 11.65/2.05  --sup_fun_splitting                     true
% 11.65/2.05  --sup_smt_interval                      50000
% 11.65/2.05  
% 11.65/2.05  ------ Superposition Simplification Setup
% 11.65/2.05  
% 11.65/2.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/2.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/2.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/2.05  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/2.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/2.05  --sup_immed_triv                        [TrivRules]
% 11.65/2.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.05  --sup_immed_bw_main                     []
% 11.65/2.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/2.05  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.05  --sup_input_bw                          []
% 11.65/2.05  
% 11.65/2.05  ------ Combination Options
% 11.65/2.05  
% 11.65/2.05  --comb_res_mult                         3
% 11.65/2.05  --comb_sup_mult                         2
% 11.65/2.05  --comb_inst_mult                        10
% 11.65/2.05  
% 11.65/2.05  ------ Debug Options
% 11.65/2.05  
% 11.65/2.05  --dbg_backtrace                         false
% 11.65/2.05  --dbg_dump_prop_clauses                 false
% 11.65/2.05  --dbg_dump_prop_clauses_file            -
% 11.65/2.05  --dbg_out_stat                          false
% 11.65/2.05  ------ Parsing...
% 11.65/2.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/2.05  
% 11.65/2.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.65/2.05  
% 11.65/2.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/2.05  
% 11.65/2.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/2.05  ------ Proving...
% 11.65/2.05  ------ Problem Properties 
% 11.65/2.05  
% 11.65/2.05  
% 11.65/2.05  clauses                                 10
% 11.65/2.05  conjectures                             1
% 11.65/2.05  EPR                                     1
% 11.65/2.05  Horn                                    10
% 11.65/2.05  unary                                   7
% 11.65/2.05  binary                                  2
% 11.65/2.05  lits                                    14
% 11.65/2.05  lits eq                                 7
% 11.65/2.05  fd_pure                                 0
% 11.65/2.05  fd_pseudo                               0
% 11.65/2.05  fd_cond                                 0
% 11.65/2.05  fd_pseudo_cond                          0
% 11.65/2.05  AC symbols                              0
% 11.65/2.05  
% 11.65/2.05  ------ Schedule dynamic 5 is on 
% 11.65/2.05  
% 11.65/2.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.65/2.05  
% 11.65/2.05  
% 11.65/2.05  ------ 
% 11.65/2.05  Current options:
% 11.65/2.05  ------ 
% 11.65/2.05  
% 11.65/2.05  ------ Input Options
% 11.65/2.05  
% 11.65/2.05  --out_options                           all
% 11.65/2.05  --tptp_safe_out                         true
% 11.65/2.05  --problem_path                          ""
% 11.65/2.05  --include_path                          ""
% 11.65/2.05  --clausifier                            res/vclausify_rel
% 11.65/2.05  --clausifier_options                    ""
% 11.65/2.05  --stdin                                 false
% 11.65/2.05  --stats_out                             all
% 11.65/2.05  
% 11.65/2.05  ------ General Options
% 11.65/2.05  
% 11.65/2.05  --fof                                   false
% 11.65/2.05  --time_out_real                         305.
% 11.65/2.05  --time_out_virtual                      -1.
% 11.65/2.05  --symbol_type_check                     false
% 11.65/2.05  --clausify_out                          false
% 11.65/2.05  --sig_cnt_out                           false
% 11.65/2.05  --trig_cnt_out                          false
% 11.65/2.05  --trig_cnt_out_tolerance                1.
% 11.65/2.05  --trig_cnt_out_sk_spl                   false
% 11.65/2.05  --abstr_cl_out                          false
% 11.65/2.05  
% 11.65/2.05  ------ Global Options
% 11.65/2.05  
% 11.65/2.05  --schedule                              default
% 11.65/2.05  --add_important_lit                     false
% 11.65/2.05  --prop_solver_per_cl                    1000
% 11.65/2.05  --min_unsat_core                        false
% 11.65/2.05  --soft_assumptions                      false
% 11.65/2.05  --soft_lemma_size                       3
% 11.65/2.05  --prop_impl_unit_size                   0
% 11.65/2.05  --prop_impl_unit                        []
% 11.65/2.05  --share_sel_clauses                     true
% 11.65/2.05  --reset_solvers                         false
% 11.65/2.05  --bc_imp_inh                            [conj_cone]
% 11.65/2.05  --conj_cone_tolerance                   3.
% 11.65/2.05  --extra_neg_conj                        none
% 11.65/2.05  --large_theory_mode                     true
% 11.65/2.05  --prolific_symb_bound                   200
% 11.65/2.05  --lt_threshold                          2000
% 11.65/2.05  --clause_weak_htbl                      true
% 11.65/2.05  --gc_record_bc_elim                     false
% 11.65/2.05  
% 11.65/2.05  ------ Preprocessing Options
% 11.65/2.05  
% 11.65/2.05  --preprocessing_flag                    true
% 11.65/2.05  --time_out_prep_mult                    0.1
% 11.65/2.05  --splitting_mode                        input
% 11.65/2.05  --splitting_grd                         true
% 11.65/2.05  --splitting_cvd                         false
% 11.65/2.05  --splitting_cvd_svl                     false
% 11.65/2.05  --splitting_nvd                         32
% 11.65/2.05  --sub_typing                            true
% 11.65/2.05  --prep_gs_sim                           true
% 11.65/2.05  --prep_unflatten                        true
% 11.65/2.05  --prep_res_sim                          true
% 11.65/2.05  --prep_upred                            true
% 11.65/2.05  --prep_sem_filter                       exhaustive
% 11.65/2.05  --prep_sem_filter_out                   false
% 11.65/2.05  --pred_elim                             true
% 11.65/2.05  --res_sim_input                         true
% 11.65/2.05  --eq_ax_congr_red                       true
% 11.65/2.05  --pure_diseq_elim                       true
% 11.65/2.05  --brand_transform                       false
% 11.65/2.05  --non_eq_to_eq                          false
% 11.65/2.05  --prep_def_merge                        true
% 11.65/2.05  --prep_def_merge_prop_impl              false
% 11.65/2.05  --prep_def_merge_mbd                    true
% 11.65/2.05  --prep_def_merge_tr_red                 false
% 11.65/2.05  --prep_def_merge_tr_cl                  false
% 11.65/2.05  --smt_preprocessing                     true
% 11.65/2.05  --smt_ac_axioms                         fast
% 11.65/2.05  --preprocessed_out                      false
% 11.65/2.05  --preprocessed_stats                    false
% 11.65/2.05  
% 11.65/2.05  ------ Abstraction refinement Options
% 11.65/2.05  
% 11.65/2.05  --abstr_ref                             []
% 11.65/2.05  --abstr_ref_prep                        false
% 11.65/2.05  --abstr_ref_until_sat                   false
% 11.65/2.05  --abstr_ref_sig_restrict                funpre
% 11.65/2.05  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.05  --abstr_ref_under                       []
% 11.65/2.05  
% 11.65/2.05  ------ SAT Options
% 11.65/2.05  
% 11.65/2.05  --sat_mode                              false
% 11.65/2.05  --sat_fm_restart_options                ""
% 11.65/2.05  --sat_gr_def                            false
% 11.65/2.05  --sat_epr_types                         true
% 11.65/2.05  --sat_non_cyclic_types                  false
% 11.65/2.05  --sat_finite_models                     false
% 11.65/2.05  --sat_fm_lemmas                         false
% 11.65/2.05  --sat_fm_prep                           false
% 11.65/2.05  --sat_fm_uc_incr                        true
% 11.65/2.05  --sat_out_model                         small
% 11.65/2.05  --sat_out_clauses                       false
% 11.65/2.05  
% 11.65/2.05  ------ QBF Options
% 11.65/2.05  
% 11.65/2.05  --qbf_mode                              false
% 11.65/2.05  --qbf_elim_univ                         false
% 11.65/2.05  --qbf_dom_inst                          none
% 11.65/2.05  --qbf_dom_pre_inst                      false
% 11.65/2.05  --qbf_sk_in                             false
% 11.65/2.05  --qbf_pred_elim                         true
% 11.65/2.05  --qbf_split                             512
% 11.65/2.05  
% 11.65/2.05  ------ BMC1 Options
% 11.65/2.05  
% 11.65/2.05  --bmc1_incremental                      false
% 11.65/2.05  --bmc1_axioms                           reachable_all
% 11.65/2.05  --bmc1_min_bound                        0
% 11.65/2.05  --bmc1_max_bound                        -1
% 11.65/2.05  --bmc1_max_bound_default                -1
% 11.65/2.05  --bmc1_symbol_reachability              true
% 11.65/2.05  --bmc1_property_lemmas                  false
% 11.65/2.05  --bmc1_k_induction                      false
% 11.65/2.05  --bmc1_non_equiv_states                 false
% 11.65/2.05  --bmc1_deadlock                         false
% 11.65/2.05  --bmc1_ucm                              false
% 11.65/2.05  --bmc1_add_unsat_core                   none
% 11.65/2.05  --bmc1_unsat_core_children              false
% 11.65/2.05  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.05  --bmc1_out_stat                         full
% 11.65/2.05  --bmc1_ground_init                      false
% 11.65/2.05  --bmc1_pre_inst_next_state              false
% 11.65/2.05  --bmc1_pre_inst_state                   false
% 11.65/2.05  --bmc1_pre_inst_reach_state             false
% 11.65/2.05  --bmc1_out_unsat_core                   false
% 11.65/2.05  --bmc1_aig_witness_out                  false
% 11.65/2.05  --bmc1_verbose                          false
% 11.65/2.05  --bmc1_dump_clauses_tptp                false
% 11.65/2.05  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.05  --bmc1_dump_file                        -
% 11.65/2.05  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.05  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.05  --bmc1_ucm_extend_mode                  1
% 11.65/2.05  --bmc1_ucm_init_mode                    2
% 11.65/2.05  --bmc1_ucm_cone_mode                    none
% 11.65/2.05  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.05  --bmc1_ucm_relax_model                  4
% 11.65/2.05  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.05  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.05  --bmc1_ucm_layered_model                none
% 11.65/2.05  --bmc1_ucm_max_lemma_size               10
% 11.65/2.05  
% 11.65/2.05  ------ AIG Options
% 11.65/2.05  
% 11.65/2.05  --aig_mode                              false
% 11.65/2.05  
% 11.65/2.05  ------ Instantiation Options
% 11.65/2.05  
% 11.65/2.05  --instantiation_flag                    true
% 11.65/2.05  --inst_sos_flag                         true
% 11.65/2.05  --inst_sos_phase                        true
% 11.65/2.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.05  --inst_lit_sel_side                     none
% 11.65/2.05  --inst_solver_per_active                1400
% 11.65/2.05  --inst_solver_calls_frac                1.
% 11.65/2.05  --inst_passive_queue_type               priority_queues
% 11.65/2.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.05  --inst_passive_queues_freq              [25;2]
% 11.65/2.05  --inst_dismatching                      true
% 11.65/2.05  --inst_eager_unprocessed_to_passive     true
% 11.65/2.05  --inst_prop_sim_given                   true
% 11.65/2.05  --inst_prop_sim_new                     false
% 11.65/2.05  --inst_subs_new                         false
% 11.65/2.05  --inst_eq_res_simp                      false
% 11.65/2.05  --inst_subs_given                       false
% 11.65/2.05  --inst_orphan_elimination               true
% 11.65/2.05  --inst_learning_loop_flag               true
% 11.65/2.05  --inst_learning_start                   3000
% 11.65/2.05  --inst_learning_factor                  2
% 11.65/2.05  --inst_start_prop_sim_after_learn       3
% 11.65/2.05  --inst_sel_renew                        solver
% 11.65/2.05  --inst_lit_activity_flag                true
% 11.65/2.05  --inst_restr_to_given                   false
% 11.65/2.05  --inst_activity_threshold               500
% 11.65/2.05  --inst_out_proof                        true
% 11.65/2.05  
% 11.65/2.05  ------ Resolution Options
% 11.65/2.05  
% 11.65/2.05  --resolution_flag                       false
% 11.65/2.05  --res_lit_sel                           adaptive
% 11.65/2.05  --res_lit_sel_side                      none
% 11.65/2.05  --res_ordering                          kbo
% 11.65/2.05  --res_to_prop_solver                    active
% 11.65/2.05  --res_prop_simpl_new                    false
% 11.65/2.05  --res_prop_simpl_given                  true
% 11.65/2.05  --res_passive_queue_type                priority_queues
% 11.65/2.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.05  --res_passive_queues_freq               [15;5]
% 11.65/2.05  --res_forward_subs                      full
% 11.65/2.05  --res_backward_subs                     full
% 11.65/2.05  --res_forward_subs_resolution           true
% 11.65/2.05  --res_backward_subs_resolution          true
% 11.65/2.05  --res_orphan_elimination                true
% 11.65/2.05  --res_time_limit                        2.
% 11.65/2.05  --res_out_proof                         true
% 11.65/2.05  
% 11.65/2.05  ------ Superposition Options
% 11.65/2.05  
% 11.65/2.05  --superposition_flag                    true
% 11.65/2.05  --sup_passive_queue_type                priority_queues
% 11.65/2.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.05  --sup_passive_queues_freq               [8;1;4]
% 11.65/2.05  --demod_completeness_check              fast
% 11.65/2.05  --demod_use_ground                      true
% 11.65/2.05  --sup_to_prop_solver                    passive
% 11.65/2.05  --sup_prop_simpl_new                    true
% 11.65/2.05  --sup_prop_simpl_given                  true
% 11.65/2.05  --sup_fun_splitting                     true
% 11.65/2.05  --sup_smt_interval                      50000
% 11.65/2.05  
% 11.65/2.05  ------ Superposition Simplification Setup
% 11.65/2.05  
% 11.65/2.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/2.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/2.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/2.05  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/2.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/2.05  --sup_immed_triv                        [TrivRules]
% 11.65/2.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.05  --sup_immed_bw_main                     []
% 11.65/2.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/2.05  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.05  --sup_input_bw                          []
% 11.65/2.05  
% 11.65/2.05  ------ Combination Options
% 11.65/2.05  
% 11.65/2.05  --comb_res_mult                         3
% 11.65/2.05  --comb_sup_mult                         2
% 11.65/2.05  --comb_inst_mult                        10
% 11.65/2.05  
% 11.65/2.05  ------ Debug Options
% 11.65/2.05  
% 11.65/2.05  --dbg_backtrace                         false
% 11.65/2.05  --dbg_dump_prop_clauses                 false
% 11.65/2.05  --dbg_dump_prop_clauses_file            -
% 11.65/2.05  --dbg_out_stat                          false
% 11.65/2.05  
% 11.65/2.05  
% 11.65/2.05  
% 11.65/2.05  
% 11.65/2.05  ------ Proving...
% 11.65/2.05  
% 11.65/2.05  
% 11.65/2.05  % SZS status Theorem for theBenchmark.p
% 11.65/2.05  
% 11.65/2.05  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/2.05  
% 11.65/2.05  fof(f5,axiom,(
% 11.65/2.05    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f23,plain,(
% 11.65/2.05    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.65/2.05    inference(cnf_transformation,[],[f5])).
% 11.65/2.05  
% 11.65/2.05  fof(f1,axiom,(
% 11.65/2.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f19,plain,(
% 11.65/2.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.65/2.05    inference(cnf_transformation,[],[f1])).
% 11.65/2.05  
% 11.65/2.05  fof(f32,plain,(
% 11.65/2.05    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 11.65/2.05    inference(definition_unfolding,[],[f23,f19])).
% 11.65/2.05  
% 11.65/2.05  fof(f3,axiom,(
% 11.65/2.05    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f15,plain,(
% 11.65/2.05    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.65/2.05    inference(ennf_transformation,[],[f3])).
% 11.65/2.05  
% 11.65/2.05  fof(f21,plain,(
% 11.65/2.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.65/2.05    inference(cnf_transformation,[],[f15])).
% 11.65/2.05  
% 11.65/2.05  fof(f7,axiom,(
% 11.65/2.05    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f25,plain,(
% 11.65/2.05    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.65/2.05    inference(cnf_transformation,[],[f7])).
% 11.65/2.05  
% 11.65/2.05  fof(f31,plain,(
% 11.65/2.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 11.65/2.05    inference(definition_unfolding,[],[f25,f19,f19])).
% 11.65/2.05  
% 11.65/2.05  fof(f8,axiom,(
% 11.65/2.05    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f26,plain,(
% 11.65/2.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 11.65/2.05    inference(cnf_transformation,[],[f8])).
% 11.65/2.05  
% 11.65/2.05  fof(f34,plain,(
% 11.65/2.05    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2))) )),
% 11.65/2.05    inference(definition_unfolding,[],[f26,f19,f19,f19])).
% 11.65/2.05  
% 11.65/2.05  fof(f4,axiom,(
% 11.65/2.05    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f22,plain,(
% 11.65/2.05    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.65/2.05    inference(cnf_transformation,[],[f4])).
% 11.65/2.05  
% 11.65/2.05  fof(f6,axiom,(
% 11.65/2.05    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f24,plain,(
% 11.65/2.05    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.65/2.05    inference(cnf_transformation,[],[f6])).
% 11.65/2.05  
% 11.65/2.05  fof(f33,plain,(
% 11.65/2.05    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 11.65/2.05    inference(definition_unfolding,[],[f24,f19])).
% 11.65/2.05  
% 11.65/2.05  fof(f11,conjecture,(
% 11.65/2.05    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f12,negated_conjecture,(
% 11.65/2.05    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.65/2.05    inference(negated_conjecture,[],[f11])).
% 11.65/2.05  
% 11.65/2.05  fof(f16,plain,(
% 11.65/2.05    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.65/2.05    inference(ennf_transformation,[],[f12])).
% 11.65/2.05  
% 11.65/2.05  fof(f17,plain,(
% 11.65/2.05    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 11.65/2.05    introduced(choice_axiom,[])).
% 11.65/2.05  
% 11.65/2.05  fof(f18,plain,(
% 11.65/2.05    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 11.65/2.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 11.65/2.05  
% 11.65/2.05  fof(f29,plain,(
% 11.65/2.05    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 11.65/2.05    inference(cnf_transformation,[],[f18])).
% 11.65/2.05  
% 11.65/2.05  fof(f36,plain,(
% 11.65/2.05    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 11.65/2.05    inference(definition_unfolding,[],[f29,f19])).
% 11.65/2.05  
% 11.65/2.05  fof(f10,axiom,(
% 11.65/2.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f28,plain,(
% 11.65/2.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 11.65/2.05    inference(cnf_transformation,[],[f10])).
% 11.65/2.05  
% 11.65/2.05  fof(f9,axiom,(
% 11.65/2.05    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f27,plain,(
% 11.65/2.05    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.65/2.05    inference(cnf_transformation,[],[f9])).
% 11.65/2.05  
% 11.65/2.05  fof(f35,plain,(
% 11.65/2.05    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 11.65/2.05    inference(definition_unfolding,[],[f27,f19])).
% 11.65/2.05  
% 11.65/2.05  fof(f30,plain,(
% 11.65/2.05    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 11.65/2.05    inference(cnf_transformation,[],[f18])).
% 11.65/2.05  
% 11.65/2.05  fof(f2,axiom,(
% 11.65/2.05    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.65/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.05  
% 11.65/2.05  fof(f13,plain,(
% 11.65/2.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.65/2.05    inference(ennf_transformation,[],[f2])).
% 11.65/2.05  
% 11.65/2.05  fof(f14,plain,(
% 11.65/2.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.65/2.05    inference(flattening,[],[f13])).
% 11.65/2.05  
% 11.65/2.05  fof(f20,plain,(
% 11.65/2.05    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.65/2.05    inference(cnf_transformation,[],[f14])).
% 11.65/2.05  
% 11.65/2.05  cnf(c_4,plain,
% 11.65/2.05      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.65/2.05      inference(cnf_transformation,[],[f32]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_230,plain,
% 11.65/2.05      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.65/2.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_2,plain,
% 11.65/2.05      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.65/2.05      inference(cnf_transformation,[],[f21]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_231,plain,
% 11.65/2.05      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.65/2.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1298,plain,
% 11.65/2.05      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_230,c_231]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_0,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 11.65/2.05      inference(cnf_transformation,[],[f31]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_610,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_28820,plain,
% 11.65/2.05      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_1298,c_610]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_6,plain,
% 11.65/2.05      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
% 11.65/2.05      inference(cnf_transformation,[],[f34]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_28828,plain,
% 11.65/2.05      ( k2_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X2)))) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_1298,c_6]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_3,plain,
% 11.65/2.05      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.65/2.05      inference(cnf_transformation,[],[f22]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_609,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_5,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 11.65/2.05      inference(cnf_transformation,[],[f33]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_233,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.65/2.05      inference(light_normalisation,[status(thm)],[c_5,c_3]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_613,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 11.65/2.05      inference(light_normalisation,[status(thm)],[c_609,c_3,c_233]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_802,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_613,c_0]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_808,plain,
% 11.65/2.05      ( k3_xboole_0(X0,X0) = X0 ),
% 11.65/2.05      inference(light_normalisation,[status(thm)],[c_802,c_3,c_233]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_810,plain,
% 11.65/2.05      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_808,c_613]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_812,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k2_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(X0,X1)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_808,c_6]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_823,plain,
% 11.65/2.05      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 11.65/2.05      inference(light_normalisation,[status(thm)],[c_812,c_0,c_810]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1064,plain,
% 11.65/2.05      ( k3_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_808,c_823]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1066,plain,
% 11.65/2.05      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.65/2.05      inference(light_normalisation,[status(thm)],[c_1064,c_808]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_28960,plain,
% 11.65/2.05      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X2)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_28828,c_810,c_1066]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_28964,plain,
% 11.65/2.05      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_28820,c_1298,c_28960]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_28965,plain,
% 11.65/2.05      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_28964,c_3,c_810]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_10,negated_conjecture,
% 11.65/2.05      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 11.65/2.05      inference(cnf_transformation,[],[f36]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_229,plain,
% 11.65/2.05      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 11.65/2.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1299,plain,
% 11.65/2.05      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_229,c_231]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_8,plain,
% 11.65/2.05      ( k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 11.65/2.05      inference(cnf_transformation,[],[f28]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_625,plain,
% 11.65/2.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_7105,plain,
% 11.65/2.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X0)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,X0)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_1299,c_625]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_622,plain,
% 11.65/2.05      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_5948,plain,
% 11.65/2.05      ( k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_1299,c_622]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_6010,plain,
% 11.65/2.05      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_5948,c_810,c_1066]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_7202,plain,
% 11.65/2.05      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X0)),k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X0)) ),
% 11.65/2.05      inference(light_normalisation,[status(thm)],[c_7105,c_1299,c_6010]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_611,plain,
% 11.65/2.05      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_0,c_230]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_736,plain,
% 11.65/2.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_3,c_611]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1302,plain,
% 11.65/2.05      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_736,c_231]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_7203,plain,
% 11.65/2.05      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k1_xboole_0 ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_7202,c_810,c_1302]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_628,plain,
% 11.65/2.05      ( r1_tarski(k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)),X0) = iProver_top ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_6,c_230]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1363,plain,
% 11.65/2.05      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),X0) = iProver_top ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_0,c_628]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1520,plain,
% 11.65/2.05      ( r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) = iProver_top ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_1299,c_1363]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1682,plain,
% 11.65/2.05      ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) = k2_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_1520,c_231]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_2025,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k2_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(sK0,k3_xboole_0(sK0,X1)))),k3_xboole_0(X0,sK0)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_1682,c_6]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_2029,plain,
% 11.65/2.05      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(sK0,k3_xboole_0(sK0,X1)))),k3_xboole_0(X0,sK0)) = X0 ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_2025,c_3,c_233,c_810]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_626,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))) = k2_xboole_0(k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)),k3_xboole_0(X0,X3)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_8348,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),sK0)),k3_xboole_0(k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),sK0)),X2)))) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_2029,c_626]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_8444,plain,
% 11.65/2.05      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 11.65/2.05      inference(demodulation,
% 11.65/2.05                [status(thm)],
% 11.65/2.05                [c_8348,c_3,c_233,c_810,c_1302,c_1682]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_8613,plain,
% 11.65/2.05      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_8444,c_8]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_8787,plain,
% 11.65/2.05      ( k5_xboole_0(k5_xboole_0(X0,X0),X0) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_808,c_8613]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_8817,plain,
% 11.65/2.05      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.65/2.05      inference(light_normalisation,[status(thm)],[c_8787,c_808,c_810]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_9670,plain,
% 11.65/2.05      ( k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k1_xboole_0 ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_7203,c_8817]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_29405,plain,
% 11.65/2.05      ( k5_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)))) = k1_xboole_0 ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_28965,c_9670]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_29463,plain,
% 11.65/2.05      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_29405,c_3,c_233,c_810]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_7,plain,
% 11.65/2.05      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 11.65/2.05      inference(cnf_transformation,[],[f35]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_9,negated_conjecture,
% 11.65/2.05      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 11.65/2.05      inference(cnf_transformation,[],[f30]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_78,plain,
% 11.65/2.05      ( ~ r1_tarski(sK0,sK1)
% 11.65/2.05      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK0
% 11.65/2.05      | sK2 != X1 ),
% 11.65/2.05      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_79,plain,
% 11.65/2.05      ( ~ r1_tarski(sK0,sK1)
% 11.65/2.05      | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0 ),
% 11.65/2.05      inference(unflattening,[status(thm)],[c_78]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_228,plain,
% 11.65/2.05      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0
% 11.65/2.05      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.65/2.05      inference(predicate_to_equality,[status(thm)],[c_79]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_29691,plain,
% 11.65/2.05      ( k5_xboole_0(sK0,k1_xboole_0) != sK0
% 11.65/2.05      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.65/2.05      inference(superposition,[status(thm)],[c_29463,c_228]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_29907,plain,
% 11.65/2.05      ( sK0 != sK0 | r1_tarski(sK0,sK1) != iProver_top ),
% 11.65/2.05      inference(demodulation,[status(thm)],[c_29691,c_233]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_29908,plain,
% 11.65/2.05      ( r1_tarski(sK0,sK1) != iProver_top ),
% 11.65/2.05      inference(equality_resolution_simp,[status(thm)],[c_29907]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_275,plain,
% 11.65/2.05      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) ),
% 11.65/2.05      inference(instantiation,[status(thm)],[c_4]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_324,plain,
% 11.65/2.05      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 11.65/2.05      inference(instantiation,[status(thm)],[c_275]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_325,plain,
% 11.65/2.05      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) = iProver_top ),
% 11.65/2.05      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_1,plain,
% 11.65/2.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 11.65/2.05      inference(cnf_transformation,[],[f20]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_242,plain,
% 11.65/2.05      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK0,X0) | r1_tarski(sK0,sK1) ),
% 11.65/2.05      inference(instantiation,[status(thm)],[c_1]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_255,plain,
% 11.65/2.05      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1)
% 11.65/2.05      | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))
% 11.65/2.05      | r1_tarski(sK0,sK1) ),
% 11.65/2.05      inference(instantiation,[status(thm)],[c_242]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_307,plain,
% 11.65/2.05      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
% 11.65/2.05      | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
% 11.65/2.05      | r1_tarski(sK0,sK1) ),
% 11.65/2.05      inference(instantiation,[status(thm)],[c_255]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_308,plain,
% 11.65/2.05      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) != iProver_top
% 11.65/2.05      | r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != iProver_top
% 11.65/2.05      | r1_tarski(sK0,sK1) = iProver_top ),
% 11.65/2.05      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(c_11,plain,
% 11.65/2.05      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 11.65/2.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.65/2.05  
% 11.65/2.05  cnf(contradiction,plain,
% 11.65/2.05      ( $false ),
% 11.65/2.05      inference(minisat,[status(thm)],[c_29908,c_325,c_308,c_11]) ).
% 11.65/2.05  
% 11.65/2.05  
% 11.65/2.05  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/2.05  
% 11.65/2.05  ------                               Statistics
% 11.65/2.05  
% 11.65/2.05  ------ General
% 11.65/2.05  
% 11.65/2.05  abstr_ref_over_cycles:                  0
% 11.65/2.05  abstr_ref_under_cycles:                 0
% 11.65/2.05  gc_basic_clause_elim:                   0
% 11.65/2.05  forced_gc_time:                         0
% 11.65/2.05  parsing_time:                           0.01
% 11.65/2.05  unif_index_cands_time:                  0.
% 11.65/2.05  unif_index_add_time:                    0.
% 11.65/2.05  orderings_time:                         0.
% 11.65/2.05  out_proof_time:                         0.01
% 11.65/2.05  total_time:                             1.093
% 11.65/2.05  num_of_symbols:                         40
% 11.65/2.05  num_of_terms:                           38566
% 11.65/2.05  
% 11.65/2.05  ------ Preprocessing
% 11.65/2.05  
% 11.65/2.05  num_of_splits:                          0
% 11.65/2.05  num_of_split_atoms:                     0
% 11.65/2.05  num_of_reused_defs:                     0
% 11.65/2.05  num_eq_ax_congr_red:                    0
% 11.65/2.05  num_of_sem_filtered_clauses:            1
% 11.65/2.05  num_of_subtypes:                        0
% 11.65/2.05  monotx_restored_types:                  0
% 11.65/2.05  sat_num_of_epr_types:                   0
% 11.65/2.05  sat_num_of_non_cyclic_types:            0
% 11.65/2.05  sat_guarded_non_collapsed_types:        0
% 11.65/2.05  num_pure_diseq_elim:                    0
% 11.65/2.05  simp_replaced_by:                       0
% 11.65/2.05  res_preprocessed:                       54
% 11.65/2.05  prep_upred:                             0
% 11.65/2.05  prep_unflattend:                        1
% 11.65/2.05  smt_new_axioms:                         0
% 11.65/2.05  pred_elim_cands:                        1
% 11.65/2.05  pred_elim:                              1
% 11.65/2.05  pred_elim_cl:                           1
% 11.65/2.05  pred_elim_cycles:                       3
% 11.65/2.05  merged_defs:                            0
% 11.65/2.05  merged_defs_ncl:                        0
% 11.65/2.05  bin_hyper_res:                          0
% 11.65/2.05  prep_cycles:                            4
% 11.65/2.05  pred_elim_time:                         0.
% 11.65/2.05  splitting_time:                         0.
% 11.65/2.05  sem_filter_time:                        0.
% 11.65/2.05  monotx_time:                            0.
% 11.65/2.05  subtype_inf_time:                       0.
% 11.65/2.05  
% 11.65/2.05  ------ Problem properties
% 11.65/2.05  
% 11.65/2.05  clauses:                                10
% 11.65/2.05  conjectures:                            1
% 11.65/2.05  epr:                                    1
% 11.65/2.05  horn:                                   10
% 11.65/2.05  ground:                                 1
% 11.65/2.05  unary:                                  7
% 11.65/2.05  binary:                                 2
% 11.65/2.05  lits:                                   14
% 11.65/2.05  lits_eq:                                7
% 11.65/2.05  fd_pure:                                0
% 11.65/2.05  fd_pseudo:                              0
% 11.65/2.05  fd_cond:                                0
% 11.65/2.05  fd_pseudo_cond:                         0
% 11.65/2.05  ac_symbols:                             0
% 11.65/2.05  
% 11.65/2.05  ------ Propositional Solver
% 11.65/2.05  
% 11.65/2.05  prop_solver_calls:                      35
% 11.65/2.05  prop_fast_solver_calls:                 443
% 11.65/2.05  smt_solver_calls:                       0
% 11.65/2.05  smt_fast_solver_calls:                  0
% 11.65/2.05  prop_num_of_clauses:                    12279
% 11.65/2.05  prop_preprocess_simplified:             14680
% 11.65/2.05  prop_fo_subsumed:                       10
% 11.65/2.05  prop_solver_time:                       0.
% 11.65/2.05  smt_solver_time:                        0.
% 11.65/2.05  smt_fast_solver_time:                   0.
% 11.65/2.05  prop_fast_solver_time:                  0.
% 11.65/2.05  prop_unsat_core_time:                   0.001
% 11.65/2.05  
% 11.65/2.05  ------ QBF
% 11.65/2.05  
% 11.65/2.05  qbf_q_res:                              0
% 11.65/2.05  qbf_num_tautologies:                    0
% 11.65/2.05  qbf_prep_cycles:                        0
% 11.65/2.05  
% 11.65/2.05  ------ BMC1
% 11.65/2.05  
% 11.65/2.05  bmc1_current_bound:                     -1
% 11.65/2.05  bmc1_last_solved_bound:                 -1
% 11.65/2.05  bmc1_unsat_core_size:                   -1
% 11.65/2.05  bmc1_unsat_core_parents_size:           -1
% 11.65/2.05  bmc1_merge_next_fun:                    0
% 11.65/2.05  bmc1_unsat_core_clauses_time:           0.
% 11.65/2.05  
% 11.65/2.05  ------ Instantiation
% 11.65/2.05  
% 11.65/2.05  inst_num_of_clauses:                    2479
% 11.65/2.05  inst_num_in_passive:                    383
% 11.65/2.05  inst_num_in_active:                     866
% 11.65/2.05  inst_num_in_unprocessed:                1232
% 11.65/2.05  inst_num_of_loops:                      940
% 11.65/2.05  inst_num_of_learning_restarts:          0
% 11.65/2.05  inst_num_moves_active_passive:          69
% 11.65/2.05  inst_lit_activity:                      0
% 11.65/2.05  inst_lit_activity_moves:                0
% 11.65/2.05  inst_num_tautologies:                   0
% 11.65/2.05  inst_num_prop_implied:                  0
% 11.65/2.05  inst_num_existing_simplified:           0
% 11.65/2.05  inst_num_eq_res_simplified:             0
% 11.65/2.05  inst_num_child_elim:                    0
% 11.65/2.05  inst_num_of_dismatching_blockings:      2026
% 11.65/2.05  inst_num_of_non_proper_insts:           3153
% 11.65/2.05  inst_num_of_duplicates:                 0
% 11.65/2.05  inst_inst_num_from_inst_to_res:         0
% 11.65/2.05  inst_dismatching_checking_time:         0.
% 11.65/2.05  
% 11.65/2.05  ------ Resolution
% 11.65/2.05  
% 11.65/2.05  res_num_of_clauses:                     0
% 11.65/2.05  res_num_in_passive:                     0
% 11.65/2.05  res_num_in_active:                      0
% 11.65/2.05  res_num_of_loops:                       58
% 11.65/2.05  res_forward_subset_subsumed:            277
% 11.65/2.05  res_backward_subset_subsumed:           4
% 11.65/2.05  res_forward_subsumed:                   0
% 11.65/2.05  res_backward_subsumed:                  0
% 11.65/2.05  res_forward_subsumption_resolution:     0
% 11.65/2.05  res_backward_subsumption_resolution:    0
% 11.65/2.05  res_clause_to_clause_subsumption:       8590
% 11.65/2.05  res_orphan_elimination:                 0
% 11.65/2.05  res_tautology_del:                      348
% 11.65/2.05  res_num_eq_res_simplified:              0
% 11.65/2.05  res_num_sel_changes:                    0
% 11.65/2.05  res_moves_from_active_to_pass:          0
% 11.65/2.05  
% 11.65/2.05  ------ Superposition
% 11.65/2.05  
% 11.65/2.05  sup_time_total:                         0.
% 11.65/2.05  sup_time_generating:                    0.
% 11.65/2.05  sup_time_sim_full:                      0.
% 11.65/2.05  sup_time_sim_immed:                     0.
% 11.65/2.05  
% 11.65/2.05  sup_num_of_clauses:                     1805
% 11.65/2.05  sup_num_in_active:                      160
% 11.65/2.05  sup_num_in_passive:                     1645
% 11.65/2.05  sup_num_of_loops:                       187
% 11.65/2.05  sup_fw_superposition:                   3457
% 11.65/2.05  sup_bw_superposition:                   2452
% 11.65/2.05  sup_immediate_simplified:               3164
% 11.65/2.05  sup_given_eliminated:                   2
% 11.65/2.05  comparisons_done:                       0
% 11.65/2.05  comparisons_avoided:                    0
% 11.65/2.05  
% 11.65/2.05  ------ Simplifications
% 11.65/2.05  
% 11.65/2.05  
% 11.65/2.05  sim_fw_subset_subsumed:                 22
% 11.65/2.05  sim_bw_subset_subsumed:                 14
% 11.65/2.05  sim_fw_subsumed:                        482
% 11.65/2.05  sim_bw_subsumed:                        60
% 11.65/2.05  sim_fw_subsumption_res:                 0
% 11.65/2.05  sim_bw_subsumption_res:                 0
% 11.65/2.05  sim_tautology_del:                      20
% 11.65/2.05  sim_eq_tautology_del:                   982
% 11.65/2.05  sim_eq_res_simp:                        1
% 11.65/2.05  sim_fw_demodulated:                     2273
% 11.65/2.05  sim_bw_demodulated:                     80
% 11.65/2.05  sim_light_normalised:                   1030
% 11.65/2.05  sim_joinable_taut:                      0
% 11.65/2.05  sim_joinable_simp:                      0
% 11.65/2.05  sim_ac_normalised:                      0
% 11.65/2.05  sim_smt_subsumption:                    0
% 11.65/2.05  
%------------------------------------------------------------------------------
