%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:36 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 272 expanded)
%              Number of clauses        :   49 (  94 expanded)
%              Number of leaves         :   13 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 319 expanded)
%              Number of equality atoms :   79 ( 269 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f24,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f21,f20,f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_224,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_227,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_769,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_224,c_227])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_332,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_337,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_332,c_5])).

cnf(c_338,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_337,c_5,c_6])).

cnf(c_7279,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))))) ),
    inference(superposition,[status(thm)],[c_769,c_338])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_235,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_4])).

cnf(c_428,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_235,c_5])).

cnf(c_440,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_428,c_4])).

cnf(c_7847,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_7279,c_5,c_440])).

cnf(c_7848,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_7847,c_4,c_235])).

cnf(c_1209,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_440,c_6])).

cnf(c_1217,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_440,c_6])).

cnf(c_1235,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(demodulation,[status(thm)],[c_1209,c_1217])).

cnf(c_1237,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_1235,c_5])).

cnf(c_1238,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1237,c_440])).

cnf(c_27532,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_7848,c_1238])).

cnf(c_431,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_235,c_6])).

cnf(c_433,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_431,c_4])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_333,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_3])).

cnf(c_778,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_333,c_4,c_235])).

cnf(c_1007,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_433,c_778])).

cnf(c_27974,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_27532,c_1007])).

cnf(c_7,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2996,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,X0),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8714,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_2996])).

cnf(c_78,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_288,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_1899,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,X0),X1)
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,sK2) != X1
    | sK1 != k4_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_3500,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK0,sK2))
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
    | sK1 != k4_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_8713,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2))
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
    | sK1 != k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_3500])).

cnf(c_77,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_301,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_396,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_1894,plain,
    ( k4_xboole_0(sK1,X0) != sK1
    | sK1 = k4_xboole_0(sK1,X0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_4643,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != sK1
    | sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_76,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_416,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_296,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27974,c_8714,c_8713,c_4643,c_416,c_296,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.76/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.49  
% 7.76/1.49  ------  iProver source info
% 7.76/1.49  
% 7.76/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.49  git: non_committed_changes: false
% 7.76/1.49  git: last_make_outside_of_git: false
% 7.76/1.49  
% 7.76/1.49  ------ 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options
% 7.76/1.49  
% 7.76/1.49  --out_options                           all
% 7.76/1.49  --tptp_safe_out                         true
% 7.76/1.49  --problem_path                          ""
% 7.76/1.49  --include_path                          ""
% 7.76/1.49  --clausifier                            res/vclausify_rel
% 7.76/1.49  --clausifier_options                    --mode clausify
% 7.76/1.49  --stdin                                 false
% 7.76/1.49  --stats_out                             sel
% 7.76/1.49  
% 7.76/1.49  ------ General Options
% 7.76/1.49  
% 7.76/1.49  --fof                                   false
% 7.76/1.49  --time_out_real                         604.99
% 7.76/1.49  --time_out_virtual                      -1.
% 7.76/1.49  --symbol_type_check                     false
% 7.76/1.49  --clausify_out                          false
% 7.76/1.49  --sig_cnt_out                           false
% 7.76/1.49  --trig_cnt_out                          false
% 7.76/1.49  --trig_cnt_out_tolerance                1.
% 7.76/1.49  --trig_cnt_out_sk_spl                   false
% 7.76/1.49  --abstr_cl_out                          false
% 7.76/1.49  
% 7.76/1.49  ------ Global Options
% 7.76/1.49  
% 7.76/1.49  --schedule                              none
% 7.76/1.49  --add_important_lit                     false
% 7.76/1.49  --prop_solver_per_cl                    1000
% 7.76/1.49  --min_unsat_core                        false
% 7.76/1.49  --soft_assumptions                      false
% 7.76/1.49  --soft_lemma_size                       3
% 7.76/1.49  --prop_impl_unit_size                   0
% 7.76/1.49  --prop_impl_unit                        []
% 7.76/1.49  --share_sel_clauses                     true
% 7.76/1.49  --reset_solvers                         false
% 7.76/1.49  --bc_imp_inh                            [conj_cone]
% 7.76/1.49  --conj_cone_tolerance                   3.
% 7.76/1.49  --extra_neg_conj                        none
% 7.76/1.49  --large_theory_mode                     true
% 7.76/1.49  --prolific_symb_bound                   200
% 7.76/1.49  --lt_threshold                          2000
% 7.76/1.49  --clause_weak_htbl                      true
% 7.76/1.49  --gc_record_bc_elim                     false
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing Options
% 7.76/1.49  
% 7.76/1.49  --preprocessing_flag                    true
% 7.76/1.49  --time_out_prep_mult                    0.1
% 7.76/1.49  --splitting_mode                        input
% 7.76/1.49  --splitting_grd                         true
% 7.76/1.49  --splitting_cvd                         false
% 7.76/1.49  --splitting_cvd_svl                     false
% 7.76/1.49  --splitting_nvd                         32
% 7.76/1.49  --sub_typing                            true
% 7.76/1.49  --prep_gs_sim                           false
% 7.76/1.49  --prep_unflatten                        true
% 7.76/1.49  --prep_res_sim                          true
% 7.76/1.49  --prep_upred                            true
% 7.76/1.49  --prep_sem_filter                       exhaustive
% 7.76/1.49  --prep_sem_filter_out                   false
% 7.76/1.49  --pred_elim                             false
% 7.76/1.49  --res_sim_input                         true
% 7.76/1.49  --eq_ax_congr_red                       true
% 7.76/1.49  --pure_diseq_elim                       true
% 7.76/1.49  --brand_transform                       false
% 7.76/1.49  --non_eq_to_eq                          false
% 7.76/1.49  --prep_def_merge                        true
% 7.76/1.49  --prep_def_merge_prop_impl              false
% 7.76/1.49  --prep_def_merge_mbd                    true
% 7.76/1.49  --prep_def_merge_tr_red                 false
% 7.76/1.49  --prep_def_merge_tr_cl                  false
% 7.76/1.49  --smt_preprocessing                     true
% 7.76/1.49  --smt_ac_axioms                         fast
% 7.76/1.49  --preprocessed_out                      false
% 7.76/1.49  --preprocessed_stats                    false
% 7.76/1.49  
% 7.76/1.49  ------ Abstraction refinement Options
% 7.76/1.49  
% 7.76/1.49  --abstr_ref                             []
% 7.76/1.49  --abstr_ref_prep                        false
% 7.76/1.49  --abstr_ref_until_sat                   false
% 7.76/1.49  --abstr_ref_sig_restrict                funpre
% 7.76/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.49  --abstr_ref_under                       []
% 7.76/1.49  
% 7.76/1.49  ------ SAT Options
% 7.76/1.49  
% 7.76/1.49  --sat_mode                              false
% 7.76/1.49  --sat_fm_restart_options                ""
% 7.76/1.49  --sat_gr_def                            false
% 7.76/1.49  --sat_epr_types                         true
% 7.76/1.49  --sat_non_cyclic_types                  false
% 7.76/1.49  --sat_finite_models                     false
% 7.76/1.49  --sat_fm_lemmas                         false
% 7.76/1.49  --sat_fm_prep                           false
% 7.76/1.49  --sat_fm_uc_incr                        true
% 7.76/1.49  --sat_out_model                         small
% 7.76/1.49  --sat_out_clauses                       false
% 7.76/1.49  
% 7.76/1.49  ------ QBF Options
% 7.76/1.49  
% 7.76/1.49  --qbf_mode                              false
% 7.76/1.49  --qbf_elim_univ                         false
% 7.76/1.49  --qbf_dom_inst                          none
% 7.76/1.49  --qbf_dom_pre_inst                      false
% 7.76/1.49  --qbf_sk_in                             false
% 7.76/1.49  --qbf_pred_elim                         true
% 7.76/1.49  --qbf_split                             512
% 7.76/1.49  
% 7.76/1.49  ------ BMC1 Options
% 7.76/1.49  
% 7.76/1.49  --bmc1_incremental                      false
% 7.76/1.49  --bmc1_axioms                           reachable_all
% 7.76/1.49  --bmc1_min_bound                        0
% 7.76/1.49  --bmc1_max_bound                        -1
% 7.76/1.49  --bmc1_max_bound_default                -1
% 7.76/1.49  --bmc1_symbol_reachability              true
% 7.76/1.49  --bmc1_property_lemmas                  false
% 7.76/1.49  --bmc1_k_induction                      false
% 7.76/1.49  --bmc1_non_equiv_states                 false
% 7.76/1.49  --bmc1_deadlock                         false
% 7.76/1.49  --bmc1_ucm                              false
% 7.76/1.49  --bmc1_add_unsat_core                   none
% 7.76/1.49  --bmc1_unsat_core_children              false
% 7.76/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.49  --bmc1_out_stat                         full
% 7.76/1.49  --bmc1_ground_init                      false
% 7.76/1.49  --bmc1_pre_inst_next_state              false
% 7.76/1.49  --bmc1_pre_inst_state                   false
% 7.76/1.49  --bmc1_pre_inst_reach_state             false
% 7.76/1.49  --bmc1_out_unsat_core                   false
% 7.76/1.49  --bmc1_aig_witness_out                  false
% 7.76/1.49  --bmc1_verbose                          false
% 7.76/1.49  --bmc1_dump_clauses_tptp                false
% 7.76/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.49  --bmc1_dump_file                        -
% 7.76/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.49  --bmc1_ucm_extend_mode                  1
% 7.76/1.49  --bmc1_ucm_init_mode                    2
% 7.76/1.49  --bmc1_ucm_cone_mode                    none
% 7.76/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.49  --bmc1_ucm_relax_model                  4
% 7.76/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.49  --bmc1_ucm_layered_model                none
% 7.76/1.49  --bmc1_ucm_max_lemma_size               10
% 7.76/1.49  
% 7.76/1.49  ------ AIG Options
% 7.76/1.49  
% 7.76/1.49  --aig_mode                              false
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation Options
% 7.76/1.49  
% 7.76/1.49  --instantiation_flag                    true
% 7.76/1.49  --inst_sos_flag                         false
% 7.76/1.49  --inst_sos_phase                        true
% 7.76/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel_side                     num_symb
% 7.76/1.49  --inst_solver_per_active                1400
% 7.76/1.49  --inst_solver_calls_frac                1.
% 7.76/1.49  --inst_passive_queue_type               priority_queues
% 7.76/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.49  --inst_passive_queues_freq              [25;2]
% 7.76/1.49  --inst_dismatching                      true
% 7.76/1.49  --inst_eager_unprocessed_to_passive     true
% 7.76/1.49  --inst_prop_sim_given                   true
% 7.76/1.49  --inst_prop_sim_new                     false
% 7.76/1.49  --inst_subs_new                         false
% 7.76/1.49  --inst_eq_res_simp                      false
% 7.76/1.49  --inst_subs_given                       false
% 7.76/1.49  --inst_orphan_elimination               true
% 7.76/1.49  --inst_learning_loop_flag               true
% 7.76/1.49  --inst_learning_start                   3000
% 7.76/1.49  --inst_learning_factor                  2
% 7.76/1.49  --inst_start_prop_sim_after_learn       3
% 7.76/1.49  --inst_sel_renew                        solver
% 7.76/1.49  --inst_lit_activity_flag                true
% 7.76/1.49  --inst_restr_to_given                   false
% 7.76/1.49  --inst_activity_threshold               500
% 7.76/1.49  --inst_out_proof                        true
% 7.76/1.49  
% 7.76/1.49  ------ Resolution Options
% 7.76/1.49  
% 7.76/1.49  --resolution_flag                       true
% 7.76/1.49  --res_lit_sel                           adaptive
% 7.76/1.49  --res_lit_sel_side                      none
% 7.76/1.49  --res_ordering                          kbo
% 7.76/1.49  --res_to_prop_solver                    active
% 7.76/1.49  --res_prop_simpl_new                    false
% 7.76/1.49  --res_prop_simpl_given                  true
% 7.76/1.49  --res_passive_queue_type                priority_queues
% 7.76/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.49  --res_passive_queues_freq               [15;5]
% 7.76/1.49  --res_forward_subs                      full
% 7.76/1.49  --res_backward_subs                     full
% 7.76/1.49  --res_forward_subs_resolution           true
% 7.76/1.49  --res_backward_subs_resolution          true
% 7.76/1.49  --res_orphan_elimination                true
% 7.76/1.49  --res_time_limit                        2.
% 7.76/1.49  --res_out_proof                         true
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Options
% 7.76/1.49  
% 7.76/1.49  --superposition_flag                    true
% 7.76/1.49  --sup_passive_queue_type                priority_queues
% 7.76/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.49  --sup_passive_queues_freq               [1;4]
% 7.76/1.49  --demod_completeness_check              fast
% 7.76/1.49  --demod_use_ground                      true
% 7.76/1.49  --sup_to_prop_solver                    passive
% 7.76/1.49  --sup_prop_simpl_new                    true
% 7.76/1.49  --sup_prop_simpl_given                  true
% 7.76/1.49  --sup_fun_splitting                     false
% 7.76/1.49  --sup_smt_interval                      50000
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Simplification Setup
% 7.76/1.49  
% 7.76/1.49  --sup_indices_passive                   []
% 7.76/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_full_bw                           [BwDemod]
% 7.76/1.49  --sup_immed_triv                        [TrivRules]
% 7.76/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_immed_bw_main                     []
% 7.76/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.49  
% 7.76/1.49  ------ Combination Options
% 7.76/1.49  
% 7.76/1.49  --comb_res_mult                         3
% 7.76/1.49  --comb_sup_mult                         2
% 7.76/1.49  --comb_inst_mult                        10
% 7.76/1.49  
% 7.76/1.49  ------ Debug Options
% 7.76/1.49  
% 7.76/1.49  --dbg_backtrace                         false
% 7.76/1.49  --dbg_dump_prop_clauses                 false
% 7.76/1.49  --dbg_dump_prop_clauses_file            -
% 7.76/1.49  --dbg_out_stat                          false
% 7.76/1.49  ------ Parsing...
% 7.76/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.49  ------ Proving...
% 7.76/1.49  ------ Problem Properties 
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  clauses                                 10
% 7.76/1.49  conjectures                             2
% 7.76/1.49  EPR                                     0
% 7.76/1.49  Horn                                    10
% 7.76/1.49  unary                                   8
% 7.76/1.49  binary                                  2
% 7.76/1.49  lits                                    12
% 7.76/1.49  lits eq                                 7
% 7.76/1.49  fd_pure                                 0
% 7.76/1.49  fd_pseudo                               0
% 7.76/1.49  fd_cond                                 0
% 7.76/1.49  fd_pseudo_cond                          0
% 7.76/1.49  AC symbols                              0
% 7.76/1.49  
% 7.76/1.49  ------ Input Options Time Limit: Unbounded
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  ------ 
% 7.76/1.49  Current options:
% 7.76/1.49  ------ 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options
% 7.76/1.49  
% 7.76/1.49  --out_options                           all
% 7.76/1.49  --tptp_safe_out                         true
% 7.76/1.49  --problem_path                          ""
% 7.76/1.49  --include_path                          ""
% 7.76/1.49  --clausifier                            res/vclausify_rel
% 7.76/1.49  --clausifier_options                    --mode clausify
% 7.76/1.49  --stdin                                 false
% 7.76/1.49  --stats_out                             sel
% 7.76/1.49  
% 7.76/1.49  ------ General Options
% 7.76/1.49  
% 7.76/1.49  --fof                                   false
% 7.76/1.49  --time_out_real                         604.99
% 7.76/1.49  --time_out_virtual                      -1.
% 7.76/1.49  --symbol_type_check                     false
% 7.76/1.49  --clausify_out                          false
% 7.76/1.49  --sig_cnt_out                           false
% 7.76/1.49  --trig_cnt_out                          false
% 7.76/1.49  --trig_cnt_out_tolerance                1.
% 7.76/1.49  --trig_cnt_out_sk_spl                   false
% 7.76/1.49  --abstr_cl_out                          false
% 7.76/1.49  
% 7.76/1.49  ------ Global Options
% 7.76/1.49  
% 7.76/1.49  --schedule                              none
% 7.76/1.49  --add_important_lit                     false
% 7.76/1.49  --prop_solver_per_cl                    1000
% 7.76/1.49  --min_unsat_core                        false
% 7.76/1.49  --soft_assumptions                      false
% 7.76/1.49  --soft_lemma_size                       3
% 7.76/1.49  --prop_impl_unit_size                   0
% 7.76/1.49  --prop_impl_unit                        []
% 7.76/1.49  --share_sel_clauses                     true
% 7.76/1.49  --reset_solvers                         false
% 7.76/1.49  --bc_imp_inh                            [conj_cone]
% 7.76/1.49  --conj_cone_tolerance                   3.
% 7.76/1.49  --extra_neg_conj                        none
% 7.76/1.49  --large_theory_mode                     true
% 7.76/1.49  --prolific_symb_bound                   200
% 7.76/1.49  --lt_threshold                          2000
% 7.76/1.49  --clause_weak_htbl                      true
% 7.76/1.49  --gc_record_bc_elim                     false
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing Options
% 7.76/1.49  
% 7.76/1.49  --preprocessing_flag                    true
% 7.76/1.49  --time_out_prep_mult                    0.1
% 7.76/1.49  --splitting_mode                        input
% 7.76/1.49  --splitting_grd                         true
% 7.76/1.49  --splitting_cvd                         false
% 7.76/1.49  --splitting_cvd_svl                     false
% 7.76/1.49  --splitting_nvd                         32
% 7.76/1.49  --sub_typing                            true
% 7.76/1.49  --prep_gs_sim                           false
% 7.76/1.49  --prep_unflatten                        true
% 7.76/1.49  --prep_res_sim                          true
% 7.76/1.49  --prep_upred                            true
% 7.76/1.49  --prep_sem_filter                       exhaustive
% 7.76/1.49  --prep_sem_filter_out                   false
% 7.76/1.49  --pred_elim                             false
% 7.76/1.49  --res_sim_input                         true
% 7.76/1.49  --eq_ax_congr_red                       true
% 7.76/1.49  --pure_diseq_elim                       true
% 7.76/1.49  --brand_transform                       false
% 7.76/1.49  --non_eq_to_eq                          false
% 7.76/1.49  --prep_def_merge                        true
% 7.76/1.49  --prep_def_merge_prop_impl              false
% 7.76/1.49  --prep_def_merge_mbd                    true
% 7.76/1.49  --prep_def_merge_tr_red                 false
% 7.76/1.49  --prep_def_merge_tr_cl                  false
% 7.76/1.49  --smt_preprocessing                     true
% 7.76/1.49  --smt_ac_axioms                         fast
% 7.76/1.49  --preprocessed_out                      false
% 7.76/1.49  --preprocessed_stats                    false
% 7.76/1.49  
% 7.76/1.49  ------ Abstraction refinement Options
% 7.76/1.49  
% 7.76/1.49  --abstr_ref                             []
% 7.76/1.49  --abstr_ref_prep                        false
% 7.76/1.49  --abstr_ref_until_sat                   false
% 7.76/1.49  --abstr_ref_sig_restrict                funpre
% 7.76/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.49  --abstr_ref_under                       []
% 7.76/1.49  
% 7.76/1.49  ------ SAT Options
% 7.76/1.49  
% 7.76/1.49  --sat_mode                              false
% 7.76/1.49  --sat_fm_restart_options                ""
% 7.76/1.49  --sat_gr_def                            false
% 7.76/1.49  --sat_epr_types                         true
% 7.76/1.49  --sat_non_cyclic_types                  false
% 7.76/1.49  --sat_finite_models                     false
% 7.76/1.49  --sat_fm_lemmas                         false
% 7.76/1.49  --sat_fm_prep                           false
% 7.76/1.49  --sat_fm_uc_incr                        true
% 7.76/1.49  --sat_out_model                         small
% 7.76/1.49  --sat_out_clauses                       false
% 7.76/1.49  
% 7.76/1.49  ------ QBF Options
% 7.76/1.49  
% 7.76/1.49  --qbf_mode                              false
% 7.76/1.49  --qbf_elim_univ                         false
% 7.76/1.49  --qbf_dom_inst                          none
% 7.76/1.49  --qbf_dom_pre_inst                      false
% 7.76/1.49  --qbf_sk_in                             false
% 7.76/1.49  --qbf_pred_elim                         true
% 7.76/1.49  --qbf_split                             512
% 7.76/1.49  
% 7.76/1.49  ------ BMC1 Options
% 7.76/1.49  
% 7.76/1.49  --bmc1_incremental                      false
% 7.76/1.49  --bmc1_axioms                           reachable_all
% 7.76/1.49  --bmc1_min_bound                        0
% 7.76/1.49  --bmc1_max_bound                        -1
% 7.76/1.49  --bmc1_max_bound_default                -1
% 7.76/1.49  --bmc1_symbol_reachability              true
% 7.76/1.49  --bmc1_property_lemmas                  false
% 7.76/1.49  --bmc1_k_induction                      false
% 7.76/1.49  --bmc1_non_equiv_states                 false
% 7.76/1.49  --bmc1_deadlock                         false
% 7.76/1.49  --bmc1_ucm                              false
% 7.76/1.49  --bmc1_add_unsat_core                   none
% 7.76/1.49  --bmc1_unsat_core_children              false
% 7.76/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.49  --bmc1_out_stat                         full
% 7.76/1.49  --bmc1_ground_init                      false
% 7.76/1.49  --bmc1_pre_inst_next_state              false
% 7.76/1.49  --bmc1_pre_inst_state                   false
% 7.76/1.49  --bmc1_pre_inst_reach_state             false
% 7.76/1.49  --bmc1_out_unsat_core                   false
% 7.76/1.49  --bmc1_aig_witness_out                  false
% 7.76/1.49  --bmc1_verbose                          false
% 7.76/1.49  --bmc1_dump_clauses_tptp                false
% 7.76/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.49  --bmc1_dump_file                        -
% 7.76/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.49  --bmc1_ucm_extend_mode                  1
% 7.76/1.49  --bmc1_ucm_init_mode                    2
% 7.76/1.49  --bmc1_ucm_cone_mode                    none
% 7.76/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.49  --bmc1_ucm_relax_model                  4
% 7.76/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.49  --bmc1_ucm_layered_model                none
% 7.76/1.49  --bmc1_ucm_max_lemma_size               10
% 7.76/1.49  
% 7.76/1.49  ------ AIG Options
% 7.76/1.49  
% 7.76/1.49  --aig_mode                              false
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation Options
% 7.76/1.49  
% 7.76/1.49  --instantiation_flag                    true
% 7.76/1.49  --inst_sos_flag                         false
% 7.76/1.49  --inst_sos_phase                        true
% 7.76/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel_side                     num_symb
% 7.76/1.49  --inst_solver_per_active                1400
% 7.76/1.49  --inst_solver_calls_frac                1.
% 7.76/1.49  --inst_passive_queue_type               priority_queues
% 7.76/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.49  --inst_passive_queues_freq              [25;2]
% 7.76/1.49  --inst_dismatching                      true
% 7.76/1.49  --inst_eager_unprocessed_to_passive     true
% 7.76/1.49  --inst_prop_sim_given                   true
% 7.76/1.49  --inst_prop_sim_new                     false
% 7.76/1.49  --inst_subs_new                         false
% 7.76/1.49  --inst_eq_res_simp                      false
% 7.76/1.49  --inst_subs_given                       false
% 7.76/1.49  --inst_orphan_elimination               true
% 7.76/1.49  --inst_learning_loop_flag               true
% 7.76/1.49  --inst_learning_start                   3000
% 7.76/1.49  --inst_learning_factor                  2
% 7.76/1.49  --inst_start_prop_sim_after_learn       3
% 7.76/1.49  --inst_sel_renew                        solver
% 7.76/1.49  --inst_lit_activity_flag                true
% 7.76/1.49  --inst_restr_to_given                   false
% 7.76/1.49  --inst_activity_threshold               500
% 7.76/1.49  --inst_out_proof                        true
% 7.76/1.49  
% 7.76/1.49  ------ Resolution Options
% 7.76/1.49  
% 7.76/1.49  --resolution_flag                       true
% 7.76/1.49  --res_lit_sel                           adaptive
% 7.76/1.49  --res_lit_sel_side                      none
% 7.76/1.49  --res_ordering                          kbo
% 7.76/1.49  --res_to_prop_solver                    active
% 7.76/1.49  --res_prop_simpl_new                    false
% 7.76/1.49  --res_prop_simpl_given                  true
% 7.76/1.49  --res_passive_queue_type                priority_queues
% 7.76/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.49  --res_passive_queues_freq               [15;5]
% 7.76/1.49  --res_forward_subs                      full
% 7.76/1.49  --res_backward_subs                     full
% 7.76/1.49  --res_forward_subs_resolution           true
% 7.76/1.49  --res_backward_subs_resolution          true
% 7.76/1.49  --res_orphan_elimination                true
% 7.76/1.49  --res_time_limit                        2.
% 7.76/1.49  --res_out_proof                         true
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Options
% 7.76/1.49  
% 7.76/1.49  --superposition_flag                    true
% 7.76/1.49  --sup_passive_queue_type                priority_queues
% 7.76/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.49  --sup_passive_queues_freq               [1;4]
% 7.76/1.49  --demod_completeness_check              fast
% 7.76/1.49  --demod_use_ground                      true
% 7.76/1.49  --sup_to_prop_solver                    passive
% 7.76/1.49  --sup_prop_simpl_new                    true
% 7.76/1.49  --sup_prop_simpl_given                  true
% 7.76/1.49  --sup_fun_splitting                     false
% 7.76/1.49  --sup_smt_interval                      50000
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Simplification Setup
% 7.76/1.49  
% 7.76/1.49  --sup_indices_passive                   []
% 7.76/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_full_bw                           [BwDemod]
% 7.76/1.49  --sup_immed_triv                        [TrivRules]
% 7.76/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_immed_bw_main                     []
% 7.76/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.49  
% 7.76/1.49  ------ Combination Options
% 7.76/1.49  
% 7.76/1.49  --comb_res_mult                         3
% 7.76/1.49  --comb_sup_mult                         2
% 7.76/1.49  --comb_inst_mult                        10
% 7.76/1.49  
% 7.76/1.49  ------ Debug Options
% 7.76/1.49  
% 7.76/1.49  --dbg_backtrace                         false
% 7.76/1.49  --dbg_dump_prop_clauses                 false
% 7.76/1.49  --dbg_dump_prop_clauses_file            -
% 7.76/1.49  --dbg_out_stat                          false
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  ------ Proving...
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  % SZS status Theorem for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  fof(f9,conjecture,(
% 7.76/1.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f10,negated_conjecture,(
% 7.76/1.49    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 7.76/1.49    inference(negated_conjecture,[],[f9])).
% 7.76/1.49  
% 7.76/1.49  fof(f11,plain,(
% 7.76/1.49    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 7.76/1.49    inference(ennf_transformation,[],[f10])).
% 7.76/1.49  
% 7.76/1.49  fof(f13,plain,(
% 7.76/1.49    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f14,plain,(
% 7.76/1.49    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.76/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 7.76/1.49  
% 7.76/1.49  fof(f24,plain,(
% 7.76/1.49    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.76/1.49    inference(cnf_transformation,[],[f14])).
% 7.76/1.49  
% 7.76/1.49  fof(f1,axiom,(
% 7.76/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f12,plain,(
% 7.76/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.76/1.49    inference(nnf_transformation,[],[f1])).
% 7.76/1.49  
% 7.76/1.49  fof(f15,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f12])).
% 7.76/1.49  
% 7.76/1.49  fof(f5,axiom,(
% 7.76/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f20,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f5])).
% 7.76/1.49  
% 7.76/1.49  fof(f27,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.76/1.49    inference(definition_unfolding,[],[f15,f20])).
% 7.76/1.49  
% 7.76/1.49  fof(f6,axiom,(
% 7.76/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f21,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f6])).
% 7.76/1.49  
% 7.76/1.49  fof(f29,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.76/1.49    inference(definition_unfolding,[],[f21,f20,f20])).
% 7.76/1.49  
% 7.76/1.49  fof(f7,axiom,(
% 7.76/1.49    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f22,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f7])).
% 7.76/1.49  
% 7.76/1.49  fof(f30,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 7.76/1.49    inference(definition_unfolding,[],[f22,f20])).
% 7.76/1.49  
% 7.76/1.49  fof(f2,axiom,(
% 7.76/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f17,plain,(
% 7.76/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.76/1.49    inference(cnf_transformation,[],[f2])).
% 7.76/1.49  
% 7.76/1.49  fof(f28,plain,(
% 7.76/1.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.76/1.49    inference(definition_unfolding,[],[f17,f20])).
% 7.76/1.49  
% 7.76/1.49  fof(f4,axiom,(
% 7.76/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f19,plain,(
% 7.76/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.76/1.49    inference(cnf_transformation,[],[f4])).
% 7.76/1.49  
% 7.76/1.49  fof(f3,axiom,(
% 7.76/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f18,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f3])).
% 7.76/1.49  
% 7.76/1.49  fof(f8,axiom,(
% 7.76/1.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f23,plain,(
% 7.76/1.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f8])).
% 7.76/1.49  
% 7.76/1.49  fof(f25,plain,(
% 7.76/1.49    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.76/1.49    inference(cnf_transformation,[],[f14])).
% 7.76/1.49  
% 7.76/1.49  cnf(c_9,negated_conjecture,
% 7.76/1.49      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f24]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_224,plain,
% 7.76/1.49      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1,plain,
% 7.76/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_227,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.76/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_769,plain,
% 7.76/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_224,c_227]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5,plain,
% 7.76/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.76/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_6,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_332,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_337,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_332,c_5]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_338,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_337,c_5,c_6]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_7279,plain,
% 7.76/1.49      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))))) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_769,c_338]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f19]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_235,plain,
% 7.76/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_2,c_4]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_428,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_235,c_5]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_440,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_428,c_4]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_7847,plain,
% 7.76/1.49      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_7279,c_5,c_440]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_7848,plain,
% 7.76/1.49      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_7847,c_4,c_235]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1209,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_440,c_6]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1217,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_440,c_6]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1235,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_1209,c_1217]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1237,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_1235,c_5]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1238,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_1237,c_440]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_27532,plain,
% 7.76/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_7848,c_1238]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_431,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_235,c_6]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_433,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_431,c_4]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_3,plain,
% 7.76/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f18]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_333,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_6,c_3]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_778,plain,
% 7.76/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_333,c_4,c_235]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1007,plain,
% 7.76/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_433,c_778]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_27974,plain,
% 7.76/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = sK1 ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_27532,c_1007]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_7,plain,
% 7.76/1.49      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2996,plain,
% 7.76/1.49      ( r1_xboole_0(k4_xboole_0(sK1,X0),X0) ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8714,plain,
% 7.76/1.49      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)) ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_2996]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_78,plain,
% 7.76/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.76/1.49      theory(equality) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_288,plain,
% 7.76/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.49      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 7.76/1.49      | k4_xboole_0(sK0,sK2) != X1
% 7.76/1.49      | sK1 != X0 ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_78]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1899,plain,
% 7.76/1.49      ( ~ r1_xboole_0(k4_xboole_0(sK1,X0),X1)
% 7.76/1.49      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 7.76/1.49      | k4_xboole_0(sK0,sK2) != X1
% 7.76/1.49      | sK1 != k4_xboole_0(sK1,X0) ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_288]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_3500,plain,
% 7.76/1.49      ( ~ r1_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK0,sK2))
% 7.76/1.49      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 7.76/1.49      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
% 7.76/1.49      | sK1 != k4_xboole_0(sK1,X0) ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_1899]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8713,plain,
% 7.76/1.49      ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2))
% 7.76/1.49      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 7.76/1.49      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
% 7.76/1.49      | sK1 != k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_3500]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_77,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_301,plain,
% 7.76/1.49      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_77]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_396,plain,
% 7.76/1.49      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_301]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1894,plain,
% 7.76/1.49      ( k4_xboole_0(sK1,X0) != sK1
% 7.76/1.49      | sK1 = k4_xboole_0(sK1,X0)
% 7.76/1.49      | sK1 != sK1 ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_396]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4643,plain,
% 7.76/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != sK1
% 7.76/1.49      | sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 7.76/1.49      | sK1 != sK1 ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_1894]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_76,plain,( X0 = X0 ),theory(equality) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_416,plain,
% 7.76/1.49      ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_76]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_296,plain,
% 7.76/1.49      ( sK1 = sK1 ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_76]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8,negated_conjecture,
% 7.76/1.49      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f25]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(contradiction,plain,
% 7.76/1.49      ( $false ),
% 7.76/1.49      inference(minisat,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_27974,c_8714,c_8713,c_4643,c_416,c_296,c_8]) ).
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  ------                               Statistics
% 7.76/1.49  
% 7.76/1.49  ------ Selected
% 7.76/1.49  
% 7.76/1.49  total_time:                             0.787
% 7.76/1.49  
%------------------------------------------------------------------------------
