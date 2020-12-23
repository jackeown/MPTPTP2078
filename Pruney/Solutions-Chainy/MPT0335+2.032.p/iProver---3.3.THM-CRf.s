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
% DateTime   : Thu Dec  3 11:38:30 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 304 expanded)
%              Number of clauses        :   43 (  90 expanded)
%              Number of leaves         :   13 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 563 expanded)
%              Number of equality atoms :  104 ( 380 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f22])).

fof(f38,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f49,plain,(
    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f43,f43])).

fof(f37,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f39,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f40,f43])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_289,plain,
    ( k3_xboole_0(X0_38,X1_38) = k3_xboole_0(X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_287,plain,
    ( r1_tarski(k3_xboole_0(X0_38,X1_38),X0_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_406,plain,
    ( r1_tarski(k3_xboole_0(X0_38,X1_38),X0_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_599,plain,
    ( r1_tarski(k3_xboole_0(X0_38,X1_38),X1_38) = iProver_top ),
    inference(superposition,[status(thm)],[c_289,c_406])).

cnf(c_11,negated_conjecture,
    ( k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_281,negated_conjecture,
    ( k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_290,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_xboole_0(sK2,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_281,c_2,c_0])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_283,plain,
    ( ~ r1_tarski(X0_38,k3_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39))
    | k3_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39) = X0_38
    | k1_xboole_0 = X0_38 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_410,plain,
    ( k3_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39) = X0_38
    | k1_xboole_0 = X0_38
    | r1_tarski(X0_38,k3_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_4707,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = X0_38
    | k1_xboole_0 = X0_38
    | r1_tarski(X0_38,k3_xboole_0(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_290,c_410])).

cnf(c_4711,plain,
    ( k3_xboole_0(sK2,sK1) = X0_38
    | k1_xboole_0 = X0_38
    | r1_tarski(X0_38,k3_xboole_0(sK2,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4707,c_290])).

cnf(c_5945,plain,
    ( k3_xboole_0(X0_38,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK2,sK1)
    | k3_xboole_0(X0_38,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_599,c_4711])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_280,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_411,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_286,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | k3_xboole_0(X0_38,X1_38) = X0_38 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_407,plain,
    ( k3_xboole_0(X0_38,X1_38) = X0_38
    | r1_tarski(X0_38,X1_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_1588,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_411,c_407])).

cnf(c_288,plain,
    ( k3_xboole_0(k3_xboole_0(X0_38,X1_38),X2_38) = k3_xboole_0(X0_38,k3_xboole_0(X1_38,X2_38)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2559,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,X0_38)) = k3_xboole_0(sK0,X0_38) ),
    inference(superposition,[status(thm)],[c_1588,c_288])).

cnf(c_3398,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0_38,sK1)) = k3_xboole_0(sK0,X0_38) ),
    inference(superposition,[status(thm)],[c_289,c_2559])).

cnf(c_6594,plain,
    ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK0,sK2)
    | k3_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5945,c_3398])).

cnf(c_6603,plain,
    ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK0,sK2)
    | k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6594,c_3398])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_112,plain,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | sK3 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_113,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) ),
    inference(unflattening,[status(thm)],[c_112])).

cnf(c_121,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X0
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_113])).

cnf(c_122,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_121])).

cnf(c_279,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_122])).

cnf(c_291,plain,
    ( k3_xboole_0(sK0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_279,c_2,c_0])).

cnf(c_427,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_291,c_290])).

cnf(c_3694,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3398,c_427])).

cnf(c_9,negated_conjecture,
    ( k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_282,negated_conjecture,
    ( k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_424,plain,
    ( k3_xboole_0(sK2,sK1) != k3_xboole_0(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_282,c_290])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6603,c_3694,c_424])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:40:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.30/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/0.97  
% 3.30/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/0.97  
% 3.30/0.97  ------  iProver source info
% 3.30/0.97  
% 3.30/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.30/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/0.97  git: non_committed_changes: false
% 3.30/0.97  git: last_make_outside_of_git: false
% 3.30/0.97  
% 3.30/0.97  ------ 
% 3.30/0.97  
% 3.30/0.97  ------ Input Options
% 3.30/0.97  
% 3.30/0.97  --out_options                           all
% 3.30/0.97  --tptp_safe_out                         true
% 3.30/0.97  --problem_path                          ""
% 3.30/0.97  --include_path                          ""
% 3.30/0.97  --clausifier                            res/vclausify_rel
% 3.30/0.97  --clausifier_options                    --mode clausify
% 3.30/0.97  --stdin                                 false
% 3.30/0.97  --stats_out                             all
% 3.30/0.97  
% 3.30/0.97  ------ General Options
% 3.30/0.97  
% 3.30/0.97  --fof                                   false
% 3.30/0.97  --time_out_real                         305.
% 3.30/0.97  --time_out_virtual                      -1.
% 3.30/0.97  --symbol_type_check                     false
% 3.30/0.97  --clausify_out                          false
% 3.30/0.97  --sig_cnt_out                           false
% 3.30/0.97  --trig_cnt_out                          false
% 3.30/0.97  --trig_cnt_out_tolerance                1.
% 3.30/0.97  --trig_cnt_out_sk_spl                   false
% 3.30/0.97  --abstr_cl_out                          false
% 3.30/0.97  
% 3.30/0.97  ------ Global Options
% 3.30/0.97  
% 3.30/0.97  --schedule                              default
% 3.30/0.97  --add_important_lit                     false
% 3.30/0.97  --prop_solver_per_cl                    1000
% 3.30/0.97  --min_unsat_core                        false
% 3.30/0.97  --soft_assumptions                      false
% 3.30/0.97  --soft_lemma_size                       3
% 3.30/0.97  --prop_impl_unit_size                   0
% 3.30/0.97  --prop_impl_unit                        []
% 3.30/0.97  --share_sel_clauses                     true
% 3.30/0.97  --reset_solvers                         false
% 3.30/0.97  --bc_imp_inh                            [conj_cone]
% 3.30/0.97  --conj_cone_tolerance                   3.
% 3.30/0.97  --extra_neg_conj                        none
% 3.30/0.97  --large_theory_mode                     true
% 3.30/0.97  --prolific_symb_bound                   200
% 3.30/0.97  --lt_threshold                          2000
% 3.30/0.97  --clause_weak_htbl                      true
% 3.30/0.97  --gc_record_bc_elim                     false
% 3.30/0.97  
% 3.30/0.97  ------ Preprocessing Options
% 3.30/0.97  
% 3.30/0.97  --preprocessing_flag                    true
% 3.30/0.97  --time_out_prep_mult                    0.1
% 3.30/0.97  --splitting_mode                        input
% 3.30/0.97  --splitting_grd                         true
% 3.30/0.97  --splitting_cvd                         false
% 3.30/0.97  --splitting_cvd_svl                     false
% 3.30/0.97  --splitting_nvd                         32
% 3.30/0.97  --sub_typing                            true
% 3.30/0.97  --prep_gs_sim                           true
% 3.30/0.97  --prep_unflatten                        true
% 3.30/0.97  --prep_res_sim                          true
% 3.30/0.97  --prep_upred                            true
% 3.30/0.97  --prep_sem_filter                       exhaustive
% 3.30/0.97  --prep_sem_filter_out                   false
% 3.30/0.97  --pred_elim                             true
% 3.30/0.97  --res_sim_input                         true
% 3.30/0.97  --eq_ax_congr_red                       true
% 3.30/0.97  --pure_diseq_elim                       true
% 3.30/0.97  --brand_transform                       false
% 3.30/0.97  --non_eq_to_eq                          false
% 3.30/0.97  --prep_def_merge                        true
% 3.30/0.97  --prep_def_merge_prop_impl              false
% 3.30/0.97  --prep_def_merge_mbd                    true
% 3.30/0.97  --prep_def_merge_tr_red                 false
% 3.30/0.97  --prep_def_merge_tr_cl                  false
% 3.30/0.97  --smt_preprocessing                     true
% 3.30/0.97  --smt_ac_axioms                         fast
% 3.30/0.97  --preprocessed_out                      false
% 3.30/0.97  --preprocessed_stats                    false
% 3.30/0.97  
% 3.30/0.97  ------ Abstraction refinement Options
% 3.30/0.97  
% 3.30/0.97  --abstr_ref                             []
% 3.30/0.97  --abstr_ref_prep                        false
% 3.30/0.97  --abstr_ref_until_sat                   false
% 3.30/0.97  --abstr_ref_sig_restrict                funpre
% 3.30/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.97  --abstr_ref_under                       []
% 3.30/0.97  
% 3.30/0.97  ------ SAT Options
% 3.30/0.97  
% 3.30/0.97  --sat_mode                              false
% 3.30/0.97  --sat_fm_restart_options                ""
% 3.30/0.97  --sat_gr_def                            false
% 3.30/0.97  --sat_epr_types                         true
% 3.30/0.97  --sat_non_cyclic_types                  false
% 3.30/0.97  --sat_finite_models                     false
% 3.30/0.97  --sat_fm_lemmas                         false
% 3.30/0.97  --sat_fm_prep                           false
% 3.30/0.97  --sat_fm_uc_incr                        true
% 3.30/0.97  --sat_out_model                         small
% 3.30/0.97  --sat_out_clauses                       false
% 3.30/0.97  
% 3.30/0.97  ------ QBF Options
% 3.30/0.97  
% 3.30/0.97  --qbf_mode                              false
% 3.30/0.97  --qbf_elim_univ                         false
% 3.30/0.97  --qbf_dom_inst                          none
% 3.30/0.97  --qbf_dom_pre_inst                      false
% 3.30/0.97  --qbf_sk_in                             false
% 3.30/0.97  --qbf_pred_elim                         true
% 3.30/0.97  --qbf_split                             512
% 3.30/0.97  
% 3.30/0.97  ------ BMC1 Options
% 3.30/0.97  
% 3.30/0.97  --bmc1_incremental                      false
% 3.30/0.97  --bmc1_axioms                           reachable_all
% 3.30/0.97  --bmc1_min_bound                        0
% 3.30/0.97  --bmc1_max_bound                        -1
% 3.30/0.97  --bmc1_max_bound_default                -1
% 3.30/0.97  --bmc1_symbol_reachability              true
% 3.30/0.97  --bmc1_property_lemmas                  false
% 3.30/0.97  --bmc1_k_induction                      false
% 3.30/0.97  --bmc1_non_equiv_states                 false
% 3.30/0.97  --bmc1_deadlock                         false
% 3.30/0.97  --bmc1_ucm                              false
% 3.30/0.97  --bmc1_add_unsat_core                   none
% 3.30/0.97  --bmc1_unsat_core_children              false
% 3.30/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.97  --bmc1_out_stat                         full
% 3.30/0.97  --bmc1_ground_init                      false
% 3.30/0.97  --bmc1_pre_inst_next_state              false
% 3.30/0.97  --bmc1_pre_inst_state                   false
% 3.30/0.97  --bmc1_pre_inst_reach_state             false
% 3.30/0.97  --bmc1_out_unsat_core                   false
% 3.30/0.97  --bmc1_aig_witness_out                  false
% 3.30/0.97  --bmc1_verbose                          false
% 3.30/0.97  --bmc1_dump_clauses_tptp                false
% 3.30/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.97  --bmc1_dump_file                        -
% 3.30/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.97  --bmc1_ucm_extend_mode                  1
% 3.30/0.97  --bmc1_ucm_init_mode                    2
% 3.30/0.97  --bmc1_ucm_cone_mode                    none
% 3.30/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.97  --bmc1_ucm_relax_model                  4
% 3.30/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.97  --bmc1_ucm_layered_model                none
% 3.30/0.97  --bmc1_ucm_max_lemma_size               10
% 3.30/0.97  
% 3.30/0.97  ------ AIG Options
% 3.30/0.97  
% 3.30/0.97  --aig_mode                              false
% 3.30/0.97  
% 3.30/0.97  ------ Instantiation Options
% 3.30/0.97  
% 3.30/0.97  --instantiation_flag                    true
% 3.30/0.97  --inst_sos_flag                         false
% 3.30/0.97  --inst_sos_phase                        true
% 3.30/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.97  --inst_lit_sel_side                     num_symb
% 3.30/0.97  --inst_solver_per_active                1400
% 3.30/0.97  --inst_solver_calls_frac                1.
% 3.30/0.97  --inst_passive_queue_type               priority_queues
% 3.30/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.97  --inst_passive_queues_freq              [25;2]
% 3.30/0.97  --inst_dismatching                      true
% 3.30/0.97  --inst_eager_unprocessed_to_passive     true
% 3.30/0.97  --inst_prop_sim_given                   true
% 3.30/0.97  --inst_prop_sim_new                     false
% 3.30/0.97  --inst_subs_new                         false
% 3.30/0.97  --inst_eq_res_simp                      false
% 3.30/0.97  --inst_subs_given                       false
% 3.30/0.97  --inst_orphan_elimination               true
% 3.30/0.97  --inst_learning_loop_flag               true
% 3.30/0.97  --inst_learning_start                   3000
% 3.30/0.97  --inst_learning_factor                  2
% 3.30/0.97  --inst_start_prop_sim_after_learn       3
% 3.30/0.97  --inst_sel_renew                        solver
% 3.30/0.97  --inst_lit_activity_flag                true
% 3.30/0.97  --inst_restr_to_given                   false
% 3.30/0.97  --inst_activity_threshold               500
% 3.30/0.97  --inst_out_proof                        true
% 3.30/0.97  
% 3.30/0.97  ------ Resolution Options
% 3.30/0.97  
% 3.30/0.97  --resolution_flag                       true
% 3.30/0.97  --res_lit_sel                           adaptive
% 3.30/0.97  --res_lit_sel_side                      none
% 3.30/0.97  --res_ordering                          kbo
% 3.30/0.97  --res_to_prop_solver                    active
% 3.30/0.97  --res_prop_simpl_new                    false
% 3.30/0.97  --res_prop_simpl_given                  true
% 3.30/0.97  --res_passive_queue_type                priority_queues
% 3.30/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.97  --res_passive_queues_freq               [15;5]
% 3.30/0.97  --res_forward_subs                      full
% 3.30/0.97  --res_backward_subs                     full
% 3.30/0.97  --res_forward_subs_resolution           true
% 3.30/0.97  --res_backward_subs_resolution          true
% 3.30/0.97  --res_orphan_elimination                true
% 3.30/0.97  --res_time_limit                        2.
% 3.30/0.97  --res_out_proof                         true
% 3.30/0.97  
% 3.30/0.97  ------ Superposition Options
% 3.30/0.97  
% 3.30/0.97  --superposition_flag                    true
% 3.30/0.97  --sup_passive_queue_type                priority_queues
% 3.30/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.97  --demod_completeness_check              fast
% 3.30/0.97  --demod_use_ground                      true
% 3.30/0.97  --sup_to_prop_solver                    passive
% 3.30/0.97  --sup_prop_simpl_new                    true
% 3.30/0.97  --sup_prop_simpl_given                  true
% 3.30/0.97  --sup_fun_splitting                     false
% 3.30/0.97  --sup_smt_interval                      50000
% 3.30/0.97  
% 3.30/0.97  ------ Superposition Simplification Setup
% 3.30/0.97  
% 3.30/0.97  --sup_indices_passive                   []
% 3.30/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.97  --sup_full_bw                           [BwDemod]
% 3.30/0.97  --sup_immed_triv                        [TrivRules]
% 3.30/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.97  --sup_immed_bw_main                     []
% 3.30/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.97  
% 3.30/0.97  ------ Combination Options
% 3.30/0.97  
% 3.30/0.97  --comb_res_mult                         3
% 3.30/0.97  --comb_sup_mult                         2
% 3.30/0.97  --comb_inst_mult                        10
% 3.30/0.97  
% 3.30/0.97  ------ Debug Options
% 3.30/0.97  
% 3.30/0.97  --dbg_backtrace                         false
% 3.30/0.97  --dbg_dump_prop_clauses                 false
% 3.30/0.97  --dbg_dump_prop_clauses_file            -
% 3.30/0.97  --dbg_out_stat                          false
% 3.30/0.97  ------ Parsing...
% 3.30/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/0.97  
% 3.30/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.30/0.97  
% 3.30/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/0.97  
% 3.30/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/0.97  ------ Proving...
% 3.30/0.97  ------ Problem Properties 
% 3.30/0.97  
% 3.30/0.97  
% 3.30/0.97  clauses                                 11
% 3.30/0.97  conjectures                             3
% 3.30/0.97  EPR                                     1
% 3.30/0.97  Horn                                    10
% 3.30/0.97  unary                                   9
% 3.30/0.97  binary                                  1
% 3.30/0.97  lits                                    14
% 3.30/0.97  lits eq                                 8
% 3.30/0.97  fd_pure                                 0
% 3.30/0.97  fd_pseudo                               0
% 3.30/0.97  fd_cond                                 0
% 3.30/0.97  fd_pseudo_cond                          1
% 3.30/0.97  AC symbols                              1
% 3.30/0.97  
% 3.30/0.97  ------ Schedule dynamic 5 is on 
% 3.30/0.97  
% 3.30/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.30/0.97  
% 3.30/0.97  
% 3.30/0.97  ------ 
% 3.30/0.97  Current options:
% 3.30/0.97  ------ 
% 3.30/0.97  
% 3.30/0.97  ------ Input Options
% 3.30/0.97  
% 3.30/0.97  --out_options                           all
% 3.30/0.97  --tptp_safe_out                         true
% 3.30/0.97  --problem_path                          ""
% 3.30/0.97  --include_path                          ""
% 3.30/0.97  --clausifier                            res/vclausify_rel
% 3.30/0.97  --clausifier_options                    --mode clausify
% 3.30/0.97  --stdin                                 false
% 3.30/0.97  --stats_out                             all
% 3.30/0.97  
% 3.30/0.97  ------ General Options
% 3.30/0.97  
% 3.30/0.97  --fof                                   false
% 3.30/0.97  --time_out_real                         305.
% 3.30/0.97  --time_out_virtual                      -1.
% 3.30/0.97  --symbol_type_check                     false
% 3.30/0.97  --clausify_out                          false
% 3.30/0.97  --sig_cnt_out                           false
% 3.30/0.97  --trig_cnt_out                          false
% 3.30/0.97  --trig_cnt_out_tolerance                1.
% 3.30/0.97  --trig_cnt_out_sk_spl                   false
% 3.30/0.97  --abstr_cl_out                          false
% 3.30/0.97  
% 3.30/0.97  ------ Global Options
% 3.30/0.97  
% 3.30/0.97  --schedule                              default
% 3.30/0.97  --add_important_lit                     false
% 3.30/0.97  --prop_solver_per_cl                    1000
% 3.30/0.97  --min_unsat_core                        false
% 3.30/0.97  --soft_assumptions                      false
% 3.30/0.97  --soft_lemma_size                       3
% 3.30/0.97  --prop_impl_unit_size                   0
% 3.30/0.97  --prop_impl_unit                        []
% 3.30/0.97  --share_sel_clauses                     true
% 3.30/0.97  --reset_solvers                         false
% 3.30/0.97  --bc_imp_inh                            [conj_cone]
% 3.30/0.97  --conj_cone_tolerance                   3.
% 3.30/0.97  --extra_neg_conj                        none
% 3.30/0.97  --large_theory_mode                     true
% 3.30/0.97  --prolific_symb_bound                   200
% 3.30/0.97  --lt_threshold                          2000
% 3.30/0.97  --clause_weak_htbl                      true
% 3.30/0.97  --gc_record_bc_elim                     false
% 3.30/0.97  
% 3.30/0.97  ------ Preprocessing Options
% 3.30/0.97  
% 3.30/0.97  --preprocessing_flag                    true
% 3.30/0.97  --time_out_prep_mult                    0.1
% 3.30/0.97  --splitting_mode                        input
% 3.30/0.97  --splitting_grd                         true
% 3.30/0.97  --splitting_cvd                         false
% 3.30/0.97  --splitting_cvd_svl                     false
% 3.30/0.97  --splitting_nvd                         32
% 3.30/0.97  --sub_typing                            true
% 3.30/0.97  --prep_gs_sim                           true
% 3.30/0.97  --prep_unflatten                        true
% 3.30/0.97  --prep_res_sim                          true
% 3.30/0.97  --prep_upred                            true
% 3.30/0.97  --prep_sem_filter                       exhaustive
% 3.30/0.97  --prep_sem_filter_out                   false
% 3.30/0.97  --pred_elim                             true
% 3.30/0.97  --res_sim_input                         true
% 3.30/0.97  --eq_ax_congr_red                       true
% 3.30/0.97  --pure_diseq_elim                       true
% 3.30/0.97  --brand_transform                       false
% 3.30/0.97  --non_eq_to_eq                          false
% 3.30/0.97  --prep_def_merge                        true
% 3.30/0.97  --prep_def_merge_prop_impl              false
% 3.30/0.97  --prep_def_merge_mbd                    true
% 3.30/0.97  --prep_def_merge_tr_red                 false
% 3.30/0.97  --prep_def_merge_tr_cl                  false
% 3.30/0.97  --smt_preprocessing                     true
% 3.30/0.97  --smt_ac_axioms                         fast
% 3.30/0.97  --preprocessed_out                      false
% 3.30/0.97  --preprocessed_stats                    false
% 3.30/0.97  
% 3.30/0.97  ------ Abstraction refinement Options
% 3.30/0.97  
% 3.30/0.97  --abstr_ref                             []
% 3.30/0.97  --abstr_ref_prep                        false
% 3.30/0.97  --abstr_ref_until_sat                   false
% 3.30/0.97  --abstr_ref_sig_restrict                funpre
% 3.30/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.97  --abstr_ref_under                       []
% 3.30/0.97  
% 3.30/0.97  ------ SAT Options
% 3.30/0.97  
% 3.30/0.97  --sat_mode                              false
% 3.30/0.97  --sat_fm_restart_options                ""
% 3.30/0.97  --sat_gr_def                            false
% 3.30/0.97  --sat_epr_types                         true
% 3.30/0.97  --sat_non_cyclic_types                  false
% 3.30/0.97  --sat_finite_models                     false
% 3.30/0.97  --sat_fm_lemmas                         false
% 3.30/0.97  --sat_fm_prep                           false
% 3.30/0.97  --sat_fm_uc_incr                        true
% 3.30/0.97  --sat_out_model                         small
% 3.30/0.97  --sat_out_clauses                       false
% 3.30/0.97  
% 3.30/0.97  ------ QBF Options
% 3.30/0.97  
% 3.30/0.97  --qbf_mode                              false
% 3.30/0.97  --qbf_elim_univ                         false
% 3.30/0.97  --qbf_dom_inst                          none
% 3.30/0.97  --qbf_dom_pre_inst                      false
% 3.30/0.97  --qbf_sk_in                             false
% 3.30/0.97  --qbf_pred_elim                         true
% 3.30/0.97  --qbf_split                             512
% 3.30/0.97  
% 3.30/0.97  ------ BMC1 Options
% 3.30/0.97  
% 3.30/0.97  --bmc1_incremental                      false
% 3.30/0.97  --bmc1_axioms                           reachable_all
% 3.30/0.97  --bmc1_min_bound                        0
% 3.30/0.97  --bmc1_max_bound                        -1
% 3.30/0.97  --bmc1_max_bound_default                -1
% 3.30/0.97  --bmc1_symbol_reachability              true
% 3.30/0.97  --bmc1_property_lemmas                  false
% 3.30/0.97  --bmc1_k_induction                      false
% 3.30/0.97  --bmc1_non_equiv_states                 false
% 3.30/0.97  --bmc1_deadlock                         false
% 3.30/0.97  --bmc1_ucm                              false
% 3.30/0.97  --bmc1_add_unsat_core                   none
% 3.30/0.97  --bmc1_unsat_core_children              false
% 3.30/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.97  --bmc1_out_stat                         full
% 3.30/0.97  --bmc1_ground_init                      false
% 3.30/0.97  --bmc1_pre_inst_next_state              false
% 3.30/0.97  --bmc1_pre_inst_state                   false
% 3.30/0.97  --bmc1_pre_inst_reach_state             false
% 3.30/0.97  --bmc1_out_unsat_core                   false
% 3.30/0.97  --bmc1_aig_witness_out                  false
% 3.30/0.97  --bmc1_verbose                          false
% 3.30/0.97  --bmc1_dump_clauses_tptp                false
% 3.30/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.97  --bmc1_dump_file                        -
% 3.30/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.97  --bmc1_ucm_extend_mode                  1
% 3.30/0.97  --bmc1_ucm_init_mode                    2
% 3.30/0.97  --bmc1_ucm_cone_mode                    none
% 3.30/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.97  --bmc1_ucm_relax_model                  4
% 3.30/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.97  --bmc1_ucm_layered_model                none
% 3.30/0.97  --bmc1_ucm_max_lemma_size               10
% 3.30/0.97  
% 3.30/0.97  ------ AIG Options
% 3.30/0.97  
% 3.30/0.97  --aig_mode                              false
% 3.30/0.97  
% 3.30/0.97  ------ Instantiation Options
% 3.30/0.97  
% 3.30/0.97  --instantiation_flag                    true
% 3.30/0.97  --inst_sos_flag                         false
% 3.30/0.97  --inst_sos_phase                        true
% 3.30/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.97  --inst_lit_sel_side                     none
% 3.30/0.97  --inst_solver_per_active                1400
% 3.30/0.97  --inst_solver_calls_frac                1.
% 3.30/0.97  --inst_passive_queue_type               priority_queues
% 3.30/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.97  --inst_passive_queues_freq              [25;2]
% 3.30/0.97  --inst_dismatching                      true
% 3.30/0.97  --inst_eager_unprocessed_to_passive     true
% 3.30/0.97  --inst_prop_sim_given                   true
% 3.30/0.97  --inst_prop_sim_new                     false
% 3.30/0.97  --inst_subs_new                         false
% 3.30/0.97  --inst_eq_res_simp                      false
% 3.30/0.97  --inst_subs_given                       false
% 3.30/0.97  --inst_orphan_elimination               true
% 3.30/0.97  --inst_learning_loop_flag               true
% 3.30/0.97  --inst_learning_start                   3000
% 3.30/0.97  --inst_learning_factor                  2
% 3.30/0.97  --inst_start_prop_sim_after_learn       3
% 3.30/0.97  --inst_sel_renew                        solver
% 3.30/0.97  --inst_lit_activity_flag                true
% 3.30/0.97  --inst_restr_to_given                   false
% 3.30/0.97  --inst_activity_threshold               500
% 3.30/0.97  --inst_out_proof                        true
% 3.30/0.97  
% 3.30/0.97  ------ Resolution Options
% 3.30/0.97  
% 3.30/0.97  --resolution_flag                       false
% 3.30/0.97  --res_lit_sel                           adaptive
% 3.30/0.97  --res_lit_sel_side                      none
% 3.30/0.97  --res_ordering                          kbo
% 3.30/0.97  --res_to_prop_solver                    active
% 3.30/0.97  --res_prop_simpl_new                    false
% 3.30/0.97  --res_prop_simpl_given                  true
% 3.30/0.97  --res_passive_queue_type                priority_queues
% 3.30/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.97  --res_passive_queues_freq               [15;5]
% 3.30/0.97  --res_forward_subs                      full
% 3.30/0.97  --res_backward_subs                     full
% 3.30/0.97  --res_forward_subs_resolution           true
% 3.30/0.97  --res_backward_subs_resolution          true
% 3.30/0.97  --res_orphan_elimination                true
% 3.30/0.97  --res_time_limit                        2.
% 3.30/0.97  --res_out_proof                         true
% 3.30/0.97  
% 3.30/0.97  ------ Superposition Options
% 3.30/0.97  
% 3.30/0.97  --superposition_flag                    true
% 3.30/0.97  --sup_passive_queue_type                priority_queues
% 3.30/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.97  --demod_completeness_check              fast
% 3.30/0.97  --demod_use_ground                      true
% 3.30/0.97  --sup_to_prop_solver                    passive
% 3.30/0.97  --sup_prop_simpl_new                    true
% 3.30/0.97  --sup_prop_simpl_given                  true
% 3.30/0.97  --sup_fun_splitting                     false
% 3.30/0.97  --sup_smt_interval                      50000
% 3.30/0.97  
% 3.30/0.97  ------ Superposition Simplification Setup
% 3.30/0.97  
% 3.30/0.97  --sup_indices_passive                   []
% 3.30/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.97  --sup_full_bw                           [BwDemod]
% 3.30/0.97  --sup_immed_triv                        [TrivRules]
% 3.30/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.97  --sup_immed_bw_main                     []
% 3.30/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.97  
% 3.30/0.97  ------ Combination Options
% 3.30/0.97  
% 3.30/0.97  --comb_res_mult                         3
% 3.30/0.97  --comb_sup_mult                         2
% 3.30/0.97  --comb_inst_mult                        10
% 3.30/0.97  
% 3.30/0.97  ------ Debug Options
% 3.30/0.97  
% 3.30/0.97  --dbg_backtrace                         false
% 3.30/0.97  --dbg_dump_prop_clauses                 false
% 3.30/0.97  --dbg_dump_prop_clauses_file            -
% 3.30/0.97  --dbg_out_stat                          false
% 3.30/0.97  
% 3.30/0.97  
% 3.30/0.97  
% 3.30/0.97  
% 3.30/0.97  ------ Proving...
% 3.30/0.97  
% 3.30/0.97  
% 3.30/0.97  % SZS status Theorem for theBenchmark.p
% 3.30/0.97  
% 3.30/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/0.97  
% 3.30/0.97  fof(f1,axiom,(
% 3.30/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f24,plain,(
% 3.30/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f1])).
% 3.30/0.97  
% 3.30/0.97  fof(f4,axiom,(
% 3.30/0.97    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f27,plain,(
% 3.30/0.97    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f4])).
% 3.30/0.97  
% 3.30/0.97  fof(f12,conjecture,(
% 3.30/0.97    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f13,negated_conjecture,(
% 3.30/0.97    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.30/0.97    inference(negated_conjecture,[],[f12])).
% 3.30/0.97  
% 3.30/0.97  fof(f18,plain,(
% 3.30/0.97    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 3.30/0.97    inference(ennf_transformation,[],[f13])).
% 3.30/0.97  
% 3.30/0.97  fof(f19,plain,(
% 3.30/0.97    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 3.30/0.97    inference(flattening,[],[f18])).
% 3.30/0.97  
% 3.30/0.97  fof(f22,plain,(
% 3.30/0.97    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1))),
% 3.30/0.97    introduced(choice_axiom,[])).
% 3.30/0.97  
% 3.30/0.97  fof(f23,plain,(
% 3.30/0.97    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1)),
% 3.30/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f22])).
% 3.30/0.97  
% 3.30/0.97  fof(f38,plain,(
% 3.30/0.97    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 3.30/0.97    inference(cnf_transformation,[],[f23])).
% 3.30/0.97  
% 3.30/0.97  fof(f6,axiom,(
% 3.30/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f29,plain,(
% 3.30/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f6])).
% 3.30/0.97  
% 3.30/0.97  fof(f7,axiom,(
% 3.30/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f30,plain,(
% 3.30/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f7])).
% 3.30/0.97  
% 3.30/0.97  fof(f8,axiom,(
% 3.30/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f31,plain,(
% 3.30/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f8])).
% 3.30/0.97  
% 3.30/0.97  fof(f9,axiom,(
% 3.30/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f32,plain,(
% 3.30/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f9])).
% 3.30/0.97  
% 3.30/0.97  fof(f41,plain,(
% 3.30/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.30/0.97    inference(definition_unfolding,[],[f31,f32])).
% 3.30/0.97  
% 3.30/0.97  fof(f42,plain,(
% 3.30/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.30/0.97    inference(definition_unfolding,[],[f30,f41])).
% 3.30/0.97  
% 3.30/0.97  fof(f43,plain,(
% 3.30/0.97    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.30/0.97    inference(definition_unfolding,[],[f29,f42])).
% 3.30/0.97  
% 3.30/0.97  fof(f49,plain,(
% 3.30/0.97    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 3.30/0.97    inference(definition_unfolding,[],[f38,f43])).
% 3.30/0.97  
% 3.30/0.97  fof(f3,axiom,(
% 3.30/0.97    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f26,plain,(
% 3.30/0.97    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f3])).
% 3.30/0.97  
% 3.30/0.97  fof(f11,axiom,(
% 3.30/0.97    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f20,plain,(
% 3.30/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.30/0.97    inference(nnf_transformation,[],[f11])).
% 3.30/0.97  
% 3.30/0.97  fof(f21,plain,(
% 3.30/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.30/0.97    inference(flattening,[],[f20])).
% 3.30/0.97  
% 3.30/0.97  fof(f34,plain,(
% 3.30/0.97    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.30/0.97    inference(cnf_transformation,[],[f21])).
% 3.30/0.97  
% 3.30/0.97  fof(f47,plain,(
% 3.30/0.97    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 3.30/0.97    inference(definition_unfolding,[],[f34,f43,f43])).
% 3.30/0.97  
% 3.30/0.97  fof(f37,plain,(
% 3.30/0.97    r1_tarski(sK0,sK1)),
% 3.30/0.97    inference(cnf_transformation,[],[f23])).
% 3.30/0.97  
% 3.30/0.97  fof(f5,axiom,(
% 3.30/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f16,plain,(
% 3.30/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.30/0.97    inference(ennf_transformation,[],[f5])).
% 3.30/0.97  
% 3.30/0.97  fof(f28,plain,(
% 3.30/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f16])).
% 3.30/0.97  
% 3.30/0.97  fof(f2,axiom,(
% 3.30/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f14,plain,(
% 3.30/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 3.30/0.97    inference(unused_predicate_definition_removal,[],[f2])).
% 3.30/0.97  
% 3.30/0.97  fof(f15,plain,(
% 3.30/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 3.30/0.97    inference(ennf_transformation,[],[f14])).
% 3.30/0.97  
% 3.30/0.97  fof(f25,plain,(
% 3.30/0.97    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.30/0.97    inference(cnf_transformation,[],[f15])).
% 3.30/0.97  
% 3.30/0.97  fof(f10,axiom,(
% 3.30/0.97    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.30/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.97  
% 3.30/0.97  fof(f17,plain,(
% 3.30/0.97    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.30/0.97    inference(ennf_transformation,[],[f10])).
% 3.30/0.97  
% 3.30/0.97  fof(f33,plain,(
% 3.30/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.30/0.97    inference(cnf_transformation,[],[f17])).
% 3.30/0.97  
% 3.30/0.97  fof(f44,plain,(
% 3.30/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 3.30/0.97    inference(definition_unfolding,[],[f33,f43])).
% 3.30/0.97  
% 3.30/0.97  fof(f39,plain,(
% 3.30/0.97    r2_hidden(sK3,sK0)),
% 3.30/0.97    inference(cnf_transformation,[],[f23])).
% 3.30/0.97  
% 3.30/0.97  fof(f40,plain,(
% 3.30/0.97    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 3.30/0.97    inference(cnf_transformation,[],[f23])).
% 3.30/0.97  
% 3.30/0.97  fof(f48,plain,(
% 3.30/0.97    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 3.30/0.97    inference(definition_unfolding,[],[f40,f43])).
% 3.30/0.97  
% 3.30/0.97  cnf(c_0,plain,
% 3.30/0.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.30/0.97      inference(cnf_transformation,[],[f24]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_289,plain,
% 3.30/0.97      ( k3_xboole_0(X0_38,X1_38) = k3_xboole_0(X1_38,X0_38) ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_3,plain,
% 3.30/0.97      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.30/0.97      inference(cnf_transformation,[],[f27]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_287,plain,
% 3.30/0.97      ( r1_tarski(k3_xboole_0(X0_38,X1_38),X0_38) ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_406,plain,
% 3.30/0.97      ( r1_tarski(k3_xboole_0(X0_38,X1_38),X0_38) = iProver_top ),
% 3.30/0.97      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_599,plain,
% 3.30/0.97      ( r1_tarski(k3_xboole_0(X0_38,X1_38),X1_38) = iProver_top ),
% 3.30/0.97      inference(superposition,[status(thm)],[c_289,c_406]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_11,negated_conjecture,
% 3.30/0.97      ( k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.30/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_281,negated_conjecture,
% 3.30/0.97      ( k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_11]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_2,plain,
% 3.30/0.97      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 3.30/0.97      inference(cnf_transformation,[],[f26]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_290,negated_conjecture,
% 3.30/0.97      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_xboole_0(sK2,sK1) ),
% 3.30/0.97      inference(theory_normalisation,[status(thm)],[c_281,c_2,c_0]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_8,plain,
% 3.30/0.97      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 3.30/0.97      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 3.30/0.97      | k1_xboole_0 = X0 ),
% 3.30/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_283,plain,
% 3.30/0.97      ( ~ r1_tarski(X0_38,k3_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39))
% 3.30/0.97      | k3_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39) = X0_38
% 3.30/0.97      | k1_xboole_0 = X0_38 ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_8]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_410,plain,
% 3.30/0.97      ( k3_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39) = X0_38
% 3.30/0.97      | k1_xboole_0 = X0_38
% 3.30/0.97      | r1_tarski(X0_38,k3_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39)) != iProver_top ),
% 3.30/0.97      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_4707,plain,
% 3.30/0.97      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = X0_38
% 3.30/0.97      | k1_xboole_0 = X0_38
% 3.30/0.97      | r1_tarski(X0_38,k3_xboole_0(sK2,sK1)) != iProver_top ),
% 3.30/0.97      inference(superposition,[status(thm)],[c_290,c_410]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_4711,plain,
% 3.30/0.97      ( k3_xboole_0(sK2,sK1) = X0_38
% 3.30/0.97      | k1_xboole_0 = X0_38
% 3.30/0.97      | r1_tarski(X0_38,k3_xboole_0(sK2,sK1)) != iProver_top ),
% 3.30/0.97      inference(demodulation,[status(thm)],[c_4707,c_290]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_5945,plain,
% 3.30/0.97      ( k3_xboole_0(X0_38,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK2,sK1)
% 3.30/0.97      | k3_xboole_0(X0_38,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 3.30/0.97      inference(superposition,[status(thm)],[c_599,c_4711]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_12,negated_conjecture,
% 3.30/0.97      ( r1_tarski(sK0,sK1) ),
% 3.30/0.97      inference(cnf_transformation,[],[f37]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_280,negated_conjecture,
% 3.30/0.97      ( r1_tarski(sK0,sK1) ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_12]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_411,plain,
% 3.30/0.97      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.30/0.97      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_4,plain,
% 3.30/0.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.30/0.97      inference(cnf_transformation,[],[f28]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_286,plain,
% 3.30/0.97      ( ~ r1_tarski(X0_38,X1_38) | k3_xboole_0(X0_38,X1_38) = X0_38 ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_407,plain,
% 3.30/0.97      ( k3_xboole_0(X0_38,X1_38) = X0_38
% 3.30/0.97      | r1_tarski(X0_38,X1_38) != iProver_top ),
% 3.30/0.97      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_1588,plain,
% 3.30/0.97      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 3.30/0.97      inference(superposition,[status(thm)],[c_411,c_407]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_288,plain,
% 3.30/0.97      ( k3_xboole_0(k3_xboole_0(X0_38,X1_38),X2_38) = k3_xboole_0(X0_38,k3_xboole_0(X1_38,X2_38)) ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_2559,plain,
% 3.30/0.97      ( k3_xboole_0(sK0,k3_xboole_0(sK1,X0_38)) = k3_xboole_0(sK0,X0_38) ),
% 3.30/0.97      inference(superposition,[status(thm)],[c_1588,c_288]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_3398,plain,
% 3.30/0.97      ( k3_xboole_0(sK0,k3_xboole_0(X0_38,sK1)) = k3_xboole_0(sK0,X0_38) ),
% 3.30/0.97      inference(superposition,[status(thm)],[c_289,c_2559]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_6594,plain,
% 3.30/0.97      ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK0,sK2)
% 3.30/0.97      | k3_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 3.30/0.97      inference(superposition,[status(thm)],[c_5945,c_3398]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_6603,plain,
% 3.30/0.97      ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK0,sK2)
% 3.30/0.97      | k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 3.30/0.97      inference(demodulation,[status(thm)],[c_6594,c_3398]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_1,plain,
% 3.30/0.97      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.30/0.97      inference(cnf_transformation,[],[f25]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_5,plain,
% 3.30/0.97      ( ~ r2_hidden(X0,X1)
% 3.30/0.97      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.30/0.97      inference(cnf_transformation,[],[f44]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_10,negated_conjecture,
% 3.30/0.97      ( r2_hidden(sK3,sK0) ),
% 3.30/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_112,plain,
% 3.30/0.97      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
% 3.30/0.97      | sK3 != X0
% 3.30/0.97      | sK0 != X1 ),
% 3.30/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_113,plain,
% 3.30/0.97      ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) ),
% 3.30/0.97      inference(unflattening,[status(thm)],[c_112]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_121,plain,
% 3.30/0.97      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X0
% 3.30/0.97      | k3_xboole_0(X0,X1) != k1_xboole_0
% 3.30/0.97      | sK0 != X1 ),
% 3.30/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_113]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_122,plain,
% 3.30/0.97      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) != k1_xboole_0 ),
% 3.30/0.97      inference(unflattening,[status(thm)],[c_121]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_279,plain,
% 3.30/0.97      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) != k1_xboole_0 ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_122]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_291,plain,
% 3.30/0.97      ( k3_xboole_0(sK0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
% 3.30/0.97      inference(theory_normalisation,[status(thm)],[c_279,c_2,c_0]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_427,plain,
% 3.30/0.97      ( k3_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k1_xboole_0 ),
% 3.30/0.97      inference(light_normalisation,[status(thm)],[c_291,c_290]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_3694,plain,
% 3.30/0.97      ( k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 3.30/0.97      inference(demodulation,[status(thm)],[c_3398,c_427]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_9,negated_conjecture,
% 3.30/0.97      ( k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.30/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_282,negated_conjecture,
% 3.30/0.97      ( k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.30/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(c_424,plain,
% 3.30/0.97      ( k3_xboole_0(sK2,sK1) != k3_xboole_0(sK0,sK2) ),
% 3.30/0.97      inference(light_normalisation,[status(thm)],[c_282,c_290]) ).
% 3.30/0.97  
% 3.30/0.97  cnf(contradiction,plain,
% 3.30/0.97      ( $false ),
% 3.30/0.97      inference(minisat,[status(thm)],[c_6603,c_3694,c_424]) ).
% 3.30/0.97  
% 3.30/0.97  
% 3.30/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/0.97  
% 3.30/0.97  ------                               Statistics
% 3.30/0.97  
% 3.30/0.97  ------ General
% 3.30/0.97  
% 3.30/0.97  abstr_ref_over_cycles:                  0
% 3.30/0.97  abstr_ref_under_cycles:                 0
% 3.30/0.97  gc_basic_clause_elim:                   0
% 3.30/0.97  forced_gc_time:                         0
% 3.30/0.97  parsing_time:                           0.009
% 3.30/0.97  unif_index_cands_time:                  0.
% 3.30/0.97  unif_index_add_time:                    0.
% 3.30/0.97  orderings_time:                         0.
% 3.30/0.97  out_proof_time:                         0.006
% 3.30/0.97  total_time:                             0.201
% 3.30/0.97  num_of_symbols:                         43
% 3.30/0.97  num_of_terms:                           6475
% 3.30/0.97  
% 3.30/0.97  ------ Preprocessing
% 3.30/0.97  
% 3.30/0.97  num_of_splits:                          0
% 3.30/0.97  num_of_split_atoms:                     0
% 3.30/0.97  num_of_reused_defs:                     0
% 3.30/0.97  num_eq_ax_congr_red:                    6
% 3.30/0.97  num_of_sem_filtered_clauses:            1
% 3.30/0.97  num_of_subtypes:                        2
% 3.30/0.97  monotx_restored_types:                  0
% 3.30/0.97  sat_num_of_epr_types:                   0
% 3.30/0.97  sat_num_of_non_cyclic_types:            0
% 3.30/0.97  sat_guarded_non_collapsed_types:        1
% 3.30/0.97  num_pure_diseq_elim:                    0
% 3.30/0.97  simp_replaced_by:                       0
% 3.30/0.97  res_preprocessed:                       55
% 3.30/0.97  prep_upred:                             0
% 3.30/0.97  prep_unflattend:                        30
% 3.30/0.97  smt_new_axioms:                         0
% 3.30/0.97  pred_elim_cands:                        1
% 3.30/0.97  pred_elim:                              2
% 3.30/0.97  pred_elim_cl:                           2
% 3.30/0.97  pred_elim_cycles:                       4
% 3.30/0.97  merged_defs:                            0
% 3.30/0.97  merged_defs_ncl:                        0
% 3.30/0.97  bin_hyper_res:                          0
% 3.30/0.97  prep_cycles:                            4
% 3.30/0.97  pred_elim_time:                         0.002
% 3.30/0.97  splitting_time:                         0.
% 3.30/0.97  sem_filter_time:                        0.
% 3.30/0.97  monotx_time:                            0.
% 3.30/0.97  subtype_inf_time:                       0.
% 3.30/0.97  
% 3.30/0.97  ------ Problem properties
% 3.30/0.97  
% 3.30/0.97  clauses:                                11
% 3.30/0.97  conjectures:                            3
% 3.30/0.97  epr:                                    1
% 3.30/0.97  horn:                                   10
% 3.30/0.97  ground:                                 4
% 3.30/0.97  unary:                                  9
% 3.30/0.97  binary:                                 1
% 3.30/0.97  lits:                                   14
% 3.30/0.97  lits_eq:                                8
% 3.30/0.97  fd_pure:                                0
% 3.30/0.97  fd_pseudo:                              0
% 3.30/0.97  fd_cond:                                0
% 3.30/0.97  fd_pseudo_cond:                         1
% 3.30/0.97  ac_symbols:                             1
% 3.30/0.97  
% 3.30/0.97  ------ Propositional Solver
% 3.30/0.97  
% 3.30/0.97  prop_solver_calls:                      30
% 3.30/0.97  prop_fast_solver_calls:                 248
% 3.30/0.97  smt_solver_calls:                       0
% 3.30/0.97  smt_fast_solver_calls:                  0
% 3.30/0.97  prop_num_of_clauses:                    2522
% 3.30/0.97  prop_preprocess_simplified:             4830
% 3.30/0.97  prop_fo_subsumed:                       0
% 3.30/0.97  prop_solver_time:                       0.
% 3.30/0.97  smt_solver_time:                        0.
% 3.30/0.97  smt_fast_solver_time:                   0.
% 3.30/0.97  prop_fast_solver_time:                  0.
% 3.30/0.97  prop_unsat_core_time:                   0.
% 3.30/0.97  
% 3.30/0.97  ------ QBF
% 3.30/0.97  
% 3.30/0.97  qbf_q_res:                              0
% 3.30/0.97  qbf_num_tautologies:                    0
% 3.30/0.97  qbf_prep_cycles:                        0
% 3.30/0.97  
% 3.30/0.97  ------ BMC1
% 3.30/0.97  
% 3.30/0.97  bmc1_current_bound:                     -1
% 3.30/0.97  bmc1_last_solved_bound:                 -1
% 3.30/0.97  bmc1_unsat_core_size:                   -1
% 3.30/0.97  bmc1_unsat_core_parents_size:           -1
% 3.30/0.97  bmc1_merge_next_fun:                    0
% 3.30/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.30/0.97  
% 3.30/0.97  ------ Instantiation
% 3.30/0.97  
% 3.30/0.97  inst_num_of_clauses:                    653
% 3.30/0.97  inst_num_in_passive:                    325
% 3.30/0.97  inst_num_in_active:                     252
% 3.30/0.97  inst_num_in_unprocessed:                76
% 3.30/0.97  inst_num_of_loops:                      280
% 3.30/0.97  inst_num_of_learning_restarts:          0
% 3.30/0.97  inst_num_moves_active_passive:          24
% 3.30/0.97  inst_lit_activity:                      0
% 3.30/0.97  inst_lit_activity_moves:                0
% 3.30/0.97  inst_num_tautologies:                   0
% 3.30/0.97  inst_num_prop_implied:                  0
% 3.30/0.97  inst_num_existing_simplified:           0
% 3.30/0.97  inst_num_eq_res_simplified:             0
% 3.30/0.97  inst_num_child_elim:                    0
% 3.30/0.97  inst_num_of_dismatching_blockings:      441
% 3.30/0.97  inst_num_of_non_proper_insts:           696
% 3.30/0.97  inst_num_of_duplicates:                 0
% 3.30/0.97  inst_inst_num_from_inst_to_res:         0
% 3.30/0.97  inst_dismatching_checking_time:         0.
% 3.30/0.97  
% 3.30/0.97  ------ Resolution
% 3.30/0.97  
% 3.30/0.97  res_num_of_clauses:                     0
% 3.30/0.97  res_num_in_passive:                     0
% 3.30/0.97  res_num_in_active:                      0
% 3.30/0.97  res_num_of_loops:                       59
% 3.30/0.97  res_forward_subset_subsumed:            159
% 3.30/0.97  res_backward_subset_subsumed:           2
% 3.30/0.97  res_forward_subsumed:                   0
% 3.30/0.97  res_backward_subsumed:                  0
% 3.30/0.97  res_forward_subsumption_resolution:     0
% 3.30/0.97  res_backward_subsumption_resolution:    0
% 3.30/0.97  res_clause_to_clause_subsumption:       3944
% 3.30/0.97  res_orphan_elimination:                 0
% 3.30/0.97  res_tautology_del:                      68
% 3.30/0.97  res_num_eq_res_simplified:              0
% 3.30/0.97  res_num_sel_changes:                    0
% 3.30/0.97  res_moves_from_active_to_pass:          0
% 3.30/0.97  
% 3.30/0.97  ------ Superposition
% 3.30/0.97  
% 3.30/0.97  sup_time_total:                         0.
% 3.30/0.97  sup_time_generating:                    0.
% 3.30/0.97  sup_time_sim_full:                      0.
% 3.30/0.97  sup_time_sim_immed:                     0.
% 3.30/0.97  
% 3.30/0.97  sup_num_of_clauses:                     391
% 3.30/0.97  sup_num_in_active:                      54
% 3.30/0.97  sup_num_in_passive:                     337
% 3.30/0.97  sup_num_of_loops:                       54
% 3.30/0.97  sup_fw_superposition:                   455
% 3.30/0.97  sup_bw_superposition:                   519
% 3.30/0.97  sup_immediate_simplified:               135
% 3.30/0.97  sup_given_eliminated:                   0
% 3.30/0.97  comparisons_done:                       0
% 3.30/0.97  comparisons_avoided:                    0
% 3.30/0.97  
% 3.30/0.97  ------ Simplifications
% 3.30/0.97  
% 3.30/0.97  
% 3.30/0.97  sim_fw_subset_subsumed:                 8
% 3.30/0.97  sim_bw_subset_subsumed:                 0
% 3.30/0.97  sim_fw_subsumed:                        74
% 3.30/0.97  sim_bw_subsumed:                        1
% 3.30/0.97  sim_fw_subsumption_res:                 0
% 3.30/0.97  sim_bw_subsumption_res:                 0
% 3.30/0.97  sim_tautology_del:                      0
% 3.30/0.97  sim_eq_tautology_del:                   4
% 3.30/0.97  sim_eq_res_simp:                        0
% 3.30/0.97  sim_fw_demodulated:                     5
% 3.30/0.97  sim_bw_demodulated:                     1
% 3.30/0.97  sim_light_normalised:                   56
% 3.30/0.97  sim_joinable_taut:                      0
% 3.30/0.97  sim_joinable_simp:                      0
% 3.30/0.97  sim_ac_normalised:                      0
% 3.30/0.97  sim_smt_subsumption:                    0
% 3.30/0.97  
%------------------------------------------------------------------------------
