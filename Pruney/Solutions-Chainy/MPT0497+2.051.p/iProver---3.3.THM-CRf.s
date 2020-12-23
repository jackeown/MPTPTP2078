%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:55 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 381 expanded)
%              Number of clauses        :   58 ( 138 expanded)
%              Number of leaves         :   15 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  222 (1124 expanded)
%              Number of equality atoms :  128 ( 541 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f50,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f33])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_574,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_581,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1380,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK1),sK0) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_574,c_581])).

cnf(c_5,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_583,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1379,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_583,c_581])).

cnf(c_2656,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(sK0,k1_relat_1(sK1))) = k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[status(thm)],[c_1380,c_1379])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_703,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2128,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_582,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2302,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_582])).

cnf(c_573,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_576,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1497,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_573,c_576])).

cnf(c_2710,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1380,c_1497])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_585,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1181,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_583,c_585])).

cnf(c_2753,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2710,c_1181])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1010,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,X0))
    | k1_relat_1(k7_relat_1(sK1,X0)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5957,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_7624,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2656,c_18,c_21,c_2128,c_2302,c_2753,c_5957])).

cnf(c_2721,plain,
    ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0))) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_1497,c_1497])).

cnf(c_10787,plain,
    ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),sK0))) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7624,c_2721])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10841,plain,
    ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),sK0))) = k4_xboole_0(k1_relat_1(sK1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10787,c_11])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10842,plain,
    ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),sK0))) = k1_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_10841,c_2])).

cnf(c_14,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_577,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_587,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1804,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(X0,k4_xboole_0(X1,X2))),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_577,c_587])).

cnf(c_11134,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10842,c_1804])).

cnf(c_192,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_191,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2236,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_192,c_191])).

cnf(c_4677,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k7_relat_1(sK1,sK0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2236,c_17])).

cnf(c_5185,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | X0 != k1_xboole_0
    | k7_relat_1(sK1,sK0) = X0 ),
    inference(resolution,[status(thm)],[c_4677,c_192])).

cnf(c_2234,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | X0 != k7_relat_1(sK1,sK0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_192,c_17])).

cnf(c_5420,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k7_relat_1(sK1,sK0) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[status(thm)],[c_5185,c_2234])).

cnf(c_4,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_49,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1035,plain,
    ( X0 != X1
    | X0 = k7_relat_1(sK1,X2)
    | k7_relat_1(sK1,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_5525,plain,
    ( k7_relat_1(sK1,sK0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_5526,plain,
    ( k7_relat_1(sK1,sK0) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5525])).

cnf(c_5738,plain,
    ( k7_relat_1(sK1,sK0) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5420,c_4,c_49,c_5526])).

cnf(c_19,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11134,c_7624,c_5738,c_21,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:47:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 4.00/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.98  
% 4.00/0.98  ------  iProver source info
% 4.00/0.98  
% 4.00/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.98  git: non_committed_changes: false
% 4.00/0.98  git: last_make_outside_of_git: false
% 4.00/0.98  
% 4.00/0.98  ------ 
% 4.00/0.98  
% 4.00/0.98  ------ Input Options
% 4.00/0.98  
% 4.00/0.98  --out_options                           all
% 4.00/0.98  --tptp_safe_out                         true
% 4.00/0.98  --problem_path                          ""
% 4.00/0.98  --include_path                          ""
% 4.00/0.98  --clausifier                            res/vclausify_rel
% 4.00/0.98  --clausifier_options                    --mode clausify
% 4.00/0.98  --stdin                                 false
% 4.00/0.98  --stats_out                             sel
% 4.00/0.98  
% 4.00/0.98  ------ General Options
% 4.00/0.98  
% 4.00/0.98  --fof                                   false
% 4.00/0.98  --time_out_real                         604.99
% 4.00/0.98  --time_out_virtual                      -1.
% 4.00/0.98  --symbol_type_check                     false
% 4.00/0.98  --clausify_out                          false
% 4.00/0.98  --sig_cnt_out                           false
% 4.00/0.98  --trig_cnt_out                          false
% 4.00/0.98  --trig_cnt_out_tolerance                1.
% 4.00/0.98  --trig_cnt_out_sk_spl                   false
% 4.00/0.98  --abstr_cl_out                          false
% 4.00/0.98  
% 4.00/0.98  ------ Global Options
% 4.00/0.98  
% 4.00/0.98  --schedule                              none
% 4.00/0.98  --add_important_lit                     false
% 4.00/0.98  --prop_solver_per_cl                    1000
% 4.00/0.98  --min_unsat_core                        false
% 4.00/0.98  --soft_assumptions                      false
% 4.00/0.98  --soft_lemma_size                       3
% 4.00/0.98  --prop_impl_unit_size                   0
% 4.00/0.98  --prop_impl_unit                        []
% 4.00/0.98  --share_sel_clauses                     true
% 4.00/0.98  --reset_solvers                         false
% 4.00/0.98  --bc_imp_inh                            [conj_cone]
% 4.00/0.98  --conj_cone_tolerance                   3.
% 4.00/0.98  --extra_neg_conj                        none
% 4.00/0.98  --large_theory_mode                     true
% 4.00/0.98  --prolific_symb_bound                   200
% 4.00/0.98  --lt_threshold                          2000
% 4.00/0.98  --clause_weak_htbl                      true
% 4.00/0.98  --gc_record_bc_elim                     false
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing Options
% 4.00/0.98  
% 4.00/0.98  --preprocessing_flag                    true
% 4.00/0.98  --time_out_prep_mult                    0.1
% 4.00/0.98  --splitting_mode                        input
% 4.00/0.98  --splitting_grd                         true
% 4.00/0.98  --splitting_cvd                         false
% 4.00/0.98  --splitting_cvd_svl                     false
% 4.00/0.98  --splitting_nvd                         32
% 4.00/0.98  --sub_typing                            true
% 4.00/0.98  --prep_gs_sim                           false
% 4.00/0.98  --prep_unflatten                        true
% 4.00/0.98  --prep_res_sim                          true
% 4.00/0.98  --prep_upred                            true
% 4.00/0.98  --prep_sem_filter                       exhaustive
% 4.00/0.98  --prep_sem_filter_out                   false
% 4.00/0.98  --pred_elim                             false
% 4.00/0.98  --res_sim_input                         true
% 4.00/0.98  --eq_ax_congr_red                       true
% 4.00/0.98  --pure_diseq_elim                       true
% 4.00/0.98  --brand_transform                       false
% 4.00/0.98  --non_eq_to_eq                          false
% 4.00/0.98  --prep_def_merge                        true
% 4.00/0.98  --prep_def_merge_prop_impl              false
% 4.00/0.98  --prep_def_merge_mbd                    true
% 4.00/0.98  --prep_def_merge_tr_red                 false
% 4.00/0.98  --prep_def_merge_tr_cl                  false
% 4.00/0.98  --smt_preprocessing                     true
% 4.00/0.98  --smt_ac_axioms                         fast
% 4.00/0.98  --preprocessed_out                      false
% 4.00/0.98  --preprocessed_stats                    false
% 4.00/0.98  
% 4.00/0.98  ------ Abstraction refinement Options
% 4.00/0.98  
% 4.00/0.98  --abstr_ref                             []
% 4.00/0.98  --abstr_ref_prep                        false
% 4.00/0.98  --abstr_ref_until_sat                   false
% 4.00/0.98  --abstr_ref_sig_restrict                funpre
% 4.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.98  --abstr_ref_under                       []
% 4.00/0.98  
% 4.00/0.98  ------ SAT Options
% 4.00/0.98  
% 4.00/0.98  --sat_mode                              false
% 4.00/0.98  --sat_fm_restart_options                ""
% 4.00/0.98  --sat_gr_def                            false
% 4.00/0.98  --sat_epr_types                         true
% 4.00/0.98  --sat_non_cyclic_types                  false
% 4.00/0.98  --sat_finite_models                     false
% 4.00/0.98  --sat_fm_lemmas                         false
% 4.00/0.98  --sat_fm_prep                           false
% 4.00/0.98  --sat_fm_uc_incr                        true
% 4.00/0.98  --sat_out_model                         small
% 4.00/0.98  --sat_out_clauses                       false
% 4.00/0.98  
% 4.00/0.98  ------ QBF Options
% 4.00/0.98  
% 4.00/0.98  --qbf_mode                              false
% 4.00/0.98  --qbf_elim_univ                         false
% 4.00/0.98  --qbf_dom_inst                          none
% 4.00/0.98  --qbf_dom_pre_inst                      false
% 4.00/0.98  --qbf_sk_in                             false
% 4.00/0.98  --qbf_pred_elim                         true
% 4.00/0.98  --qbf_split                             512
% 4.00/0.98  
% 4.00/0.98  ------ BMC1 Options
% 4.00/0.98  
% 4.00/0.98  --bmc1_incremental                      false
% 4.00/0.98  --bmc1_axioms                           reachable_all
% 4.00/0.98  --bmc1_min_bound                        0
% 4.00/0.98  --bmc1_max_bound                        -1
% 4.00/0.98  --bmc1_max_bound_default                -1
% 4.00/0.98  --bmc1_symbol_reachability              true
% 4.00/0.98  --bmc1_property_lemmas                  false
% 4.00/0.98  --bmc1_k_induction                      false
% 4.00/0.98  --bmc1_non_equiv_states                 false
% 4.00/0.98  --bmc1_deadlock                         false
% 4.00/0.98  --bmc1_ucm                              false
% 4.00/0.98  --bmc1_add_unsat_core                   none
% 4.00/0.98  --bmc1_unsat_core_children              false
% 4.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.98  --bmc1_out_stat                         full
% 4.00/0.98  --bmc1_ground_init                      false
% 4.00/0.98  --bmc1_pre_inst_next_state              false
% 4.00/0.98  --bmc1_pre_inst_state                   false
% 4.00/0.98  --bmc1_pre_inst_reach_state             false
% 4.00/0.98  --bmc1_out_unsat_core                   false
% 4.00/0.98  --bmc1_aig_witness_out                  false
% 4.00/0.98  --bmc1_verbose                          false
% 4.00/0.98  --bmc1_dump_clauses_tptp                false
% 4.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.98  --bmc1_dump_file                        -
% 4.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.98  --bmc1_ucm_extend_mode                  1
% 4.00/0.98  --bmc1_ucm_init_mode                    2
% 4.00/0.98  --bmc1_ucm_cone_mode                    none
% 4.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.98  --bmc1_ucm_relax_model                  4
% 4.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.98  --bmc1_ucm_layered_model                none
% 4.00/0.98  --bmc1_ucm_max_lemma_size               10
% 4.00/0.98  
% 4.00/0.98  ------ AIG Options
% 4.00/0.98  
% 4.00/0.98  --aig_mode                              false
% 4.00/0.98  
% 4.00/0.98  ------ Instantiation Options
% 4.00/0.98  
% 4.00/0.98  --instantiation_flag                    true
% 4.00/0.98  --inst_sos_flag                         false
% 4.00/0.98  --inst_sos_phase                        true
% 4.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel_side                     num_symb
% 4.00/0.98  --inst_solver_per_active                1400
% 4.00/0.98  --inst_solver_calls_frac                1.
% 4.00/0.98  --inst_passive_queue_type               priority_queues
% 4.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.98  --inst_passive_queues_freq              [25;2]
% 4.00/0.98  --inst_dismatching                      true
% 4.00/0.98  --inst_eager_unprocessed_to_passive     true
% 4.00/0.98  --inst_prop_sim_given                   true
% 4.00/0.98  --inst_prop_sim_new                     false
% 4.00/0.98  --inst_subs_new                         false
% 4.00/0.98  --inst_eq_res_simp                      false
% 4.00/0.98  --inst_subs_given                       false
% 4.00/0.98  --inst_orphan_elimination               true
% 4.00/0.98  --inst_learning_loop_flag               true
% 4.00/0.98  --inst_learning_start                   3000
% 4.00/0.98  --inst_learning_factor                  2
% 4.00/0.98  --inst_start_prop_sim_after_learn       3
% 4.00/0.98  --inst_sel_renew                        solver
% 4.00/0.98  --inst_lit_activity_flag                true
% 4.00/0.98  --inst_restr_to_given                   false
% 4.00/0.98  --inst_activity_threshold               500
% 4.00/0.98  --inst_out_proof                        true
% 4.00/0.98  
% 4.00/0.98  ------ Resolution Options
% 4.00/0.98  
% 4.00/0.98  --resolution_flag                       true
% 4.00/0.98  --res_lit_sel                           adaptive
% 4.00/0.98  --res_lit_sel_side                      none
% 4.00/0.98  --res_ordering                          kbo
% 4.00/0.98  --res_to_prop_solver                    active
% 4.00/0.98  --res_prop_simpl_new                    false
% 4.00/0.98  --res_prop_simpl_given                  true
% 4.00/0.98  --res_passive_queue_type                priority_queues
% 4.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.98  --res_passive_queues_freq               [15;5]
% 4.00/0.98  --res_forward_subs                      full
% 4.00/0.98  --res_backward_subs                     full
% 4.00/0.98  --res_forward_subs_resolution           true
% 4.00/0.98  --res_backward_subs_resolution          true
% 4.00/0.98  --res_orphan_elimination                true
% 4.00/0.98  --res_time_limit                        2.
% 4.00/0.98  --res_out_proof                         true
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Options
% 4.00/0.98  
% 4.00/0.98  --superposition_flag                    true
% 4.00/0.98  --sup_passive_queue_type                priority_queues
% 4.00/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.98  --sup_passive_queues_freq               [1;4]
% 4.00/0.98  --demod_completeness_check              fast
% 4.00/0.98  --demod_use_ground                      true
% 4.00/0.98  --sup_to_prop_solver                    passive
% 4.00/0.98  --sup_prop_simpl_new                    true
% 4.00/0.98  --sup_prop_simpl_given                  true
% 4.00/0.98  --sup_fun_splitting                     false
% 4.00/0.98  --sup_smt_interval                      50000
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Simplification Setup
% 4.00/0.98  
% 4.00/0.98  --sup_indices_passive                   []
% 4.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_full_bw                           [BwDemod]
% 4.00/0.98  --sup_immed_triv                        [TrivRules]
% 4.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_immed_bw_main                     []
% 4.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  
% 4.00/0.98  ------ Combination Options
% 4.00/0.98  
% 4.00/0.98  --comb_res_mult                         3
% 4.00/0.98  --comb_sup_mult                         2
% 4.00/0.98  --comb_inst_mult                        10
% 4.00/0.98  
% 4.00/0.98  ------ Debug Options
% 4.00/0.98  
% 4.00/0.98  --dbg_backtrace                         false
% 4.00/0.98  --dbg_dump_prop_clauses                 false
% 4.00/0.98  --dbg_dump_prop_clauses_file            -
% 4.00/0.98  --dbg_out_stat                          false
% 4.00/0.98  ------ Parsing...
% 4.00/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.98  ------ Proving...
% 4.00/0.98  ------ Problem Properties 
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  clauses                                 19
% 4.00/0.98  conjectures                             3
% 4.00/0.98  EPR                                     3
% 4.00/0.98  Horn                                    18
% 4.00/0.98  unary                                   7
% 4.00/0.98  binary                                  10
% 4.00/0.98  lits                                    33
% 4.00/0.98  lits eq                                 14
% 4.00/0.98  fd_pure                                 0
% 4.00/0.98  fd_pseudo                               0
% 4.00/0.98  fd_cond                                 3
% 4.00/0.98  fd_pseudo_cond                          0
% 4.00/0.98  AC symbols                              0
% 4.00/0.98  
% 4.00/0.98  ------ Input Options Time Limit: Unbounded
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  ------ 
% 4.00/0.98  Current options:
% 4.00/0.98  ------ 
% 4.00/0.98  
% 4.00/0.98  ------ Input Options
% 4.00/0.98  
% 4.00/0.98  --out_options                           all
% 4.00/0.98  --tptp_safe_out                         true
% 4.00/0.98  --problem_path                          ""
% 4.00/0.98  --include_path                          ""
% 4.00/0.98  --clausifier                            res/vclausify_rel
% 4.00/0.98  --clausifier_options                    --mode clausify
% 4.00/0.98  --stdin                                 false
% 4.00/0.98  --stats_out                             sel
% 4.00/0.98  
% 4.00/0.98  ------ General Options
% 4.00/0.98  
% 4.00/0.98  --fof                                   false
% 4.00/0.98  --time_out_real                         604.99
% 4.00/0.98  --time_out_virtual                      -1.
% 4.00/0.98  --symbol_type_check                     false
% 4.00/0.98  --clausify_out                          false
% 4.00/0.98  --sig_cnt_out                           false
% 4.00/0.98  --trig_cnt_out                          false
% 4.00/0.98  --trig_cnt_out_tolerance                1.
% 4.00/0.98  --trig_cnt_out_sk_spl                   false
% 4.00/0.98  --abstr_cl_out                          false
% 4.00/0.98  
% 4.00/0.98  ------ Global Options
% 4.00/0.98  
% 4.00/0.98  --schedule                              none
% 4.00/0.98  --add_important_lit                     false
% 4.00/0.98  --prop_solver_per_cl                    1000
% 4.00/0.98  --min_unsat_core                        false
% 4.00/0.98  --soft_assumptions                      false
% 4.00/0.98  --soft_lemma_size                       3
% 4.00/0.98  --prop_impl_unit_size                   0
% 4.00/0.98  --prop_impl_unit                        []
% 4.00/0.98  --share_sel_clauses                     true
% 4.00/0.98  --reset_solvers                         false
% 4.00/0.98  --bc_imp_inh                            [conj_cone]
% 4.00/0.98  --conj_cone_tolerance                   3.
% 4.00/0.98  --extra_neg_conj                        none
% 4.00/0.98  --large_theory_mode                     true
% 4.00/0.98  --prolific_symb_bound                   200
% 4.00/0.98  --lt_threshold                          2000
% 4.00/0.98  --clause_weak_htbl                      true
% 4.00/0.98  --gc_record_bc_elim                     false
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing Options
% 4.00/0.98  
% 4.00/0.98  --preprocessing_flag                    true
% 4.00/0.98  --time_out_prep_mult                    0.1
% 4.00/0.98  --splitting_mode                        input
% 4.00/0.98  --splitting_grd                         true
% 4.00/0.98  --splitting_cvd                         false
% 4.00/0.98  --splitting_cvd_svl                     false
% 4.00/0.98  --splitting_nvd                         32
% 4.00/0.98  --sub_typing                            true
% 4.00/0.98  --prep_gs_sim                           false
% 4.00/0.98  --prep_unflatten                        true
% 4.00/0.98  --prep_res_sim                          true
% 4.00/0.98  --prep_upred                            true
% 4.00/0.98  --prep_sem_filter                       exhaustive
% 4.00/0.98  --prep_sem_filter_out                   false
% 4.00/0.98  --pred_elim                             false
% 4.00/0.98  --res_sim_input                         true
% 4.00/0.98  --eq_ax_congr_red                       true
% 4.00/0.98  --pure_diseq_elim                       true
% 4.00/0.98  --brand_transform                       false
% 4.00/0.98  --non_eq_to_eq                          false
% 4.00/0.98  --prep_def_merge                        true
% 4.00/0.98  --prep_def_merge_prop_impl              false
% 4.00/0.98  --prep_def_merge_mbd                    true
% 4.00/0.98  --prep_def_merge_tr_red                 false
% 4.00/0.98  --prep_def_merge_tr_cl                  false
% 4.00/0.98  --smt_preprocessing                     true
% 4.00/0.98  --smt_ac_axioms                         fast
% 4.00/0.98  --preprocessed_out                      false
% 4.00/0.98  --preprocessed_stats                    false
% 4.00/0.98  
% 4.00/0.98  ------ Abstraction refinement Options
% 4.00/0.98  
% 4.00/0.98  --abstr_ref                             []
% 4.00/0.98  --abstr_ref_prep                        false
% 4.00/0.98  --abstr_ref_until_sat                   false
% 4.00/0.98  --abstr_ref_sig_restrict                funpre
% 4.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.98  --abstr_ref_under                       []
% 4.00/0.98  
% 4.00/0.98  ------ SAT Options
% 4.00/0.98  
% 4.00/0.98  --sat_mode                              false
% 4.00/0.98  --sat_fm_restart_options                ""
% 4.00/0.98  --sat_gr_def                            false
% 4.00/0.98  --sat_epr_types                         true
% 4.00/0.98  --sat_non_cyclic_types                  false
% 4.00/0.98  --sat_finite_models                     false
% 4.00/0.98  --sat_fm_lemmas                         false
% 4.00/0.98  --sat_fm_prep                           false
% 4.00/0.98  --sat_fm_uc_incr                        true
% 4.00/0.98  --sat_out_model                         small
% 4.00/0.98  --sat_out_clauses                       false
% 4.00/0.98  
% 4.00/0.98  ------ QBF Options
% 4.00/0.98  
% 4.00/0.98  --qbf_mode                              false
% 4.00/0.98  --qbf_elim_univ                         false
% 4.00/0.98  --qbf_dom_inst                          none
% 4.00/0.98  --qbf_dom_pre_inst                      false
% 4.00/0.98  --qbf_sk_in                             false
% 4.00/0.98  --qbf_pred_elim                         true
% 4.00/0.98  --qbf_split                             512
% 4.00/0.98  
% 4.00/0.98  ------ BMC1 Options
% 4.00/0.98  
% 4.00/0.98  --bmc1_incremental                      false
% 4.00/0.98  --bmc1_axioms                           reachable_all
% 4.00/0.98  --bmc1_min_bound                        0
% 4.00/0.98  --bmc1_max_bound                        -1
% 4.00/0.98  --bmc1_max_bound_default                -1
% 4.00/0.98  --bmc1_symbol_reachability              true
% 4.00/0.98  --bmc1_property_lemmas                  false
% 4.00/0.98  --bmc1_k_induction                      false
% 4.00/0.98  --bmc1_non_equiv_states                 false
% 4.00/0.98  --bmc1_deadlock                         false
% 4.00/0.98  --bmc1_ucm                              false
% 4.00/0.98  --bmc1_add_unsat_core                   none
% 4.00/0.98  --bmc1_unsat_core_children              false
% 4.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.98  --bmc1_out_stat                         full
% 4.00/0.98  --bmc1_ground_init                      false
% 4.00/0.98  --bmc1_pre_inst_next_state              false
% 4.00/0.98  --bmc1_pre_inst_state                   false
% 4.00/0.98  --bmc1_pre_inst_reach_state             false
% 4.00/0.98  --bmc1_out_unsat_core                   false
% 4.00/0.98  --bmc1_aig_witness_out                  false
% 4.00/0.98  --bmc1_verbose                          false
% 4.00/0.98  --bmc1_dump_clauses_tptp                false
% 4.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.98  --bmc1_dump_file                        -
% 4.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.98  --bmc1_ucm_extend_mode                  1
% 4.00/0.98  --bmc1_ucm_init_mode                    2
% 4.00/0.98  --bmc1_ucm_cone_mode                    none
% 4.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.98  --bmc1_ucm_relax_model                  4
% 4.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.98  --bmc1_ucm_layered_model                none
% 4.00/0.98  --bmc1_ucm_max_lemma_size               10
% 4.00/0.98  
% 4.00/0.98  ------ AIG Options
% 4.00/0.98  
% 4.00/0.98  --aig_mode                              false
% 4.00/0.98  
% 4.00/0.98  ------ Instantiation Options
% 4.00/0.98  
% 4.00/0.98  --instantiation_flag                    true
% 4.00/0.98  --inst_sos_flag                         false
% 4.00/0.98  --inst_sos_phase                        true
% 4.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel_side                     num_symb
% 4.00/0.98  --inst_solver_per_active                1400
% 4.00/0.98  --inst_solver_calls_frac                1.
% 4.00/0.98  --inst_passive_queue_type               priority_queues
% 4.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.98  --inst_passive_queues_freq              [25;2]
% 4.00/0.98  --inst_dismatching                      true
% 4.00/0.98  --inst_eager_unprocessed_to_passive     true
% 4.00/0.98  --inst_prop_sim_given                   true
% 4.00/0.98  --inst_prop_sim_new                     false
% 4.00/0.98  --inst_subs_new                         false
% 4.00/0.98  --inst_eq_res_simp                      false
% 4.00/0.98  --inst_subs_given                       false
% 4.00/0.98  --inst_orphan_elimination               true
% 4.00/0.98  --inst_learning_loop_flag               true
% 4.00/0.98  --inst_learning_start                   3000
% 4.00/0.98  --inst_learning_factor                  2
% 4.00/0.98  --inst_start_prop_sim_after_learn       3
% 4.00/0.98  --inst_sel_renew                        solver
% 4.00/0.98  --inst_lit_activity_flag                true
% 4.00/0.98  --inst_restr_to_given                   false
% 4.00/0.98  --inst_activity_threshold               500
% 4.00/0.98  --inst_out_proof                        true
% 4.00/0.98  
% 4.00/0.98  ------ Resolution Options
% 4.00/0.98  
% 4.00/0.98  --resolution_flag                       true
% 4.00/0.98  --res_lit_sel                           adaptive
% 4.00/0.98  --res_lit_sel_side                      none
% 4.00/0.98  --res_ordering                          kbo
% 4.00/0.98  --res_to_prop_solver                    active
% 4.00/0.98  --res_prop_simpl_new                    false
% 4.00/0.98  --res_prop_simpl_given                  true
% 4.00/0.98  --res_passive_queue_type                priority_queues
% 4.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.98  --res_passive_queues_freq               [15;5]
% 4.00/0.98  --res_forward_subs                      full
% 4.00/0.98  --res_backward_subs                     full
% 4.00/0.98  --res_forward_subs_resolution           true
% 4.00/0.98  --res_backward_subs_resolution          true
% 4.00/0.98  --res_orphan_elimination                true
% 4.00/0.98  --res_time_limit                        2.
% 4.00/0.98  --res_out_proof                         true
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Options
% 4.00/0.98  
% 4.00/0.98  --superposition_flag                    true
% 4.00/0.98  --sup_passive_queue_type                priority_queues
% 4.00/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.98  --sup_passive_queues_freq               [1;4]
% 4.00/0.98  --demod_completeness_check              fast
% 4.00/0.98  --demod_use_ground                      true
% 4.00/0.98  --sup_to_prop_solver                    passive
% 4.00/0.98  --sup_prop_simpl_new                    true
% 4.00/0.98  --sup_prop_simpl_given                  true
% 4.00/0.98  --sup_fun_splitting                     false
% 4.00/0.98  --sup_smt_interval                      50000
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Simplification Setup
% 4.00/0.98  
% 4.00/0.98  --sup_indices_passive                   []
% 4.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_full_bw                           [BwDemod]
% 4.00/0.98  --sup_immed_triv                        [TrivRules]
% 4.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_immed_bw_main                     []
% 4.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  
% 4.00/0.98  ------ Combination Options
% 4.00/0.98  
% 4.00/0.98  --comb_res_mult                         3
% 4.00/0.98  --comb_sup_mult                         2
% 4.00/0.98  --comb_inst_mult                        10
% 4.00/0.98  
% 4.00/0.98  ------ Debug Options
% 4.00/0.98  
% 4.00/0.98  --dbg_backtrace                         false
% 4.00/0.98  --dbg_dump_prop_clauses                 false
% 4.00/0.98  --dbg_dump_prop_clauses_file            -
% 4.00/0.98  --dbg_out_stat                          false
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  ------ Proving...
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  % SZS status Theorem for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  fof(f15,conjecture,(
% 4.00/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f16,negated_conjecture,(
% 4.00/0.98    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 4.00/0.98    inference(negated_conjecture,[],[f15])).
% 4.00/0.98  
% 4.00/0.98  fof(f24,plain,(
% 4.00/0.98    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 4.00/0.98    inference(ennf_transformation,[],[f16])).
% 4.00/0.98  
% 4.00/0.98  fof(f26,plain,(
% 4.00/0.98    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 4.00/0.98    inference(nnf_transformation,[],[f24])).
% 4.00/0.98  
% 4.00/0.98  fof(f27,plain,(
% 4.00/0.98    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 4.00/0.98    inference(flattening,[],[f26])).
% 4.00/0.98  
% 4.00/0.98  fof(f28,plain,(
% 4.00/0.98    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 4.00/0.98    introduced(choice_axiom,[])).
% 4.00/0.98  
% 4.00/0.98  fof(f29,plain,(
% 4.00/0.98    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 4.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 4.00/0.98  
% 4.00/0.98  fof(f50,plain,(
% 4.00/0.98    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 4.00/0.98    inference(cnf_transformation,[],[f29])).
% 4.00/0.98  
% 4.00/0.98  fof(f6,axiom,(
% 4.00/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f25,plain,(
% 4.00/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 4.00/0.98    inference(nnf_transformation,[],[f6])).
% 4.00/0.98  
% 4.00/0.98  fof(f37,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f25])).
% 4.00/0.98  
% 4.00/0.98  fof(f5,axiom,(
% 4.00/0.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f36,plain,(
% 4.00/0.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f5])).
% 4.00/0.98  
% 4.00/0.98  fof(f49,plain,(
% 4.00/0.98    v1_relat_1(sK1)),
% 4.00/0.98    inference(cnf_transformation,[],[f29])).
% 4.00/0.98  
% 4.00/0.98  fof(f51,plain,(
% 4.00/0.98    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 4.00/0.98    inference(cnf_transformation,[],[f29])).
% 4.00/0.98  
% 4.00/0.98  fof(f10,axiom,(
% 4.00/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f19,plain,(
% 4.00/0.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.00/0.98    inference(ennf_transformation,[],[f10])).
% 4.00/0.98  
% 4.00/0.98  fof(f42,plain,(
% 4.00/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f19])).
% 4.00/0.98  
% 4.00/0.98  fof(f38,plain,(
% 4.00/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 4.00/0.98    inference(cnf_transformation,[],[f25])).
% 4.00/0.98  
% 4.00/0.98  fof(f14,axiom,(
% 4.00/0.98    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f23,plain,(
% 4.00/0.98    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 4.00/0.98    inference(ennf_transformation,[],[f14])).
% 4.00/0.98  
% 4.00/0.98  fof(f48,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f3,axiom,(
% 4.00/0.98    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f33,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f3])).
% 4.00/0.98  
% 4.00/0.98  fof(f54,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.00/0.98    inference(definition_unfolding,[],[f48,f33])).
% 4.00/0.98  
% 4.00/0.98  fof(f4,axiom,(
% 4.00/0.98    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f18,plain,(
% 4.00/0.98    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 4.00/0.98    inference(ennf_transformation,[],[f4])).
% 4.00/0.98  
% 4.00/0.98  fof(f35,plain,(
% 4.00/0.98    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 4.00/0.98    inference(cnf_transformation,[],[f18])).
% 4.00/0.98  
% 4.00/0.98  fof(f12,axiom,(
% 4.00/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f20,plain,(
% 4.00/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.00/0.98    inference(ennf_transformation,[],[f12])).
% 4.00/0.98  
% 4.00/0.98  fof(f21,plain,(
% 4.00/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.00/0.98    inference(flattening,[],[f20])).
% 4.00/0.98  
% 4.00/0.98  fof(f45,plain,(
% 4.00/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f21])).
% 4.00/0.98  
% 4.00/0.98  fof(f11,axiom,(
% 4.00/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f43,plain,(
% 4.00/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.00/0.98    inference(cnf_transformation,[],[f11])).
% 4.00/0.98  
% 4.00/0.98  fof(f2,axiom,(
% 4.00/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f32,plain,(
% 4.00/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.00/0.98    inference(cnf_transformation,[],[f2])).
% 4.00/0.98  
% 4.00/0.98  fof(f13,axiom,(
% 4.00/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f22,plain,(
% 4.00/0.98    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 4.00/0.98    inference(ennf_transformation,[],[f13])).
% 4.00/0.98  
% 4.00/0.98  fof(f47,plain,(
% 4.00/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f22])).
% 4.00/0.98  
% 4.00/0.98  fof(f1,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f17,plain,(
% 4.00/0.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 4.00/0.98    inference(ennf_transformation,[],[f1])).
% 4.00/0.98  
% 4.00/0.98  fof(f31,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f17])).
% 4.00/0.98  
% 4.00/0.98  fof(f34,plain,(
% 4.00/0.98    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f18])).
% 4.00/0.98  
% 4.00/0.98  fof(f55,plain,(
% 4.00/0.98    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 4.00/0.98    inference(equality_resolution,[],[f34])).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17,negated_conjecture,
% 4.00/0.98      ( r1_xboole_0(k1_relat_1(sK1),sK0)
% 4.00/0.98      | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_574,plain,
% 4.00/0.98      ( k1_xboole_0 = k7_relat_1(sK1,sK0)
% 4.00/0.98      | r1_xboole_0(k1_relat_1(sK1),sK0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_7,plain,
% 4.00/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f37]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_581,plain,
% 4.00/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1380,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 4.00/0.98      | k4_xboole_0(k1_relat_1(sK1),sK0) = k1_relat_1(sK1) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_574,c_581]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5,plain,
% 4.00/0.98      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f36]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_583,plain,
% 4.00/0.98      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1379,plain,
% 4.00/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_583,c_581]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2656,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 4.00/0.98      | k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(sK0,k1_relat_1(sK1))) = k4_xboole_0(k1_relat_1(sK1),sK0) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1380,c_1379]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_18,negated_conjecture,
% 4.00/0.98      ( v1_relat_1(sK1) ),
% 4.00/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16,negated_conjecture,
% 4.00/0.98      ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
% 4.00/0.98      | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f51]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_21,plain,
% 4.00/0.98      ( k1_xboole_0 != k7_relat_1(sK1,sK0)
% 4.00/0.98      | r1_xboole_0(k1_relat_1(sK1),sK0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_9,plain,
% 4.00/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_703,plain,
% 4.00/0.98      ( v1_relat_1(k7_relat_1(sK1,X0)) | ~ v1_relat_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2128,plain,
% 4.00/0.98      ( v1_relat_1(k7_relat_1(sK1,sK0)) | ~ v1_relat_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_703]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6,plain,
% 4.00/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f38]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_582,plain,
% 4.00/0.98      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2302,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 4.00/0.98      | r1_xboole_0(k1_relat_1(sK1),sK0) = iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1380,c_582]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_573,plain,
% 4.00/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_15,plain,
% 4.00/0.98      ( ~ v1_relat_1(X0)
% 4.00/0.98      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f54]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_576,plain,
% 4.00/0.98      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 4.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1497,plain,
% 4.00/0.98      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_573,c_576]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2710,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 4.00/0.98      | k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1380,c_1497]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3,plain,
% 4.00/0.98      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f35]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_585,plain,
% 4.00/0.98      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1181,plain,
% 4.00/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_583,c_585]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2753,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 4.00/0.98      | k1_relat_1(k7_relat_1(sK1,sK0)) = k1_xboole_0 ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_2710,c_1181]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13,plain,
% 4.00/0.98      ( ~ v1_relat_1(X0)
% 4.00/0.98      | k1_relat_1(X0) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1010,plain,
% 4.00/0.98      ( ~ v1_relat_1(k7_relat_1(sK1,X0))
% 4.00/0.98      | k1_relat_1(k7_relat_1(sK1,X0)) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = k7_relat_1(sK1,X0) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5957,plain,
% 4.00/0.98      ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
% 4.00/0.98      | k1_relat_1(k7_relat_1(sK1,sK0)) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1010]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_7624,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) = k1_xboole_0 ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_2656,c_18,c_21,c_2128,c_2302,c_2753,c_5957]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2721,plain,
% 4.00/0.98      ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0))) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1497,c_1497]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10787,plain,
% 4.00/0.98      ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),sK0))) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k1_xboole_0)) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_7624,c_2721]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11,plain,
% 4.00/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f43]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10841,plain,
% 4.00/0.98      ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),sK0))) = k4_xboole_0(k1_relat_1(sK1),k1_xboole_0) ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_10787,c_11]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2,plain,
% 4.00/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f32]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10842,plain,
% 4.00/0.98      ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),sK0))) = k1_relat_1(sK1) ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_10841,c_2]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_14,plain,
% 4.00/0.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f47]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_577,plain,
% 4.00/0.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 4.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_0,plain,
% 4.00/0.98      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 4.00/0.98      inference(cnf_transformation,[],[f31]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_587,plain,
% 4.00/0.98      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 4.00/0.98      | r1_xboole_0(X0,X2) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1804,plain,
% 4.00/0.98      ( r1_xboole_0(k1_relat_1(k7_relat_1(X0,k4_xboole_0(X1,X2))),X2) = iProver_top
% 4.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_577,c_587]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11134,plain,
% 4.00/0.98      ( r1_xboole_0(k1_relat_1(sK1),sK0) = iProver_top
% 4.00/0.98      | v1_relat_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_10842,c_1804]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_192,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_191,plain,( X0 = X0 ),theory(equality) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2236,plain,
% 4.00/0.98      ( X0 != X1 | X1 = X0 ),
% 4.00/0.98      inference(resolution,[status(thm)],[c_192,c_191]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4677,plain,
% 4.00/0.98      ( r1_xboole_0(k1_relat_1(sK1),sK0)
% 4.00/0.98      | k7_relat_1(sK1,sK0) = k1_xboole_0 ),
% 4.00/0.98      inference(resolution,[status(thm)],[c_2236,c_17]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5185,plain,
% 4.00/0.98      ( r1_xboole_0(k1_relat_1(sK1),sK0)
% 4.00/0.98      | X0 != k1_xboole_0
% 4.00/0.98      | k7_relat_1(sK1,sK0) = X0 ),
% 4.00/0.98      inference(resolution,[status(thm)],[c_4677,c_192]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2234,plain,
% 4.00/0.98      ( r1_xboole_0(k1_relat_1(sK1),sK0)
% 4.00/0.98      | X0 != k7_relat_1(sK1,sK0)
% 4.00/0.98      | k1_xboole_0 = X0 ),
% 4.00/0.98      inference(resolution,[status(thm)],[c_192,c_17]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5420,plain,
% 4.00/0.98      ( r1_xboole_0(k1_relat_1(sK1),sK0)
% 4.00/0.98      | k7_relat_1(sK1,sK0) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
% 4.00/0.98      inference(resolution,[status(thm)],[c_5185,c_2234]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4,plain,
% 4.00/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_49,plain,
% 4.00/0.98      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 4.00/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1035,plain,
% 4.00/0.98      ( X0 != X1 | X0 = k7_relat_1(sK1,X2) | k7_relat_1(sK1,X2) != X1 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_192]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5525,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) != X0
% 4.00/0.98      | k1_xboole_0 != X0
% 4.00/0.98      | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1035]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5526,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = k7_relat_1(sK1,sK0)
% 4.00/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_5525]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5738,plain,
% 4.00/0.98      ( k7_relat_1(sK1,sK0) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_5420,c_4,c_49,c_5526]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_19,plain,
% 4.00/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(contradiction,plain,
% 4.00/0.98      ( $false ),
% 4.00/0.98      inference(minisat,[status(thm)],[c_11134,c_7624,c_5738,c_21,c_19]) ).
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  ------                               Statistics
% 4.00/0.98  
% 4.00/0.98  ------ Selected
% 4.00/0.98  
% 4.00/0.98  total_time:                             0.316
% 4.00/0.98  
%------------------------------------------------------------------------------
