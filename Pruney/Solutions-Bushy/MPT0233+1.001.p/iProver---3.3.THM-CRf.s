%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0233+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:47 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of clauses        :   22 (  23 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :   18
%              Number of atoms          :  137 ( 181 expanded)
%              Number of equality atoms :  113 ( 145 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).

fof(f27,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f20,f17])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( X0 = X3
      | X0 = X2
      | k2_tarski(X0,X1) != k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X0 = X2
      | k2_tarski(X0,X1) != k2_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_389,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k1_tarski(X2) = X0
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_390,plain,
    ( k2_tarski(X0,X1) = X2
    | k1_tarski(X1) = X2
    | k1_tarski(X0) = X2
    | o_0_0_xboole_0 = X2
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_846,plain,
    ( k2_tarski(sK2,sK3) = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | k2_tarski(sK0,sK1) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_389,c_390])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_94,plain,
    ( k2_tarski(X0,X1) != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_939,plain,
    ( k2_tarski(sK2,sK3) = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_846,c_94])).

cnf(c_7,plain,
    ( X0 = X1
    | X2 = X1
    | k2_tarski(X0,X2) != k2_tarski(X1,X3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_947,plain,
    ( k2_tarski(X0,X1) != k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK2 = X0
    | sK3 = X0 ),
    inference(superposition,[status(thm)],[c_939,c_7])).

cnf(c_1215,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK2 = sK0
    | sK3 = sK0 ),
    inference(equality_resolution,[status(thm)],[c_947])).

cnf(c_8,plain,
    ( X0 = X1
    | k2_tarski(X0,X2) != k1_tarski(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1498,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | k1_tarski(X0) != k1_tarski(sK2)
    | sK2 = sK0
    | sK3 = sK0
    | sK0 = X0 ),
    inference(superposition,[status(thm)],[c_1215,c_8])).

cnf(c_2185,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK2 = sK0
    | sK3 = sK0 ),
    inference(equality_resolution,[status(thm)],[c_1498])).

cnf(c_9855,plain,
    ( k1_tarski(X0) != k1_tarski(sK3)
    | sK2 = sK0
    | sK3 = sK0
    | sK0 = X0 ),
    inference(superposition,[status(thm)],[c_2185,c_8])).

cnf(c_9960,plain,
    ( sK2 = sK0
    | sK3 = sK0 ),
    inference(equality_resolution,[status(thm)],[c_9855])).

cnf(c_10,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16945,plain,
    ( sK3 = sK0 ),
    inference(superposition,[status(thm)],[c_9960,c_10])).

cnf(c_9,negated_conjecture,
    ( sK0 != sK3 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17230,plain,
    ( sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_16945,c_9])).

cnf(c_17231,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_17230])).


%------------------------------------------------------------------------------
