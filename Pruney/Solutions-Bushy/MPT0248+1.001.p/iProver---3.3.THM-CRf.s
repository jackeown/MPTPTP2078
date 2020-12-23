%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0248+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:49 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 171 expanded)
%              Number of clauses        :   23 (  57 expanded)
%              Number of leaves         :    6 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 790 expanded)
%              Number of equality atoms :  103 ( 739 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | k1_tarski(sK0) != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_xboole_0 != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_tarski(sK0) != sK1 )
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ( k1_xboole_0 != sK2
      | k1_tarski(sK0) != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_xboole_0 != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_tarski(sK0) != sK1 )
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f18,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f8])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f20,plain,
    ( k1_tarski(sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,
    ( k1_tarski(sK0) != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,
    ( k1_xboole_0 != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_216,plain,
    ( k2_xboole_0(sK2,sK1) = k1_tarski(sK0) ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_62,plain,
    ( X0 != X1
    | k2_xboole_0(X0,X2) != k1_tarski(X3)
    | k1_tarski(X3) = X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_63,plain,
    ( k2_xboole_0(X0,X1) != k1_tarski(X2)
    | k1_tarski(X2) = X0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_62])).

cnf(c_258,plain,
    ( k1_tarski(X0) != k1_tarski(sK0)
    | k1_tarski(X0) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_216,c_63])).

cnf(c_429,plain,
    ( k1_tarski(sK0) = sK2
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_258])).

cnf(c_7,negated_conjecture,
    ( k1_tarski(sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,negated_conjecture,
    ( k1_tarski(sK0) != sK1
    | k1_tarski(sK0) != sK2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_113,plain,
    ( k2_xboole_0(sK1,X0) != k1_tarski(X1)
    | k1_tarski(X1) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_132,plain,
    ( k2_xboole_0(sK1,sK2) != k1_tarski(sK0)
    | k1_tarski(sK0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_137,negated_conjecture,
    ( k1_tarski(sK0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_9,c_8,c_132])).

cnf(c_474,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_9,c_8,c_7,c_132])).

cnf(c_6,negated_conjecture,
    ( k1_tarski(sK0) != sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_482,plain,
    ( k1_tarski(sK0) != sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_474,c_6])).

cnf(c_487,plain,
    ( k1_tarski(sK0) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_482])).

cnf(c_483,plain,
    ( k2_xboole_0(sK1,k1_xboole_0) = k1_tarski(sK0) ),
    inference(demodulation,[status(thm)],[c_474,c_9])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_485,plain,
    ( k1_tarski(sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_483,c_4])).

cnf(c_488,plain,
    ( sK1 != sK1 ),
    inference(light_normalisation,[status(thm)],[c_487,c_485])).

cnf(c_489,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_488])).


%------------------------------------------------------------------------------
