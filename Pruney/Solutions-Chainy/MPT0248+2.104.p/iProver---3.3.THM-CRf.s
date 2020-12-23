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
% DateTime   : Thu Dec  3 11:32:24 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 882 expanded)
%              Number of clauses        :   93 ( 200 expanded)
%              Number of leaves         :   23 ( 251 expanded)
%              Depth                    :   16
%              Number of atoms          :  393 (2478 expanded)
%              Number of equality atoms :  274 (2159 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK5
        | k1_tarski(sK3) != sK4 )
      & ( k1_tarski(sK3) != sK5
        | k1_xboole_0 != sK4 )
      & ( k1_tarski(sK3) != sK5
        | k1_tarski(sK3) != sK4 )
      & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( k1_xboole_0 != sK5
      | k1_tarski(sK3) != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_xboole_0 != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_tarski(sK3) != sK4 )
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f58])).

fof(f101,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f85,f86])).

fof(f125,plain,(
    k2_xboole_0(sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f101,f105])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f96,f86,f105,f105,f86])).

fof(f104,plain,
    ( k1_xboole_0 != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f59])).

fof(f122,plain,
    ( k1_xboole_0 != sK5
    | k2_enumset1(sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f104,f105])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f97,f86])).

fof(f136,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f120])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f93,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f115,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f93,f105,f105,f105])).

fof(f132,plain,(
    ! [X1] : k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f115])).

fof(f23,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f116,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f95,f105,f86])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,
    ( k1_tarski(sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f59])).

fof(f123,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f103,f105])).

fof(f102,plain,
    ( k1_tarski(sK3) != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f59])).

fof(f124,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK5
    | k2_enumset1(sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f102,f105,f105])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1060,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,X3)
    | X2 = X1
    | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1059,plain,
    ( X0 = X1
    | k2_xboole_0(X0,X2) != k2_xboole_0(X3,X1)
    | r1_xboole_0(X2,X1) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2320,plain,
    ( X0 = X1
    | k2_xboole_0(X2,X0) != X1
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1059])).

cnf(c_17,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1058,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1704,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1058])).

cnf(c_4530,plain,
    ( r1_xboole_0(X1,X2) != iProver_top
    | k2_xboole_0(X2,X0) != X1
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2320,c_1704])).

cnf(c_4531,plain,
    ( X0 = X1
    | k2_xboole_0(X2,X0) != X1
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4530])).

cnf(c_4538,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_xboole_0(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4531])).

cnf(c_30510,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1060,c_4538])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1063,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1055,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1062,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2612,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1062])).

cnf(c_6910,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1063,c_2612])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1061,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7526,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6910,c_1061])).

cnf(c_41,negated_conjecture,
    ( k2_xboole_0(sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_37,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1050,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k2_enumset1(X0,X0,X0,X2) = X1
    | k2_enumset1(X2,X2,X2,X2) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1329,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_1050])).

cnf(c_1330,plain,
    ( k2_xboole_0(sK4,sK5) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1329,c_41])).

cnf(c_9187,plain,
    ( k2_xboole_0(k1_xboole_0,sK5) = k2_xboole_0(sK4,sK5)
    | k2_xboole_0(k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7526,c_1330])).

cnf(c_30595,plain,
    ( k2_xboole_0(sK4,sK5) = sK5
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30510,c_9187])).

cnf(c_509,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1295,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_28520,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_512,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3290,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))
    | ~ r1_xboole_0(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_512,c_17])).

cnf(c_14466,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))
    | X0 != X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3290,c_18])).

cnf(c_38,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_5931,plain,
    ( ~ r1_tarski(sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(sK3,sK3,sK3,sK3) = sK4
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(resolution,[status(thm)],[c_37,c_38])).

cnf(c_36,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_46,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_1106,plain,
    ( k2_xboole_0(sK4,sK5) != sK4
    | sK5 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_38,c_41])).

cnf(c_31,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_32,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1156,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31,c_32])).

cnf(c_1216,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_1405,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1))
    | k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_1407,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_1299,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_2258,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_2263,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | k4_xboole_0(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1501,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2709,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_2710,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_21,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1057,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3084,plain,
    ( k2_xboole_0(sK4,sK5) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1057,c_1330])).

cnf(c_2550,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) != X0
    | k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_5563,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) != sK5
    | k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2550])).

cnf(c_16,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5564,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = sK5 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6436,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5931,c_46,c_1106,c_1216,c_1407,c_2258,c_2263,c_2709,c_2710,c_3084,c_5563,c_5564])).

cnf(c_14511,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | k1_xboole_0 != sK5 ),
    inference(resolution,[status(thm)],[c_14466,c_6436])).

cnf(c_1740,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | k4_xboole_0(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2435,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) != X0
    | k4_xboole_0(sK4,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_5388,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) != sK4
    | k4_xboole_0(sK4,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_5389,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = sK4 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_510,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3206,plain,
    ( r1_tarski(X0,k4_xboole_0(k1_xboole_0,X1))
    | ~ r1_tarski(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_510,c_17])).

cnf(c_11536,plain,
    ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0)
    | r1_tarski(k2_xboole_0(sK4,sK5),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[status(thm)],[c_3206,c_41])).

cnf(c_508,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3218,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_510,c_508])).

cnf(c_8071,plain,
    ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0)
    | r1_tarski(k2_xboole_0(sK4,sK5),X0) ),
    inference(resolution,[status(thm)],[c_3218,c_41])).

cnf(c_3214,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r1_tarski(X1,k2_xboole_0(sK4,sK5))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_510,c_41])).

cnf(c_3517,plain,
    ( r1_tarski(X0,k2_xboole_0(sK4,sK5))
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3214,c_13])).

cnf(c_8415,plain,
    ( r1_tarski(k2_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))
    | k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8071,c_3517])).

cnf(c_10591,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8415,c_1216])).

cnf(c_10597,plain,
    ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_10591,c_8])).

cnf(c_12541,plain,
    ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11536,c_46,c_10597])).

cnf(c_2876,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_509,c_508])).

cnf(c_5996,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_2876,c_41])).

cnf(c_8080,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0)
    | ~ r1_tarski(k2_xboole_0(sK4,sK5),X0) ),
    inference(resolution,[status(thm)],[c_3218,c_5996])).

cnf(c_12553,plain,
    ( ~ r1_tarski(k2_xboole_0(sK4,sK5),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12541,c_8080])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_13261,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(sK5,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12553,c_22])).

cnf(c_14901,plain,
    ( k1_xboole_0 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14511,c_1740,c_2263,c_5388,c_5389,c_5563,c_5564,c_6436,c_13261])).

cnf(c_39,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1101,plain,
    ( k2_xboole_0(sK4,sK5) != sK5
    | sK4 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_39,c_41])).

cnf(c_40,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK4
    | k2_enumset1(sK3,sK3,sK3,sK3) != sK5 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1137,plain,
    ( k2_xboole_0(sK4,sK5) != sK4
    | k2_xboole_0(sK4,sK5) != sK5 ),
    inference(light_normalisation,[status(thm)],[c_40,c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30595,c_28520,c_14901,c_3084,c_1407,c_1101,c_1216,c_1137,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:17:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.00/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.00/1.50  
% 8.00/1.50  ------  iProver source info
% 8.00/1.50  
% 8.00/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.00/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.00/1.50  git: non_committed_changes: false
% 8.00/1.50  git: last_make_outside_of_git: false
% 8.00/1.50  
% 8.00/1.50  ------ 
% 8.00/1.50  
% 8.00/1.50  ------ Input Options
% 8.00/1.50  
% 8.00/1.50  --out_options                           all
% 8.00/1.50  --tptp_safe_out                         true
% 8.00/1.50  --problem_path                          ""
% 8.00/1.50  --include_path                          ""
% 8.00/1.50  --clausifier                            res/vclausify_rel
% 8.00/1.50  --clausifier_options                    --mode clausify
% 8.00/1.50  --stdin                                 false
% 8.00/1.50  --stats_out                             sel
% 8.00/1.50  
% 8.00/1.50  ------ General Options
% 8.00/1.50  
% 8.00/1.50  --fof                                   false
% 8.00/1.50  --time_out_real                         604.99
% 8.00/1.50  --time_out_virtual                      -1.
% 8.00/1.50  --symbol_type_check                     false
% 8.00/1.50  --clausify_out                          false
% 8.00/1.50  --sig_cnt_out                           false
% 8.00/1.50  --trig_cnt_out                          false
% 8.00/1.50  --trig_cnt_out_tolerance                1.
% 8.00/1.50  --trig_cnt_out_sk_spl                   false
% 8.00/1.50  --abstr_cl_out                          false
% 8.00/1.50  
% 8.00/1.50  ------ Global Options
% 8.00/1.50  
% 8.00/1.50  --schedule                              none
% 8.00/1.50  --add_important_lit                     false
% 8.00/1.50  --prop_solver_per_cl                    1000
% 8.00/1.50  --min_unsat_core                        false
% 8.00/1.50  --soft_assumptions                      false
% 8.00/1.50  --soft_lemma_size                       3
% 8.00/1.50  --prop_impl_unit_size                   0
% 8.00/1.50  --prop_impl_unit                        []
% 8.00/1.50  --share_sel_clauses                     true
% 8.00/1.50  --reset_solvers                         false
% 8.00/1.50  --bc_imp_inh                            [conj_cone]
% 8.00/1.50  --conj_cone_tolerance                   3.
% 8.00/1.50  --extra_neg_conj                        none
% 8.00/1.50  --large_theory_mode                     true
% 8.00/1.50  --prolific_symb_bound                   200
% 8.00/1.50  --lt_threshold                          2000
% 8.00/1.50  --clause_weak_htbl                      true
% 8.00/1.50  --gc_record_bc_elim                     false
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing Options
% 8.00/1.50  
% 8.00/1.50  --preprocessing_flag                    true
% 8.00/1.50  --time_out_prep_mult                    0.1
% 8.00/1.50  --splitting_mode                        input
% 8.00/1.50  --splitting_grd                         true
% 8.00/1.50  --splitting_cvd                         false
% 8.00/1.50  --splitting_cvd_svl                     false
% 8.00/1.50  --splitting_nvd                         32
% 8.00/1.50  --sub_typing                            true
% 8.00/1.50  --prep_gs_sim                           false
% 8.00/1.50  --prep_unflatten                        true
% 8.00/1.50  --prep_res_sim                          true
% 8.00/1.50  --prep_upred                            true
% 8.00/1.50  --prep_sem_filter                       exhaustive
% 8.00/1.50  --prep_sem_filter_out                   false
% 8.00/1.50  --pred_elim                             false
% 8.00/1.50  --res_sim_input                         true
% 8.00/1.50  --eq_ax_congr_red                       true
% 8.00/1.50  --pure_diseq_elim                       true
% 8.00/1.50  --brand_transform                       false
% 8.00/1.50  --non_eq_to_eq                          false
% 8.00/1.50  --prep_def_merge                        true
% 8.00/1.50  --prep_def_merge_prop_impl              false
% 8.00/1.50  --prep_def_merge_mbd                    true
% 8.00/1.50  --prep_def_merge_tr_red                 false
% 8.00/1.50  --prep_def_merge_tr_cl                  false
% 8.00/1.50  --smt_preprocessing                     true
% 8.00/1.50  --smt_ac_axioms                         fast
% 8.00/1.50  --preprocessed_out                      false
% 8.00/1.50  --preprocessed_stats                    false
% 8.00/1.50  
% 8.00/1.50  ------ Abstraction refinement Options
% 8.00/1.50  
% 8.00/1.50  --abstr_ref                             []
% 8.00/1.50  --abstr_ref_prep                        false
% 8.00/1.50  --abstr_ref_until_sat                   false
% 8.00/1.50  --abstr_ref_sig_restrict                funpre
% 8.00/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.50  --abstr_ref_under                       []
% 8.00/1.50  
% 8.00/1.50  ------ SAT Options
% 8.00/1.50  
% 8.00/1.50  --sat_mode                              false
% 8.00/1.50  --sat_fm_restart_options                ""
% 8.00/1.50  --sat_gr_def                            false
% 8.00/1.50  --sat_epr_types                         true
% 8.00/1.50  --sat_non_cyclic_types                  false
% 8.00/1.50  --sat_finite_models                     false
% 8.00/1.50  --sat_fm_lemmas                         false
% 8.00/1.50  --sat_fm_prep                           false
% 8.00/1.50  --sat_fm_uc_incr                        true
% 8.00/1.50  --sat_out_model                         small
% 8.00/1.50  --sat_out_clauses                       false
% 8.00/1.50  
% 8.00/1.50  ------ QBF Options
% 8.00/1.50  
% 8.00/1.50  --qbf_mode                              false
% 8.00/1.50  --qbf_elim_univ                         false
% 8.00/1.50  --qbf_dom_inst                          none
% 8.00/1.50  --qbf_dom_pre_inst                      false
% 8.00/1.50  --qbf_sk_in                             false
% 8.00/1.50  --qbf_pred_elim                         true
% 8.00/1.50  --qbf_split                             512
% 8.00/1.50  
% 8.00/1.50  ------ BMC1 Options
% 8.00/1.50  
% 8.00/1.50  --bmc1_incremental                      false
% 8.00/1.50  --bmc1_axioms                           reachable_all
% 8.00/1.50  --bmc1_min_bound                        0
% 8.00/1.50  --bmc1_max_bound                        -1
% 8.00/1.50  --bmc1_max_bound_default                -1
% 8.00/1.50  --bmc1_symbol_reachability              true
% 8.00/1.50  --bmc1_property_lemmas                  false
% 8.00/1.50  --bmc1_k_induction                      false
% 8.00/1.50  --bmc1_non_equiv_states                 false
% 8.00/1.50  --bmc1_deadlock                         false
% 8.00/1.50  --bmc1_ucm                              false
% 8.00/1.50  --bmc1_add_unsat_core                   none
% 8.00/1.50  --bmc1_unsat_core_children              false
% 8.00/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.50  --bmc1_out_stat                         full
% 8.00/1.50  --bmc1_ground_init                      false
% 8.00/1.50  --bmc1_pre_inst_next_state              false
% 8.00/1.50  --bmc1_pre_inst_state                   false
% 8.00/1.50  --bmc1_pre_inst_reach_state             false
% 8.00/1.50  --bmc1_out_unsat_core                   false
% 8.00/1.50  --bmc1_aig_witness_out                  false
% 8.00/1.50  --bmc1_verbose                          false
% 8.00/1.50  --bmc1_dump_clauses_tptp                false
% 8.00/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.50  --bmc1_dump_file                        -
% 8.00/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.50  --bmc1_ucm_extend_mode                  1
% 8.00/1.50  --bmc1_ucm_init_mode                    2
% 8.00/1.50  --bmc1_ucm_cone_mode                    none
% 8.00/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.50  --bmc1_ucm_relax_model                  4
% 8.00/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.50  --bmc1_ucm_layered_model                none
% 8.00/1.50  --bmc1_ucm_max_lemma_size               10
% 8.00/1.50  
% 8.00/1.50  ------ AIG Options
% 8.00/1.50  
% 8.00/1.50  --aig_mode                              false
% 8.00/1.50  
% 8.00/1.50  ------ Instantiation Options
% 8.00/1.50  
% 8.00/1.50  --instantiation_flag                    true
% 8.00/1.50  --inst_sos_flag                         false
% 8.00/1.50  --inst_sos_phase                        true
% 8.00/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel_side                     num_symb
% 8.00/1.50  --inst_solver_per_active                1400
% 8.00/1.50  --inst_solver_calls_frac                1.
% 8.00/1.50  --inst_passive_queue_type               priority_queues
% 8.00/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.50  --inst_passive_queues_freq              [25;2]
% 8.00/1.50  --inst_dismatching                      true
% 8.00/1.50  --inst_eager_unprocessed_to_passive     true
% 8.00/1.50  --inst_prop_sim_given                   true
% 8.00/1.50  --inst_prop_sim_new                     false
% 8.00/1.50  --inst_subs_new                         false
% 8.00/1.50  --inst_eq_res_simp                      false
% 8.00/1.50  --inst_subs_given                       false
% 8.00/1.50  --inst_orphan_elimination               true
% 8.00/1.50  --inst_learning_loop_flag               true
% 8.00/1.50  --inst_learning_start                   3000
% 8.00/1.50  --inst_learning_factor                  2
% 8.00/1.50  --inst_start_prop_sim_after_learn       3
% 8.00/1.50  --inst_sel_renew                        solver
% 8.00/1.50  --inst_lit_activity_flag                true
% 8.00/1.50  --inst_restr_to_given                   false
% 8.00/1.50  --inst_activity_threshold               500
% 8.00/1.50  --inst_out_proof                        true
% 8.00/1.50  
% 8.00/1.50  ------ Resolution Options
% 8.00/1.50  
% 8.00/1.50  --resolution_flag                       true
% 8.00/1.50  --res_lit_sel                           adaptive
% 8.00/1.50  --res_lit_sel_side                      none
% 8.00/1.50  --res_ordering                          kbo
% 8.00/1.50  --res_to_prop_solver                    active
% 8.00/1.50  --res_prop_simpl_new                    false
% 8.00/1.50  --res_prop_simpl_given                  true
% 8.00/1.50  --res_passive_queue_type                priority_queues
% 8.00/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.50  --res_passive_queues_freq               [15;5]
% 8.00/1.50  --res_forward_subs                      full
% 8.00/1.50  --res_backward_subs                     full
% 8.00/1.50  --res_forward_subs_resolution           true
% 8.00/1.50  --res_backward_subs_resolution          true
% 8.00/1.50  --res_orphan_elimination                true
% 8.00/1.50  --res_time_limit                        2.
% 8.00/1.50  --res_out_proof                         true
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Options
% 8.00/1.50  
% 8.00/1.50  --superposition_flag                    true
% 8.00/1.50  --sup_passive_queue_type                priority_queues
% 8.00/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.50  --sup_passive_queues_freq               [1;4]
% 8.00/1.50  --demod_completeness_check              fast
% 8.00/1.50  --demod_use_ground                      true
% 8.00/1.50  --sup_to_prop_solver                    passive
% 8.00/1.50  --sup_prop_simpl_new                    true
% 8.00/1.50  --sup_prop_simpl_given                  true
% 8.00/1.50  --sup_fun_splitting                     false
% 8.00/1.50  --sup_smt_interval                      50000
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Simplification Setup
% 8.00/1.50  
% 8.00/1.50  --sup_indices_passive                   []
% 8.00/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_full_bw                           [BwDemod]
% 8.00/1.50  --sup_immed_triv                        [TrivRules]
% 8.00/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_immed_bw_main                     []
% 8.00/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.00/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.00/1.50  
% 8.00/1.50  ------ Combination Options
% 8.00/1.50  
% 8.00/1.50  --comb_res_mult                         3
% 8.00/1.50  --comb_sup_mult                         2
% 8.00/1.50  --comb_inst_mult                        10
% 8.00/1.50  
% 8.00/1.50  ------ Debug Options
% 8.00/1.50  
% 8.00/1.50  --dbg_backtrace                         false
% 8.00/1.50  --dbg_dump_prop_clauses                 false
% 8.00/1.50  --dbg_dump_prop_clauses_file            -
% 8.00/1.50  --dbg_out_stat                          false
% 8.00/1.50  ------ Parsing...
% 8.00/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.00/1.50  ------ Proving...
% 8.00/1.50  ------ Problem Properties 
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  clauses                                 35
% 8.00/1.50  conjectures                             4
% 8.00/1.50  EPR                                     7
% 8.00/1.50  Horn                                    29
% 8.00/1.50  unary                                   15
% 8.00/1.50  binary                                  13
% 8.00/1.50  lits                                    65
% 8.00/1.50  lits eq                                 23
% 8.00/1.50  fd_pure                                 0
% 8.00/1.50  fd_pseudo                               0
% 8.00/1.50  fd_cond                                 0
% 8.00/1.50  fd_pseudo_cond                          4
% 8.00/1.50  AC symbols                              0
% 8.00/1.50  
% 8.00/1.50  ------ Input Options Time Limit: Unbounded
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  ------ 
% 8.00/1.50  Current options:
% 8.00/1.50  ------ 
% 8.00/1.50  
% 8.00/1.50  ------ Input Options
% 8.00/1.50  
% 8.00/1.50  --out_options                           all
% 8.00/1.50  --tptp_safe_out                         true
% 8.00/1.50  --problem_path                          ""
% 8.00/1.50  --include_path                          ""
% 8.00/1.50  --clausifier                            res/vclausify_rel
% 8.00/1.50  --clausifier_options                    --mode clausify
% 8.00/1.50  --stdin                                 false
% 8.00/1.50  --stats_out                             sel
% 8.00/1.50  
% 8.00/1.50  ------ General Options
% 8.00/1.50  
% 8.00/1.50  --fof                                   false
% 8.00/1.50  --time_out_real                         604.99
% 8.00/1.50  --time_out_virtual                      -1.
% 8.00/1.50  --symbol_type_check                     false
% 8.00/1.50  --clausify_out                          false
% 8.00/1.50  --sig_cnt_out                           false
% 8.00/1.50  --trig_cnt_out                          false
% 8.00/1.50  --trig_cnt_out_tolerance                1.
% 8.00/1.50  --trig_cnt_out_sk_spl                   false
% 8.00/1.50  --abstr_cl_out                          false
% 8.00/1.50  
% 8.00/1.50  ------ Global Options
% 8.00/1.50  
% 8.00/1.50  --schedule                              none
% 8.00/1.50  --add_important_lit                     false
% 8.00/1.50  --prop_solver_per_cl                    1000
% 8.00/1.50  --min_unsat_core                        false
% 8.00/1.50  --soft_assumptions                      false
% 8.00/1.50  --soft_lemma_size                       3
% 8.00/1.50  --prop_impl_unit_size                   0
% 8.00/1.50  --prop_impl_unit                        []
% 8.00/1.50  --share_sel_clauses                     true
% 8.00/1.50  --reset_solvers                         false
% 8.00/1.50  --bc_imp_inh                            [conj_cone]
% 8.00/1.50  --conj_cone_tolerance                   3.
% 8.00/1.50  --extra_neg_conj                        none
% 8.00/1.50  --large_theory_mode                     true
% 8.00/1.50  --prolific_symb_bound                   200
% 8.00/1.50  --lt_threshold                          2000
% 8.00/1.50  --clause_weak_htbl                      true
% 8.00/1.50  --gc_record_bc_elim                     false
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing Options
% 8.00/1.50  
% 8.00/1.50  --preprocessing_flag                    true
% 8.00/1.50  --time_out_prep_mult                    0.1
% 8.00/1.50  --splitting_mode                        input
% 8.00/1.50  --splitting_grd                         true
% 8.00/1.50  --splitting_cvd                         false
% 8.00/1.50  --splitting_cvd_svl                     false
% 8.00/1.50  --splitting_nvd                         32
% 8.00/1.50  --sub_typing                            true
% 8.00/1.50  --prep_gs_sim                           false
% 8.00/1.50  --prep_unflatten                        true
% 8.00/1.50  --prep_res_sim                          true
% 8.00/1.50  --prep_upred                            true
% 8.00/1.50  --prep_sem_filter                       exhaustive
% 8.00/1.50  --prep_sem_filter_out                   false
% 8.00/1.50  --pred_elim                             false
% 8.00/1.50  --res_sim_input                         true
% 8.00/1.50  --eq_ax_congr_red                       true
% 8.00/1.50  --pure_diseq_elim                       true
% 8.00/1.50  --brand_transform                       false
% 8.00/1.50  --non_eq_to_eq                          false
% 8.00/1.50  --prep_def_merge                        true
% 8.00/1.50  --prep_def_merge_prop_impl              false
% 8.00/1.50  --prep_def_merge_mbd                    true
% 8.00/1.50  --prep_def_merge_tr_red                 false
% 8.00/1.50  --prep_def_merge_tr_cl                  false
% 8.00/1.50  --smt_preprocessing                     true
% 8.00/1.50  --smt_ac_axioms                         fast
% 8.00/1.50  --preprocessed_out                      false
% 8.00/1.50  --preprocessed_stats                    false
% 8.00/1.50  
% 8.00/1.50  ------ Abstraction refinement Options
% 8.00/1.50  
% 8.00/1.50  --abstr_ref                             []
% 8.00/1.50  --abstr_ref_prep                        false
% 8.00/1.50  --abstr_ref_until_sat                   false
% 8.00/1.50  --abstr_ref_sig_restrict                funpre
% 8.00/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.50  --abstr_ref_under                       []
% 8.00/1.50  
% 8.00/1.50  ------ SAT Options
% 8.00/1.50  
% 8.00/1.50  --sat_mode                              false
% 8.00/1.50  --sat_fm_restart_options                ""
% 8.00/1.50  --sat_gr_def                            false
% 8.00/1.50  --sat_epr_types                         true
% 8.00/1.50  --sat_non_cyclic_types                  false
% 8.00/1.50  --sat_finite_models                     false
% 8.00/1.50  --sat_fm_lemmas                         false
% 8.00/1.50  --sat_fm_prep                           false
% 8.00/1.50  --sat_fm_uc_incr                        true
% 8.00/1.50  --sat_out_model                         small
% 8.00/1.50  --sat_out_clauses                       false
% 8.00/1.50  
% 8.00/1.50  ------ QBF Options
% 8.00/1.50  
% 8.00/1.50  --qbf_mode                              false
% 8.00/1.50  --qbf_elim_univ                         false
% 8.00/1.50  --qbf_dom_inst                          none
% 8.00/1.50  --qbf_dom_pre_inst                      false
% 8.00/1.50  --qbf_sk_in                             false
% 8.00/1.50  --qbf_pred_elim                         true
% 8.00/1.50  --qbf_split                             512
% 8.00/1.50  
% 8.00/1.50  ------ BMC1 Options
% 8.00/1.50  
% 8.00/1.50  --bmc1_incremental                      false
% 8.00/1.50  --bmc1_axioms                           reachable_all
% 8.00/1.50  --bmc1_min_bound                        0
% 8.00/1.50  --bmc1_max_bound                        -1
% 8.00/1.50  --bmc1_max_bound_default                -1
% 8.00/1.50  --bmc1_symbol_reachability              true
% 8.00/1.50  --bmc1_property_lemmas                  false
% 8.00/1.50  --bmc1_k_induction                      false
% 8.00/1.50  --bmc1_non_equiv_states                 false
% 8.00/1.50  --bmc1_deadlock                         false
% 8.00/1.50  --bmc1_ucm                              false
% 8.00/1.50  --bmc1_add_unsat_core                   none
% 8.00/1.50  --bmc1_unsat_core_children              false
% 8.00/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.50  --bmc1_out_stat                         full
% 8.00/1.50  --bmc1_ground_init                      false
% 8.00/1.50  --bmc1_pre_inst_next_state              false
% 8.00/1.50  --bmc1_pre_inst_state                   false
% 8.00/1.50  --bmc1_pre_inst_reach_state             false
% 8.00/1.50  --bmc1_out_unsat_core                   false
% 8.00/1.50  --bmc1_aig_witness_out                  false
% 8.00/1.50  --bmc1_verbose                          false
% 8.00/1.50  --bmc1_dump_clauses_tptp                false
% 8.00/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.50  --bmc1_dump_file                        -
% 8.00/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.50  --bmc1_ucm_extend_mode                  1
% 8.00/1.50  --bmc1_ucm_init_mode                    2
% 8.00/1.50  --bmc1_ucm_cone_mode                    none
% 8.00/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.50  --bmc1_ucm_relax_model                  4
% 8.00/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.50  --bmc1_ucm_layered_model                none
% 8.00/1.50  --bmc1_ucm_max_lemma_size               10
% 8.00/1.50  
% 8.00/1.50  ------ AIG Options
% 8.00/1.50  
% 8.00/1.50  --aig_mode                              false
% 8.00/1.50  
% 8.00/1.50  ------ Instantiation Options
% 8.00/1.50  
% 8.00/1.50  --instantiation_flag                    true
% 8.00/1.50  --inst_sos_flag                         false
% 8.00/1.50  --inst_sos_phase                        true
% 8.00/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel_side                     num_symb
% 8.00/1.50  --inst_solver_per_active                1400
% 8.00/1.50  --inst_solver_calls_frac                1.
% 8.00/1.50  --inst_passive_queue_type               priority_queues
% 8.00/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.50  --inst_passive_queues_freq              [25;2]
% 8.00/1.50  --inst_dismatching                      true
% 8.00/1.50  --inst_eager_unprocessed_to_passive     true
% 8.00/1.50  --inst_prop_sim_given                   true
% 8.00/1.50  --inst_prop_sim_new                     false
% 8.00/1.50  --inst_subs_new                         false
% 8.00/1.50  --inst_eq_res_simp                      false
% 8.00/1.50  --inst_subs_given                       false
% 8.00/1.50  --inst_orphan_elimination               true
% 8.00/1.50  --inst_learning_loop_flag               true
% 8.00/1.50  --inst_learning_start                   3000
% 8.00/1.50  --inst_learning_factor                  2
% 8.00/1.50  --inst_start_prop_sim_after_learn       3
% 8.00/1.50  --inst_sel_renew                        solver
% 8.00/1.50  --inst_lit_activity_flag                true
% 8.00/1.50  --inst_restr_to_given                   false
% 8.00/1.50  --inst_activity_threshold               500
% 8.00/1.50  --inst_out_proof                        true
% 8.00/1.50  
% 8.00/1.50  ------ Resolution Options
% 8.00/1.50  
% 8.00/1.50  --resolution_flag                       true
% 8.00/1.50  --res_lit_sel                           adaptive
% 8.00/1.50  --res_lit_sel_side                      none
% 8.00/1.50  --res_ordering                          kbo
% 8.00/1.50  --res_to_prop_solver                    active
% 8.00/1.50  --res_prop_simpl_new                    false
% 8.00/1.50  --res_prop_simpl_given                  true
% 8.00/1.50  --res_passive_queue_type                priority_queues
% 8.00/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.50  --res_passive_queues_freq               [15;5]
% 8.00/1.50  --res_forward_subs                      full
% 8.00/1.50  --res_backward_subs                     full
% 8.00/1.50  --res_forward_subs_resolution           true
% 8.00/1.50  --res_backward_subs_resolution          true
% 8.00/1.50  --res_orphan_elimination                true
% 8.00/1.50  --res_time_limit                        2.
% 8.00/1.50  --res_out_proof                         true
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Options
% 8.00/1.50  
% 8.00/1.50  --superposition_flag                    true
% 8.00/1.50  --sup_passive_queue_type                priority_queues
% 8.00/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.50  --sup_passive_queues_freq               [1;4]
% 8.00/1.50  --demod_completeness_check              fast
% 8.00/1.50  --demod_use_ground                      true
% 8.00/1.50  --sup_to_prop_solver                    passive
% 8.00/1.50  --sup_prop_simpl_new                    true
% 8.00/1.50  --sup_prop_simpl_given                  true
% 8.00/1.50  --sup_fun_splitting                     false
% 8.00/1.50  --sup_smt_interval                      50000
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Simplification Setup
% 8.00/1.50  
% 8.00/1.50  --sup_indices_passive                   []
% 8.00/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_full_bw                           [BwDemod]
% 8.00/1.50  --sup_immed_triv                        [TrivRules]
% 8.00/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_immed_bw_main                     []
% 8.00/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.00/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.00/1.50  
% 8.00/1.50  ------ Combination Options
% 8.00/1.50  
% 8.00/1.50  --comb_res_mult                         3
% 8.00/1.50  --comb_sup_mult                         2
% 8.00/1.50  --comb_inst_mult                        10
% 8.00/1.50  
% 8.00/1.50  ------ Debug Options
% 8.00/1.50  
% 8.00/1.50  --dbg_backtrace                         false
% 8.00/1.50  --dbg_dump_prop_clauses                 false
% 8.00/1.50  --dbg_dump_prop_clauses_file            -
% 8.00/1.50  --dbg_out_stat                          false
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  ------ Proving...
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  % SZS status Theorem for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  fof(f12,axiom,(
% 8.00/1.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f79,plain,(
% 8.00/1.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f12])).
% 8.00/1.50  
% 8.00/1.50  fof(f5,axiom,(
% 8.00/1.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f71,plain,(
% 8.00/1.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.00/1.50    inference(cnf_transformation,[],[f5])).
% 8.00/1.50  
% 8.00/1.50  fof(f13,axiom,(
% 8.00/1.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f34,plain,(
% 8.00/1.50    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 8.00/1.50    inference(ennf_transformation,[],[f13])).
% 8.00/1.50  
% 8.00/1.50  fof(f35,plain,(
% 8.00/1.50    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 8.00/1.50    inference(flattening,[],[f34])).
% 8.00/1.50  
% 8.00/1.50  fof(f80,plain,(
% 8.00/1.50    ( ! [X2,X0,X3,X1] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f35])).
% 8.00/1.50  
% 8.00/1.50  fof(f11,axiom,(
% 8.00/1.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f78,plain,(
% 8.00/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f11])).
% 8.00/1.50  
% 8.00/1.50  fof(f14,axiom,(
% 8.00/1.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f81,plain,(
% 8.00/1.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f14])).
% 8.00/1.50  
% 8.00/1.50  fof(f7,axiom,(
% 8.00/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f73,plain,(
% 8.00/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f7])).
% 8.00/1.50  
% 8.00/1.50  fof(f17,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f38,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 8.00/1.50    inference(ennf_transformation,[],[f17])).
% 8.00/1.50  
% 8.00/1.50  fof(f84,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f38])).
% 8.00/1.50  
% 8.00/1.50  fof(f8,axiom,(
% 8.00/1.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f52,plain,(
% 8.00/1.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 8.00/1.50    inference(nnf_transformation,[],[f8])).
% 8.00/1.50  
% 8.00/1.50  fof(f75,plain,(
% 8.00/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f52])).
% 8.00/1.50  
% 8.00/1.50  fof(f74,plain,(
% 8.00/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f52])).
% 8.00/1.50  
% 8.00/1.50  fof(f25,conjecture,(
% 8.00/1.50    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f26,negated_conjecture,(
% 8.00/1.50    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 8.00/1.50    inference(negated_conjecture,[],[f25])).
% 8.00/1.50  
% 8.00/1.50  fof(f41,plain,(
% 8.00/1.50    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f26])).
% 8.00/1.50  
% 8.00/1.50  fof(f58,plain,(
% 8.00/1.50    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f59,plain,(
% 8.00/1.50    (k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 8.00/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f58])).
% 8.00/1.50  
% 8.00/1.50  fof(f101,plain,(
% 8.00/1.50    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 8.00/1.50    inference(cnf_transformation,[],[f59])).
% 8.00/1.50  
% 8.00/1.50  fof(f18,axiom,(
% 8.00/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f85,plain,(
% 8.00/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f18])).
% 8.00/1.50  
% 8.00/1.50  fof(f19,axiom,(
% 8.00/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f86,plain,(
% 8.00/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f19])).
% 8.00/1.50  
% 8.00/1.50  fof(f105,plain,(
% 8.00/1.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 8.00/1.50    inference(definition_unfolding,[],[f85,f86])).
% 8.00/1.50  
% 8.00/1.50  fof(f125,plain,(
% 8.00/1.50    k2_xboole_0(sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 8.00/1.50    inference(definition_unfolding,[],[f101,f105])).
% 8.00/1.50  
% 8.00/1.50  fof(f24,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f40,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f24])).
% 8.00/1.50  
% 8.00/1.50  fof(f56,plain,(
% 8.00/1.50    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 8.00/1.50    inference(nnf_transformation,[],[f40])).
% 8.00/1.50  
% 8.00/1.50  fof(f57,plain,(
% 8.00/1.50    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 8.00/1.50    inference(flattening,[],[f56])).
% 8.00/1.50  
% 8.00/1.50  fof(f96,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f57])).
% 8.00/1.50  
% 8.00/1.50  fof(f121,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 8.00/1.50    inference(definition_unfolding,[],[f96,f86,f105,f105,f86])).
% 8.00/1.50  
% 8.00/1.50  fof(f104,plain,(
% 8.00/1.50    k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4),
% 8.00/1.50    inference(cnf_transformation,[],[f59])).
% 8.00/1.50  
% 8.00/1.50  fof(f122,plain,(
% 8.00/1.50    k1_xboole_0 != sK5 | k2_enumset1(sK3,sK3,sK3,sK3) != sK4),
% 8.00/1.50    inference(definition_unfolding,[],[f104,f105])).
% 8.00/1.50  
% 8.00/1.50  fof(f97,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 8.00/1.50    inference(cnf_transformation,[],[f57])).
% 8.00/1.50  
% 8.00/1.50  fof(f120,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k1_xboole_0 != X0) )),
% 8.00/1.50    inference(definition_unfolding,[],[f97,f86])).
% 8.00/1.50  
% 8.00/1.50  fof(f136,plain,(
% 8.00/1.50    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X2))) )),
% 8.00/1.50    inference(equality_resolution,[],[f120])).
% 8.00/1.50  
% 8.00/1.50  fof(f22,axiom,(
% 8.00/1.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f55,plain,(
% 8.00/1.50    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 8.00/1.50    inference(nnf_transformation,[],[f22])).
% 8.00/1.50  
% 8.00/1.50  fof(f93,plain,(
% 8.00/1.50    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f55])).
% 8.00/1.50  
% 8.00/1.50  fof(f115,plain,(
% 8.00/1.50    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 8.00/1.50    inference(definition_unfolding,[],[f93,f105,f105,f105])).
% 8.00/1.50  
% 8.00/1.50  fof(f132,plain,(
% 8.00/1.50    ( ! [X1] : (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1)) )),
% 8.00/1.50    inference(equality_resolution,[],[f115])).
% 8.00/1.50  
% 8.00/1.50  fof(f23,axiom,(
% 8.00/1.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f95,plain,(
% 8.00/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f23])).
% 8.00/1.50  
% 8.00/1.50  fof(f116,plain,(
% 8.00/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 8.00/1.50    inference(definition_unfolding,[],[f95,f105,f86])).
% 8.00/1.50  
% 8.00/1.50  fof(f4,axiom,(
% 8.00/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f50,plain,(
% 8.00/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.00/1.50    inference(nnf_transformation,[],[f4])).
% 8.00/1.50  
% 8.00/1.50  fof(f51,plain,(
% 8.00/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.00/1.50    inference(flattening,[],[f50])).
% 8.00/1.50  
% 8.00/1.50  fof(f70,plain,(
% 8.00/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f15,axiom,(
% 8.00/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f82,plain,(
% 8.00/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f15])).
% 8.00/1.50  
% 8.00/1.50  fof(f9,axiom,(
% 8.00/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f76,plain,(
% 8.00/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.00/1.50    inference(cnf_transformation,[],[f9])).
% 8.00/1.50  
% 8.00/1.50  fof(f16,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 8.00/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f36,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 8.00/1.50    inference(ennf_transformation,[],[f16])).
% 8.00/1.50  
% 8.00/1.50  fof(f37,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 8.00/1.50    inference(flattening,[],[f36])).
% 8.00/1.50  
% 8.00/1.50  fof(f83,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f37])).
% 8.00/1.50  
% 8.00/1.50  fof(f103,plain,(
% 8.00/1.50    k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4),
% 8.00/1.50    inference(cnf_transformation,[],[f59])).
% 8.00/1.50  
% 8.00/1.50  fof(f123,plain,(
% 8.00/1.50    k2_enumset1(sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4),
% 8.00/1.50    inference(definition_unfolding,[],[f103,f105])).
% 8.00/1.50  
% 8.00/1.50  fof(f102,plain,(
% 8.00/1.50    k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4),
% 8.00/1.50    inference(cnf_transformation,[],[f59])).
% 8.00/1.50  
% 8.00/1.50  fof(f124,plain,(
% 8.00/1.50    k2_enumset1(sK3,sK3,sK3,sK3) != sK5 | k2_enumset1(sK3,sK3,sK3,sK3) != sK4),
% 8.00/1.50    inference(definition_unfolding,[],[f102,f105,f105])).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18,plain,
% 8.00/1.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f79]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1060,plain,
% 8.00/1.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_11,plain,
% 8.00/1.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f71]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_19,plain,
% 8.00/1.50      ( ~ r1_xboole_0(X0,X1)
% 8.00/1.50      | ~ r1_xboole_0(X2,X3)
% 8.00/1.50      | X2 = X1
% 8.00/1.50      | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f80]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1059,plain,
% 8.00/1.50      ( X0 = X1
% 8.00/1.50      | k2_xboole_0(X0,X2) != k2_xboole_0(X3,X1)
% 8.00/1.50      | r1_xboole_0(X2,X1) != iProver_top
% 8.00/1.50      | r1_xboole_0(X0,X3) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2320,plain,
% 8.00/1.50      ( X0 = X1
% 8.00/1.50      | k2_xboole_0(X2,X0) != X1
% 8.00/1.50      | r1_xboole_0(X1,X2) != iProver_top
% 8.00/1.50      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_11,c_1059]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_17,plain,
% 8.00/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f78]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_20,plain,
% 8.00/1.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f81]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1058,plain,
% 8.00/1.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1704,plain,
% 8.00/1.50      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_17,c_1058]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4530,plain,
% 8.00/1.50      ( r1_xboole_0(X1,X2) != iProver_top
% 8.00/1.50      | k2_xboole_0(X2,X0) != X1
% 8.00/1.50      | X0 = X1 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_2320,c_1704]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4531,plain,
% 8.00/1.50      ( X0 = X1
% 8.00/1.50      | k2_xboole_0(X2,X0) != X1
% 8.00/1.50      | r1_xboole_0(X1,X2) != iProver_top ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_4530]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4538,plain,
% 8.00/1.50      ( k2_xboole_0(X0,X1) = X1
% 8.00/1.50      | r1_xboole_0(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 8.00/1.50      inference(equality_resolution,[status(thm)],[c_4531]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_30510,plain,
% 8.00/1.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1060,c_4538]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_13,plain,
% 8.00/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f73]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1063,plain,
% 8.00/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_23,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,X1)
% 8.00/1.50      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f84]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1055,plain,
% 8.00/1.50      ( r1_tarski(X0,X1) != iProver_top
% 8.00/1.50      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_14,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f75]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1062,plain,
% 8.00/1.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 8.00/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2612,plain,
% 8.00/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k1_xboole_0
% 8.00/1.50      | r1_tarski(X0,X2) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1055,c_1062]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6910,plain,
% 8.00/1.50      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1063,c_2612]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_15,plain,
% 8.00/1.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f74]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1061,plain,
% 8.00/1.50      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 8.00/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7526,plain,
% 8.00/1.50      ( r1_tarski(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X1,X0)) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_6910,c_1061]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_41,negated_conjecture,
% 8.00/1.50      ( k2_xboole_0(sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 8.00/1.50      inference(cnf_transformation,[],[f125]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_37,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 8.00/1.50      | k2_enumset1(X1,X1,X1,X2) = X0
% 8.00/1.50      | k2_enumset1(X2,X2,X2,X2) = X0
% 8.00/1.50      | k2_enumset1(X1,X1,X1,X1) = X0
% 8.00/1.50      | k1_xboole_0 = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f121]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1050,plain,
% 8.00/1.50      ( k2_enumset1(X0,X0,X0,X0) = X1
% 8.00/1.50      | k2_enumset1(X0,X0,X0,X2) = X1
% 8.00/1.50      | k2_enumset1(X2,X2,X2,X2) = X1
% 8.00/1.50      | k1_xboole_0 = X1
% 8.00/1.50      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1329,plain,
% 8.00/1.50      ( k2_enumset1(sK3,sK3,sK3,sK3) = X0
% 8.00/1.50      | k1_xboole_0 = X0
% 8.00/1.50      | r1_tarski(X0,k2_xboole_0(sK4,sK5)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_41,c_1050]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1330,plain,
% 8.00/1.50      ( k2_xboole_0(sK4,sK5) = X0
% 8.00/1.50      | k1_xboole_0 = X0
% 8.00/1.50      | r1_tarski(X0,k2_xboole_0(sK4,sK5)) != iProver_top ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_1329,c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_9187,plain,
% 8.00/1.50      ( k2_xboole_0(k1_xboole_0,sK5) = k2_xboole_0(sK4,sK5)
% 8.00/1.50      | k2_xboole_0(k1_xboole_0,sK5) = k1_xboole_0 ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_7526,c_1330]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_30595,plain,
% 8.00/1.50      ( k2_xboole_0(sK4,sK5) = sK5 | sK5 = k1_xboole_0 ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_30510,c_9187]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_509,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1295,plain,
% 8.00/1.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_509]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_28520,plain,
% 8.00/1.50      ( sK5 != k1_xboole_0
% 8.00/1.50      | k1_xboole_0 = sK5
% 8.00/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1295]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_512,plain,
% 8.00/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.00/1.50      theory(equality) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3290,plain,
% 8.00/1.50      ( r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))
% 8.00/1.50      | ~ r1_xboole_0(X2,k1_xboole_0)
% 8.00/1.50      | X0 != X2 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_512,c_17]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_14466,plain,
% 8.00/1.50      ( r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) | X0 != X2 ),
% 8.00/1.50      inference(forward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_3290,c_18]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_38,negated_conjecture,
% 8.00/1.50      ( k2_enumset1(sK3,sK3,sK3,sK3) != sK4 | k1_xboole_0 != sK5 ),
% 8.00/1.50      inference(cnf_transformation,[],[f122]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5931,plain,
% 8.00/1.50      ( ~ r1_tarski(sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 8.00/1.50      | k2_enumset1(sK3,sK3,sK3,sK3) = sK4
% 8.00/1.50      | k1_xboole_0 = sK4
% 8.00/1.50      | k1_xboole_0 != sK5 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_37,c_38]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_36,plain,
% 8.00/1.50      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f136]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_46,plain,
% 8.00/1.50      ( r1_tarski(k1_xboole_0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_36]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1106,plain,
% 8.00/1.50      ( k2_xboole_0(sK4,sK5) != sK4 | sK5 != k1_xboole_0 ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_38,c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_31,plain,
% 8.00/1.50      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f132]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_32,plain,
% 8.00/1.50      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f116]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1156,plain,
% 8.00/1.50      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_31,c_32]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1216,plain,
% 8.00/1.50      ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1156]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1405,plain,
% 8.00/1.50      ( ~ r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1))
% 8.00/1.50      | k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 8.00/1.50      | k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 8.00/1.50      | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
% 8.00/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_37]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1407,plain,
% 8.00/1.50      ( ~ r1_tarski(k1_xboole_0,k2_enumset1(sK3,sK3,sK3,sK3))
% 8.00/1.50      | k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 8.00/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1405]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1299,plain,
% 8.00/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_509]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2258,plain,
% 8.00/1.50      ( sK4 != k1_xboole_0
% 8.00/1.50      | k1_xboole_0 = sK4
% 8.00/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1299]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2263,plain,
% 8.00/1.50      ( r1_tarski(sK5,k1_xboole_0)
% 8.00/1.50      | k4_xboole_0(sK5,k1_xboole_0) != k1_xboole_0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f70]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1501,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2709,plain,
% 8.00/1.50      ( ~ r1_tarski(sK5,k1_xboole_0)
% 8.00/1.50      | ~ r1_tarski(k1_xboole_0,sK5)
% 8.00/1.50      | sK5 = k1_xboole_0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1501]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2710,plain,
% 8.00/1.50      ( r1_tarski(k1_xboole_0,sK5) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_21,plain,
% 8.00/1.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f82]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1057,plain,
% 8.00/1.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3084,plain,
% 8.00/1.50      ( k2_xboole_0(sK4,sK5) = sK4 | sK4 = k1_xboole_0 ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1057,c_1330]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2550,plain,
% 8.00/1.50      ( k4_xboole_0(sK5,k1_xboole_0) != X0
% 8.00/1.50      | k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0
% 8.00/1.50      | k1_xboole_0 != X0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_509]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5563,plain,
% 8.00/1.50      ( k4_xboole_0(sK5,k1_xboole_0) != sK5
% 8.00/1.50      | k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0
% 8.00/1.50      | k1_xboole_0 != sK5 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2550]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_16,plain,
% 8.00/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f76]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5564,plain,
% 8.00/1.50      ( k4_xboole_0(sK5,k1_xboole_0) = sK5 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6436,plain,
% 8.00/1.50      ( k1_xboole_0 = sK4 | k1_xboole_0 != sK5 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_5931,c_46,c_1106,c_1216,c_1407,c_2258,c_2263,c_2709,
% 8.00/1.50                 c_2710,c_3084,c_5563,c_5564]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_14511,plain,
% 8.00/1.50      ( r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
% 8.00/1.50      | k1_xboole_0 != sK5 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_14466,c_6436]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1740,plain,
% 8.00/1.50      ( r1_tarski(sK4,k1_xboole_0)
% 8.00/1.50      | k4_xboole_0(sK4,k1_xboole_0) != k1_xboole_0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2435,plain,
% 8.00/1.50      ( k4_xboole_0(sK4,k1_xboole_0) != X0
% 8.00/1.50      | k4_xboole_0(sK4,k1_xboole_0) = k1_xboole_0
% 8.00/1.50      | k1_xboole_0 != X0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_509]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5388,plain,
% 8.00/1.50      ( k4_xboole_0(sK4,k1_xboole_0) != sK4
% 8.00/1.50      | k4_xboole_0(sK4,k1_xboole_0) = k1_xboole_0
% 8.00/1.50      | k1_xboole_0 != sK4 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2435]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5389,plain,
% 8.00/1.50      ( k4_xboole_0(sK4,k1_xboole_0) = sK4 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_510,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.00/1.50      theory(equality) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3206,plain,
% 8.00/1.50      ( r1_tarski(X0,k4_xboole_0(k1_xboole_0,X1))
% 8.00/1.50      | ~ r1_tarski(X2,k1_xboole_0)
% 8.00/1.50      | X0 != X2 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_510,c_17]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_11536,plain,
% 8.00/1.50      ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0)
% 8.00/1.50      | r1_tarski(k2_xboole_0(sK4,sK5),k4_xboole_0(k1_xboole_0,X0)) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_3206,c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_508,plain,( X0 = X0 ),theory(equality) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3218,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_510,c_508]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8071,plain,
% 8.00/1.50      ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0)
% 8.00/1.50      | r1_tarski(k2_xboole_0(sK4,sK5),X0) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_3218,c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3214,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 8.00/1.50      | r1_tarski(X1,k2_xboole_0(sK4,sK5))
% 8.00/1.50      | X1 != X0 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_510,c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3517,plain,
% 8.00/1.50      ( r1_tarski(X0,k2_xboole_0(sK4,sK5)) | X0 != k1_xboole_0 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_3214,c_13]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8415,plain,
% 8.00/1.50      ( r1_tarski(k2_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))
% 8.00/1.50      | k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_8071,c_3517]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_10591,plain,
% 8.00/1.50      ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_8415,c_1216]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_10597,plain,
% 8.00/1.50      ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0)
% 8.00/1.50      | ~ r1_tarski(k1_xboole_0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_10591,c_8]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_12541,plain,
% 8.00/1.50      ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_11536,c_46,c_10597]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2876,plain,
% 8.00/1.50      ( X0 != X1 | X1 = X0 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_509,c_508]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5996,plain,
% 8.00/1.50      ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_xboole_0(sK4,sK5) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_2876,c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8080,plain,
% 8.00/1.50      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0)
% 8.00/1.50      | ~ r1_tarski(k2_xboole_0(sK4,sK5),X0) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_3218,c_5996]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_12553,plain,
% 8.00/1.50      ( ~ r1_tarski(k2_xboole_0(sK4,sK5),k1_xboole_0) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_12541,c_8080]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22,plain,
% 8.00/1.50      ( ~ r1_tarski(X0,X1)
% 8.00/1.50      | ~ r1_tarski(X2,X1)
% 8.00/1.50      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f83]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_13261,plain,
% 8.00/1.50      ( ~ r1_tarski(sK4,k1_xboole_0) | ~ r1_tarski(sK5,k1_xboole_0) ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_12553,c_22]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_14901,plain,
% 8.00/1.50      ( k1_xboole_0 != sK5 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_14511,c_1740,c_2263,c_5388,c_5389,c_5563,c_5564,
% 8.00/1.50                 c_6436,c_13261]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_39,negated_conjecture,
% 8.00/1.50      ( k2_enumset1(sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4 ),
% 8.00/1.50      inference(cnf_transformation,[],[f123]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1101,plain,
% 8.00/1.50      ( k2_xboole_0(sK4,sK5) != sK5 | sK4 != k1_xboole_0 ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_39,c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_40,negated_conjecture,
% 8.00/1.50      ( k2_enumset1(sK3,sK3,sK3,sK3) != sK4
% 8.00/1.50      | k2_enumset1(sK3,sK3,sK3,sK3) != sK5 ),
% 8.00/1.50      inference(cnf_transformation,[],[f124]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1137,plain,
% 8.00/1.50      ( k2_xboole_0(sK4,sK5) != sK4 | k2_xboole_0(sK4,sK5) != sK5 ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_40,c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(contradiction,plain,
% 8.00/1.50      ( $false ),
% 8.00/1.50      inference(minisat,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_30595,c_28520,c_14901,c_3084,c_1407,c_1101,c_1216,
% 8.00/1.50                 c_1137,c_46]) ).
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  ------                               Statistics
% 8.00/1.50  
% 8.00/1.50  ------ Selected
% 8.00/1.50  
% 8.00/1.50  total_time:                             0.803
% 8.00/1.50  
%------------------------------------------------------------------------------
