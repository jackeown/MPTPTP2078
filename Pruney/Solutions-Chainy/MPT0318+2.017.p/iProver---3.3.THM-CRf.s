%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:26 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   84 (2049 expanded)
%              Number of clauses        :   39 ( 520 expanded)
%              Number of leaves         :   11 ( 493 expanded)
%              Depth                    :   20
%              Number of atoms          :  214 (5660 expanded)
%              Number of equality atoms :  165 (5023 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k2_zfmisc_1(X0,k1_tarski(X1)) != k1_xboole_0
        & k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k2_zfmisc_1(X0,k1_tarski(X1)) != k1_xboole_0
          & k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k2_zfmisc_1(X0,k1_tarski(X1)) = k1_xboole_0
        | k2_zfmisc_1(k1_tarski(X1),X0) = k1_xboole_0 )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ( k2_zfmisc_1(X0,k1_tarski(X1)) = k1_xboole_0
          | k2_zfmisc_1(k1_tarski(X1),X0) = k1_xboole_0 )
        & k1_xboole_0 != X0 )
   => ( ( k2_zfmisc_1(sK1,k1_tarski(sK2)) = k1_xboole_0
        | k2_zfmisc_1(k1_tarski(sK2),sK1) = k1_xboole_0 )
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ( k2_zfmisc_1(sK1,k1_tarski(sK2)) = k1_xboole_0
      | k2_zfmisc_1(k1_tarski(sK2),sK1) = k1_xboole_0 )
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f20])).

fof(f38,plain,
    ( k2_zfmisc_1(sK1,k1_tarski(sK2)) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski(sK2),sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,
    ( k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0
    | k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f38,f40,f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f22,f40])).

fof(f53,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f51,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f52,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f51])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f32,f40])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_399,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) = k1_xboole_0
    | k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_832,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_6])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_148,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_480,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_481,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_958,plain,
    ( k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_13,c_27,c_28,c_481])).

cnf(c_959,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_958])).

cnf(c_962,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_959,c_6])).

cnf(c_963,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_962,c_13,c_27,c_28,c_481])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_400,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_970,plain,
    ( sK2 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_400])).

cnf(c_1102,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | sK2 = X0 ),
    inference(superposition,[status(thm)],[c_399,c_970])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_396,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k1_xboole_0
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_971,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_396])).

cnf(c_1381,plain,
    ( sK2 = X0
    | r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_971])).

cnf(c_1392,plain,
    ( sK2 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1381,c_400])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_401,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1396,plain,
    ( r2_hidden(X0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1392,c_401])).

cnf(c_1399,plain,
    ( X0 = X1
    | r2_hidden(X1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1392,c_400])).

cnf(c_1437,plain,
    ( X0 = X1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1396,c_1399])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_398,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1397,plain,
    ( k4_xboole_0(X0,sK2) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1392,c_398])).

cnf(c_1439,plain,
    ( X0 != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1437,c_1397])).

cnf(c_1449,plain,
    ( r2_hidden(X0,X1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1439])).

cnf(c_1401,plain,
    ( k4_xboole_0(sK2,X0) != k1_xboole_0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1392,c_396])).

cnf(c_1441,plain,
    ( k1_xboole_0 != X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1437,c_1401])).

cnf(c_1447,plain,
    ( r2_hidden(X0,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1441,c_1437])).

cnf(c_1451,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1449,c_1447])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.78/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.78/1.05  
% 0.78/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.78/1.05  
% 0.78/1.05  ------  iProver source info
% 0.78/1.05  
% 0.78/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.78/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.78/1.05  git: non_committed_changes: false
% 0.78/1.05  git: last_make_outside_of_git: false
% 0.78/1.05  
% 0.78/1.05  ------ 
% 0.78/1.05  
% 0.78/1.05  ------ Input Options
% 0.78/1.05  
% 0.78/1.05  --out_options                           all
% 0.78/1.05  --tptp_safe_out                         true
% 0.78/1.05  --problem_path                          ""
% 0.78/1.05  --include_path                          ""
% 0.78/1.05  --clausifier                            res/vclausify_rel
% 0.78/1.05  --clausifier_options                    --mode clausify
% 0.78/1.05  --stdin                                 false
% 0.78/1.05  --stats_out                             all
% 0.78/1.05  
% 0.78/1.05  ------ General Options
% 0.78/1.05  
% 0.78/1.05  --fof                                   false
% 0.78/1.05  --time_out_real                         305.
% 0.78/1.05  --time_out_virtual                      -1.
% 0.78/1.05  --symbol_type_check                     false
% 0.78/1.05  --clausify_out                          false
% 0.78/1.05  --sig_cnt_out                           false
% 0.78/1.05  --trig_cnt_out                          false
% 0.78/1.05  --trig_cnt_out_tolerance                1.
% 0.78/1.05  --trig_cnt_out_sk_spl                   false
% 0.78/1.05  --abstr_cl_out                          false
% 0.78/1.05  
% 0.78/1.05  ------ Global Options
% 0.78/1.05  
% 0.78/1.05  --schedule                              default
% 0.78/1.05  --add_important_lit                     false
% 0.78/1.05  --prop_solver_per_cl                    1000
% 0.78/1.05  --min_unsat_core                        false
% 0.78/1.05  --soft_assumptions                      false
% 0.78/1.05  --soft_lemma_size                       3
% 0.78/1.05  --prop_impl_unit_size                   0
% 0.78/1.05  --prop_impl_unit                        []
% 0.78/1.05  --share_sel_clauses                     true
% 0.78/1.05  --reset_solvers                         false
% 0.78/1.05  --bc_imp_inh                            [conj_cone]
% 0.78/1.05  --conj_cone_tolerance                   3.
% 0.78/1.05  --extra_neg_conj                        none
% 0.78/1.05  --large_theory_mode                     true
% 0.78/1.05  --prolific_symb_bound                   200
% 0.78/1.05  --lt_threshold                          2000
% 0.78/1.05  --clause_weak_htbl                      true
% 0.78/1.05  --gc_record_bc_elim                     false
% 0.78/1.05  
% 0.78/1.05  ------ Preprocessing Options
% 0.78/1.05  
% 0.78/1.05  --preprocessing_flag                    true
% 0.78/1.05  --time_out_prep_mult                    0.1
% 0.78/1.05  --splitting_mode                        input
% 0.78/1.05  --splitting_grd                         true
% 0.78/1.05  --splitting_cvd                         false
% 0.78/1.05  --splitting_cvd_svl                     false
% 0.78/1.05  --splitting_nvd                         32
% 0.78/1.05  --sub_typing                            true
% 0.78/1.05  --prep_gs_sim                           true
% 0.78/1.05  --prep_unflatten                        true
% 0.78/1.05  --prep_res_sim                          true
% 0.78/1.05  --prep_upred                            true
% 0.78/1.05  --prep_sem_filter                       exhaustive
% 0.78/1.05  --prep_sem_filter_out                   false
% 0.78/1.05  --pred_elim                             true
% 0.78/1.05  --res_sim_input                         true
% 0.78/1.05  --eq_ax_congr_red                       true
% 0.78/1.05  --pure_diseq_elim                       true
% 0.78/1.05  --brand_transform                       false
% 0.78/1.05  --non_eq_to_eq                          false
% 0.78/1.05  --prep_def_merge                        true
% 0.78/1.05  --prep_def_merge_prop_impl              false
% 0.78/1.05  --prep_def_merge_mbd                    true
% 0.78/1.05  --prep_def_merge_tr_red                 false
% 0.78/1.05  --prep_def_merge_tr_cl                  false
% 0.78/1.05  --smt_preprocessing                     true
% 0.78/1.05  --smt_ac_axioms                         fast
% 0.78/1.05  --preprocessed_out                      false
% 0.78/1.05  --preprocessed_stats                    false
% 0.78/1.05  
% 0.78/1.05  ------ Abstraction refinement Options
% 0.78/1.05  
% 0.78/1.05  --abstr_ref                             []
% 0.78/1.05  --abstr_ref_prep                        false
% 0.78/1.05  --abstr_ref_until_sat                   false
% 0.78/1.05  --abstr_ref_sig_restrict                funpre
% 0.78/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.78/1.05  --abstr_ref_under                       []
% 0.78/1.05  
% 0.78/1.05  ------ SAT Options
% 0.78/1.05  
% 0.78/1.05  --sat_mode                              false
% 0.78/1.05  --sat_fm_restart_options                ""
% 0.78/1.05  --sat_gr_def                            false
% 0.78/1.05  --sat_epr_types                         true
% 0.78/1.05  --sat_non_cyclic_types                  false
% 0.78/1.05  --sat_finite_models                     false
% 0.78/1.05  --sat_fm_lemmas                         false
% 0.78/1.05  --sat_fm_prep                           false
% 0.78/1.05  --sat_fm_uc_incr                        true
% 0.78/1.05  --sat_out_model                         small
% 0.78/1.05  --sat_out_clauses                       false
% 0.78/1.05  
% 0.78/1.05  ------ QBF Options
% 0.78/1.05  
% 0.78/1.05  --qbf_mode                              false
% 0.78/1.05  --qbf_elim_univ                         false
% 0.78/1.05  --qbf_dom_inst                          none
% 0.78/1.05  --qbf_dom_pre_inst                      false
% 0.78/1.05  --qbf_sk_in                             false
% 0.78/1.05  --qbf_pred_elim                         true
% 0.78/1.05  --qbf_split                             512
% 0.78/1.05  
% 0.78/1.05  ------ BMC1 Options
% 0.78/1.05  
% 0.78/1.05  --bmc1_incremental                      false
% 0.78/1.05  --bmc1_axioms                           reachable_all
% 0.78/1.05  --bmc1_min_bound                        0
% 0.78/1.05  --bmc1_max_bound                        -1
% 0.78/1.05  --bmc1_max_bound_default                -1
% 0.78/1.05  --bmc1_symbol_reachability              true
% 0.78/1.05  --bmc1_property_lemmas                  false
% 0.78/1.05  --bmc1_k_induction                      false
% 0.78/1.05  --bmc1_non_equiv_states                 false
% 0.78/1.05  --bmc1_deadlock                         false
% 0.78/1.05  --bmc1_ucm                              false
% 0.78/1.05  --bmc1_add_unsat_core                   none
% 0.78/1.05  --bmc1_unsat_core_children              false
% 0.78/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.78/1.05  --bmc1_out_stat                         full
% 0.78/1.05  --bmc1_ground_init                      false
% 0.78/1.05  --bmc1_pre_inst_next_state              false
% 0.78/1.05  --bmc1_pre_inst_state                   false
% 0.78/1.05  --bmc1_pre_inst_reach_state             false
% 0.78/1.05  --bmc1_out_unsat_core                   false
% 0.78/1.05  --bmc1_aig_witness_out                  false
% 0.78/1.05  --bmc1_verbose                          false
% 0.78/1.05  --bmc1_dump_clauses_tptp                false
% 0.78/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.78/1.05  --bmc1_dump_file                        -
% 0.78/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.78/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.78/1.05  --bmc1_ucm_extend_mode                  1
% 0.78/1.05  --bmc1_ucm_init_mode                    2
% 0.78/1.05  --bmc1_ucm_cone_mode                    none
% 0.78/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.78/1.05  --bmc1_ucm_relax_model                  4
% 0.78/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.78/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.78/1.05  --bmc1_ucm_layered_model                none
% 0.78/1.05  --bmc1_ucm_max_lemma_size               10
% 0.78/1.05  
% 0.78/1.05  ------ AIG Options
% 0.78/1.05  
% 0.78/1.05  --aig_mode                              false
% 0.78/1.05  
% 0.78/1.05  ------ Instantiation Options
% 0.78/1.05  
% 0.78/1.05  --instantiation_flag                    true
% 0.78/1.05  --inst_sos_flag                         false
% 0.78/1.05  --inst_sos_phase                        true
% 0.78/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.78/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.78/1.05  --inst_lit_sel_side                     num_symb
% 0.78/1.05  --inst_solver_per_active                1400
% 0.78/1.05  --inst_solver_calls_frac                1.
% 0.78/1.05  --inst_passive_queue_type               priority_queues
% 0.78/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.78/1.05  --inst_passive_queues_freq              [25;2]
% 0.78/1.05  --inst_dismatching                      true
% 0.78/1.05  --inst_eager_unprocessed_to_passive     true
% 0.78/1.05  --inst_prop_sim_given                   true
% 0.78/1.05  --inst_prop_sim_new                     false
% 0.78/1.05  --inst_subs_new                         false
% 0.78/1.05  --inst_eq_res_simp                      false
% 0.78/1.05  --inst_subs_given                       false
% 0.78/1.05  --inst_orphan_elimination               true
% 0.78/1.05  --inst_learning_loop_flag               true
% 0.78/1.05  --inst_learning_start                   3000
% 0.78/1.05  --inst_learning_factor                  2
% 0.78/1.05  --inst_start_prop_sim_after_learn       3
% 0.78/1.05  --inst_sel_renew                        solver
% 0.78/1.05  --inst_lit_activity_flag                true
% 0.78/1.05  --inst_restr_to_given                   false
% 0.78/1.05  --inst_activity_threshold               500
% 0.78/1.05  --inst_out_proof                        true
% 0.78/1.05  
% 0.78/1.05  ------ Resolution Options
% 0.78/1.05  
% 0.78/1.05  --resolution_flag                       true
% 0.78/1.05  --res_lit_sel                           adaptive
% 0.78/1.05  --res_lit_sel_side                      none
% 0.78/1.05  --res_ordering                          kbo
% 0.78/1.05  --res_to_prop_solver                    active
% 0.78/1.05  --res_prop_simpl_new                    false
% 0.78/1.05  --res_prop_simpl_given                  true
% 0.78/1.05  --res_passive_queue_type                priority_queues
% 0.78/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.78/1.05  --res_passive_queues_freq               [15;5]
% 0.78/1.05  --res_forward_subs                      full
% 0.78/1.05  --res_backward_subs                     full
% 0.78/1.05  --res_forward_subs_resolution           true
% 0.78/1.05  --res_backward_subs_resolution          true
% 0.78/1.05  --res_orphan_elimination                true
% 0.78/1.05  --res_time_limit                        2.
% 0.78/1.05  --res_out_proof                         true
% 0.78/1.05  
% 0.78/1.05  ------ Superposition Options
% 0.78/1.05  
% 0.78/1.05  --superposition_flag                    true
% 0.78/1.05  --sup_passive_queue_type                priority_queues
% 0.78/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.78/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.78/1.05  --demod_completeness_check              fast
% 0.78/1.05  --demod_use_ground                      true
% 0.78/1.05  --sup_to_prop_solver                    passive
% 0.78/1.05  --sup_prop_simpl_new                    true
% 0.78/1.05  --sup_prop_simpl_given                  true
% 0.78/1.05  --sup_fun_splitting                     false
% 0.78/1.05  --sup_smt_interval                      50000
% 0.78/1.05  
% 0.78/1.05  ------ Superposition Simplification Setup
% 0.78/1.05  
% 0.78/1.05  --sup_indices_passive                   []
% 0.78/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.78/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.05  --sup_full_bw                           [BwDemod]
% 0.78/1.05  --sup_immed_triv                        [TrivRules]
% 0.78/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.78/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.05  --sup_immed_bw_main                     []
% 0.78/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.78/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.78/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.78/1.05  
% 0.78/1.05  ------ Combination Options
% 0.78/1.05  
% 0.78/1.05  --comb_res_mult                         3
% 0.78/1.05  --comb_sup_mult                         2
% 0.78/1.05  --comb_inst_mult                        10
% 0.78/1.05  
% 0.78/1.05  ------ Debug Options
% 0.78/1.05  
% 0.78/1.05  --dbg_backtrace                         false
% 0.78/1.05  --dbg_dump_prop_clauses                 false
% 0.78/1.05  --dbg_dump_prop_clauses_file            -
% 0.78/1.05  --dbg_out_stat                          false
% 0.78/1.05  ------ Parsing...
% 0.78/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.78/1.05  
% 0.78/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.78/1.05  
% 0.78/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.78/1.05  
% 0.78/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.78/1.05  ------ Proving...
% 0.78/1.05  ------ Problem Properties 
% 0.78/1.05  
% 0.78/1.05  
% 0.78/1.05  clauses                                 14
% 0.78/1.05  conjectures                             2
% 0.78/1.05  EPR                                     1
% 0.78/1.05  Horn                                    10
% 0.78/1.05  unary                                   4
% 0.78/1.05  binary                                  6
% 0.78/1.05  lits                                    28
% 0.78/1.05  lits eq                                 18
% 0.78/1.05  fd_pure                                 0
% 0.78/1.05  fd_pseudo                               0
% 0.78/1.05  fd_cond                                 1
% 0.78/1.05  fd_pseudo_cond                          2
% 0.78/1.05  AC symbols                              0
% 0.78/1.05  
% 0.78/1.05  ------ Schedule dynamic 5 is on 
% 0.78/1.05  
% 0.78/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.78/1.05  
% 0.78/1.05  
% 0.78/1.05  ------ 
% 0.78/1.05  Current options:
% 0.78/1.05  ------ 
% 0.78/1.05  
% 0.78/1.05  ------ Input Options
% 0.78/1.05  
% 0.78/1.05  --out_options                           all
% 0.78/1.05  --tptp_safe_out                         true
% 0.78/1.05  --problem_path                          ""
% 0.78/1.05  --include_path                          ""
% 0.78/1.05  --clausifier                            res/vclausify_rel
% 0.78/1.05  --clausifier_options                    --mode clausify
% 0.78/1.05  --stdin                                 false
% 0.78/1.05  --stats_out                             all
% 0.78/1.05  
% 0.78/1.05  ------ General Options
% 0.78/1.05  
% 0.78/1.05  --fof                                   false
% 0.78/1.05  --time_out_real                         305.
% 0.78/1.05  --time_out_virtual                      -1.
% 0.78/1.05  --symbol_type_check                     false
% 0.78/1.05  --clausify_out                          false
% 0.78/1.05  --sig_cnt_out                           false
% 0.78/1.05  --trig_cnt_out                          false
% 0.78/1.05  --trig_cnt_out_tolerance                1.
% 0.78/1.05  --trig_cnt_out_sk_spl                   false
% 0.78/1.05  --abstr_cl_out                          false
% 0.78/1.05  
% 0.78/1.05  ------ Global Options
% 0.78/1.05  
% 0.78/1.05  --schedule                              default
% 0.78/1.05  --add_important_lit                     false
% 0.78/1.05  --prop_solver_per_cl                    1000
% 0.78/1.05  --min_unsat_core                        false
% 0.78/1.05  --soft_assumptions                      false
% 0.78/1.05  --soft_lemma_size                       3
% 0.78/1.05  --prop_impl_unit_size                   0
% 0.78/1.05  --prop_impl_unit                        []
% 0.78/1.05  --share_sel_clauses                     true
% 0.78/1.05  --reset_solvers                         false
% 0.78/1.05  --bc_imp_inh                            [conj_cone]
% 0.78/1.05  --conj_cone_tolerance                   3.
% 0.78/1.05  --extra_neg_conj                        none
% 0.78/1.05  --large_theory_mode                     true
% 0.78/1.05  --prolific_symb_bound                   200
% 0.78/1.05  --lt_threshold                          2000
% 0.78/1.05  --clause_weak_htbl                      true
% 0.78/1.05  --gc_record_bc_elim                     false
% 0.78/1.05  
% 0.78/1.05  ------ Preprocessing Options
% 0.78/1.05  
% 0.78/1.05  --preprocessing_flag                    true
% 0.78/1.05  --time_out_prep_mult                    0.1
% 0.78/1.05  --splitting_mode                        input
% 0.78/1.05  --splitting_grd                         true
% 0.78/1.05  --splitting_cvd                         false
% 0.78/1.05  --splitting_cvd_svl                     false
% 0.78/1.05  --splitting_nvd                         32
% 0.78/1.05  --sub_typing                            true
% 0.78/1.05  --prep_gs_sim                           true
% 0.78/1.05  --prep_unflatten                        true
% 0.78/1.05  --prep_res_sim                          true
% 0.78/1.05  --prep_upred                            true
% 0.78/1.05  --prep_sem_filter                       exhaustive
% 0.78/1.05  --prep_sem_filter_out                   false
% 0.78/1.05  --pred_elim                             true
% 0.78/1.05  --res_sim_input                         true
% 0.78/1.05  --eq_ax_congr_red                       true
% 0.78/1.05  --pure_diseq_elim                       true
% 0.78/1.05  --brand_transform                       false
% 0.78/1.05  --non_eq_to_eq                          false
% 0.78/1.05  --prep_def_merge                        true
% 0.78/1.05  --prep_def_merge_prop_impl              false
% 0.78/1.05  --prep_def_merge_mbd                    true
% 0.78/1.05  --prep_def_merge_tr_red                 false
% 0.78/1.05  --prep_def_merge_tr_cl                  false
% 0.78/1.05  --smt_preprocessing                     true
% 0.78/1.05  --smt_ac_axioms                         fast
% 0.78/1.05  --preprocessed_out                      false
% 0.78/1.05  --preprocessed_stats                    false
% 0.78/1.05  
% 0.78/1.05  ------ Abstraction refinement Options
% 0.78/1.05  
% 0.78/1.05  --abstr_ref                             []
% 0.78/1.05  --abstr_ref_prep                        false
% 0.78/1.05  --abstr_ref_until_sat                   false
% 0.78/1.05  --abstr_ref_sig_restrict                funpre
% 0.78/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.78/1.05  --abstr_ref_under                       []
% 0.78/1.05  
% 0.78/1.05  ------ SAT Options
% 0.78/1.05  
% 0.78/1.05  --sat_mode                              false
% 0.78/1.05  --sat_fm_restart_options                ""
% 0.78/1.05  --sat_gr_def                            false
% 0.78/1.05  --sat_epr_types                         true
% 0.78/1.05  --sat_non_cyclic_types                  false
% 0.78/1.05  --sat_finite_models                     false
% 0.78/1.05  --sat_fm_lemmas                         false
% 0.78/1.05  --sat_fm_prep                           false
% 0.78/1.05  --sat_fm_uc_incr                        true
% 0.78/1.05  --sat_out_model                         small
% 0.78/1.05  --sat_out_clauses                       false
% 0.78/1.05  
% 0.78/1.05  ------ QBF Options
% 0.78/1.05  
% 0.78/1.05  --qbf_mode                              false
% 0.78/1.05  --qbf_elim_univ                         false
% 0.78/1.05  --qbf_dom_inst                          none
% 0.78/1.05  --qbf_dom_pre_inst                      false
% 0.78/1.05  --qbf_sk_in                             false
% 0.78/1.05  --qbf_pred_elim                         true
% 0.78/1.05  --qbf_split                             512
% 0.78/1.05  
% 0.78/1.05  ------ BMC1 Options
% 0.78/1.05  
% 0.78/1.05  --bmc1_incremental                      false
% 0.78/1.05  --bmc1_axioms                           reachable_all
% 0.78/1.05  --bmc1_min_bound                        0
% 0.78/1.05  --bmc1_max_bound                        -1
% 0.78/1.05  --bmc1_max_bound_default                -1
% 0.78/1.05  --bmc1_symbol_reachability              true
% 0.78/1.05  --bmc1_property_lemmas                  false
% 0.78/1.05  --bmc1_k_induction                      false
% 0.78/1.05  --bmc1_non_equiv_states                 false
% 0.78/1.05  --bmc1_deadlock                         false
% 0.78/1.05  --bmc1_ucm                              false
% 0.78/1.05  --bmc1_add_unsat_core                   none
% 0.78/1.05  --bmc1_unsat_core_children              false
% 0.78/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.78/1.05  --bmc1_out_stat                         full
% 0.78/1.05  --bmc1_ground_init                      false
% 0.78/1.05  --bmc1_pre_inst_next_state              false
% 0.78/1.05  --bmc1_pre_inst_state                   false
% 0.78/1.05  --bmc1_pre_inst_reach_state             false
% 0.78/1.05  --bmc1_out_unsat_core                   false
% 0.78/1.05  --bmc1_aig_witness_out                  false
% 0.78/1.05  --bmc1_verbose                          false
% 0.78/1.05  --bmc1_dump_clauses_tptp                false
% 0.78/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.78/1.05  --bmc1_dump_file                        -
% 0.78/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.78/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.78/1.05  --bmc1_ucm_extend_mode                  1
% 0.78/1.05  --bmc1_ucm_init_mode                    2
% 0.78/1.05  --bmc1_ucm_cone_mode                    none
% 0.78/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.78/1.05  --bmc1_ucm_relax_model                  4
% 0.78/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.78/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.78/1.05  --bmc1_ucm_layered_model                none
% 0.78/1.05  --bmc1_ucm_max_lemma_size               10
% 0.78/1.05  
% 0.78/1.05  ------ AIG Options
% 0.78/1.05  
% 0.78/1.05  --aig_mode                              false
% 0.78/1.05  
% 0.78/1.05  ------ Instantiation Options
% 0.78/1.05  
% 0.78/1.05  --instantiation_flag                    true
% 0.78/1.05  --inst_sos_flag                         false
% 0.78/1.05  --inst_sos_phase                        true
% 0.78/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.78/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.78/1.05  --inst_lit_sel_side                     none
% 0.78/1.05  --inst_solver_per_active                1400
% 0.78/1.05  --inst_solver_calls_frac                1.
% 0.78/1.05  --inst_passive_queue_type               priority_queues
% 0.78/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.78/1.05  --inst_passive_queues_freq              [25;2]
% 0.78/1.05  --inst_dismatching                      true
% 0.78/1.05  --inst_eager_unprocessed_to_passive     true
% 0.78/1.05  --inst_prop_sim_given                   true
% 0.78/1.05  --inst_prop_sim_new                     false
% 0.78/1.05  --inst_subs_new                         false
% 0.78/1.05  --inst_eq_res_simp                      false
% 0.78/1.05  --inst_subs_given                       false
% 0.78/1.05  --inst_orphan_elimination               true
% 0.78/1.05  --inst_learning_loop_flag               true
% 0.78/1.05  --inst_learning_start                   3000
% 0.78/1.05  --inst_learning_factor                  2
% 0.78/1.05  --inst_start_prop_sim_after_learn       3
% 0.78/1.05  --inst_sel_renew                        solver
% 0.78/1.05  --inst_lit_activity_flag                true
% 0.78/1.05  --inst_restr_to_given                   false
% 0.78/1.05  --inst_activity_threshold               500
% 0.78/1.05  --inst_out_proof                        true
% 0.78/1.05  
% 0.78/1.05  ------ Resolution Options
% 0.78/1.05  
% 0.78/1.05  --resolution_flag                       false
% 0.78/1.05  --res_lit_sel                           adaptive
% 0.78/1.05  --res_lit_sel_side                      none
% 0.78/1.05  --res_ordering                          kbo
% 0.78/1.05  --res_to_prop_solver                    active
% 0.78/1.05  --res_prop_simpl_new                    false
% 0.78/1.05  --res_prop_simpl_given                  true
% 0.78/1.05  --res_passive_queue_type                priority_queues
% 0.78/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.78/1.05  --res_passive_queues_freq               [15;5]
% 0.78/1.05  --res_forward_subs                      full
% 0.78/1.05  --res_backward_subs                     full
% 0.78/1.05  --res_forward_subs_resolution           true
% 0.78/1.05  --res_backward_subs_resolution          true
% 0.78/1.05  --res_orphan_elimination                true
% 0.78/1.05  --res_time_limit                        2.
% 0.78/1.05  --res_out_proof                         true
% 0.78/1.05  
% 0.78/1.05  ------ Superposition Options
% 0.78/1.05  
% 0.78/1.05  --superposition_flag                    true
% 0.78/1.05  --sup_passive_queue_type                priority_queues
% 0.78/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.78/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.78/1.05  --demod_completeness_check              fast
% 0.78/1.05  --demod_use_ground                      true
% 0.78/1.05  --sup_to_prop_solver                    passive
% 0.78/1.05  --sup_prop_simpl_new                    true
% 0.78/1.05  --sup_prop_simpl_given                  true
% 0.78/1.05  --sup_fun_splitting                     false
% 0.78/1.05  --sup_smt_interval                      50000
% 0.78/1.05  
% 0.78/1.05  ------ Superposition Simplification Setup
% 0.78/1.05  
% 0.78/1.05  --sup_indices_passive                   []
% 0.78/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.78/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.05  --sup_full_bw                           [BwDemod]
% 0.78/1.05  --sup_immed_triv                        [TrivRules]
% 0.78/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.78/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.05  --sup_immed_bw_main                     []
% 0.78/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.78/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.78/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.78/1.05  
% 0.78/1.05  ------ Combination Options
% 0.78/1.05  
% 0.78/1.05  --comb_res_mult                         3
% 0.78/1.05  --comb_sup_mult                         2
% 0.78/1.05  --comb_inst_mult                        10
% 0.78/1.05  
% 0.78/1.05  ------ Debug Options
% 0.78/1.05  
% 0.78/1.05  --dbg_backtrace                         false
% 0.78/1.05  --dbg_dump_prop_clauses                 false
% 0.78/1.05  --dbg_dump_prop_clauses_file            -
% 0.78/1.05  --dbg_out_stat                          false
% 0.78/1.05  
% 0.78/1.05  
% 0.78/1.05  
% 0.78/1.05  
% 0.78/1.05  ------ Proving...
% 0.78/1.05  
% 0.78/1.05  
% 0.78/1.05  % SZS status Theorem for theBenchmark.p
% 0.78/1.05  
% 0.78/1.05   Resolution empty clause
% 0.78/1.05  
% 0.78/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.78/1.05  
% 0.78/1.05  fof(f6,axiom,(
% 0.78/1.05    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.78/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.78/1.05  
% 0.78/1.05  fof(f17,plain,(
% 0.78/1.05    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.78/1.05    inference(nnf_transformation,[],[f6])).
% 0.78/1.05  
% 0.78/1.05  fof(f33,plain,(
% 0.78/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.78/1.05    inference(cnf_transformation,[],[f17])).
% 0.78/1.05  
% 0.78/1.05  fof(f2,axiom,(
% 0.78/1.05    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.78/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.78/1.05  
% 0.78/1.05  fof(f26,plain,(
% 0.78/1.05    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.78/1.05    inference(cnf_transformation,[],[f2])).
% 0.78/1.05  
% 0.78/1.05  fof(f3,axiom,(
% 0.78/1.05    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.78/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.78/1.05  
% 0.78/1.05  fof(f27,plain,(
% 0.78/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.78/1.05    inference(cnf_transformation,[],[f3])).
% 0.78/1.05  
% 0.78/1.05  fof(f4,axiom,(
% 0.78/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.78/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.78/1.05  
% 0.78/1.05  fof(f28,plain,(
% 0.78/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.78/1.05    inference(cnf_transformation,[],[f4])).
% 0.78/1.05  
% 0.78/1.05  fof(f39,plain,(
% 0.78/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.78/1.05    inference(definition_unfolding,[],[f27,f28])).
% 0.78/1.05  
% 0.78/1.05  fof(f40,plain,(
% 0.78/1.05    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.78/1.05    inference(definition_unfolding,[],[f26,f39])).
% 0.78/1.05  
% 0.78/1.05  fof(f45,plain,(
% 0.78/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.78/1.05    inference(definition_unfolding,[],[f33,f40])).
% 0.78/1.05  
% 0.78/1.05  fof(f8,conjecture,(
% 0.78/1.05    ! [X0,X1] : (k1_xboole_0 != X0 => (k2_zfmisc_1(X0,k1_tarski(X1)) != k1_xboole_0 & k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0))),
% 0.78/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.78/1.05  
% 0.78/1.05  fof(f9,negated_conjecture,(
% 0.78/1.05    ~! [X0,X1] : (k1_xboole_0 != X0 => (k2_zfmisc_1(X0,k1_tarski(X1)) != k1_xboole_0 & k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0))),
% 0.78/1.05    inference(negated_conjecture,[],[f8])).
% 0.78/1.05  
% 0.78/1.05  fof(f10,plain,(
% 0.78/1.05    ? [X0,X1] : ((k2_zfmisc_1(X0,k1_tarski(X1)) = k1_xboole_0 | k2_zfmisc_1(k1_tarski(X1),X0) = k1_xboole_0) & k1_xboole_0 != X0)),
% 0.78/1.05    inference(ennf_transformation,[],[f9])).
% 0.78/1.05  
% 0.78/1.05  fof(f20,plain,(
% 0.78/1.05    ? [X0,X1] : ((k2_zfmisc_1(X0,k1_tarski(X1)) = k1_xboole_0 | k2_zfmisc_1(k1_tarski(X1),X0) = k1_xboole_0) & k1_xboole_0 != X0) => ((k2_zfmisc_1(sK1,k1_tarski(sK2)) = k1_xboole_0 | k2_zfmisc_1(k1_tarski(sK2),sK1) = k1_xboole_0) & k1_xboole_0 != sK1)),
% 0.78/1.05    introduced(choice_axiom,[])).
% 0.78/1.05  
% 0.78/1.05  fof(f21,plain,(
% 0.78/1.05    (k2_zfmisc_1(sK1,k1_tarski(sK2)) = k1_xboole_0 | k2_zfmisc_1(k1_tarski(sK2),sK1) = k1_xboole_0) & k1_xboole_0 != sK1),
% 0.78/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f20])).
% 0.78/1.05  
% 0.78/1.05  fof(f38,plain,(
% 0.78/1.05    k2_zfmisc_1(sK1,k1_tarski(sK2)) = k1_xboole_0 | k2_zfmisc_1(k1_tarski(sK2),sK1) = k1_xboole_0),
% 0.78/1.05    inference(cnf_transformation,[],[f21])).
% 0.78/1.05  
% 0.78/1.05  fof(f50,plain,(
% 0.78/1.05    k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 | k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) = k1_xboole_0),
% 0.78/1.05    inference(definition_unfolding,[],[f38,f40,f40])).
% 0.78/1.05  
% 0.78/1.05  fof(f5,axiom,(
% 0.78/1.05    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.78/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.78/1.05  
% 0.78/1.05  fof(f15,plain,(
% 0.78/1.05    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.78/1.05    inference(nnf_transformation,[],[f5])).
% 0.78/1.05  
% 0.78/1.05  fof(f16,plain,(
% 0.78/1.05    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.78/1.05    inference(flattening,[],[f15])).
% 0.78/1.05  
% 0.78/1.05  fof(f29,plain,(
% 0.78/1.05    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 0.78/1.05    inference(cnf_transformation,[],[f16])).
% 0.78/1.05  
% 0.78/1.05  fof(f37,plain,(
% 0.78/1.05    k1_xboole_0 != sK1),
% 0.78/1.05    inference(cnf_transformation,[],[f21])).
% 0.78/1.05  
% 0.78/1.05  fof(f30,plain,(
% 0.78/1.05    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.78/1.05    inference(cnf_transformation,[],[f16])).
% 0.78/1.05  
% 0.78/1.05  fof(f55,plain,(
% 0.78/1.05    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 0.78/1.05    inference(equality_resolution,[],[f30])).
% 0.78/1.05  
% 0.78/1.05  fof(f1,axiom,(
% 0.78/1.05    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.78/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.78/1.05  
% 0.78/1.05  fof(f11,plain,(
% 0.78/1.05    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.78/1.05    inference(nnf_transformation,[],[f1])).
% 0.78/1.05  
% 0.78/1.05  fof(f12,plain,(
% 0.78/1.05    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.78/1.05    inference(rectify,[],[f11])).
% 0.78/1.05  
% 0.78/1.05  fof(f13,plain,(
% 0.78/1.05    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 0.78/1.05    introduced(choice_axiom,[])).
% 0.78/1.05  
% 0.78/1.05  fof(f14,plain,(
% 0.78/1.05    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.78/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 0.78/1.05  
% 0.78/1.05  fof(f22,plain,(
% 0.78/1.05    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.78/1.05    inference(cnf_transformation,[],[f14])).
% 0.78/1.05  
% 0.78/1.05  fof(f44,plain,(
% 0.78/1.05    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.78/1.05    inference(definition_unfolding,[],[f22,f40])).
% 0.78/1.05  
% 0.78/1.05  fof(f53,plain,(
% 0.78/1.05    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 0.78/1.05    inference(equality_resolution,[],[f44])).
% 0.78/1.05  
% 0.78/1.05  fof(f7,axiom,(
% 0.78/1.05    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.78/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.78/1.05  
% 0.78/1.05  fof(f18,plain,(
% 0.78/1.05    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.78/1.05    inference(nnf_transformation,[],[f7])).
% 0.78/1.05  
% 0.78/1.05  fof(f19,plain,(
% 0.78/1.05    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.78/1.05    inference(flattening,[],[f18])).
% 0.78/1.05  
% 0.78/1.05  fof(f35,plain,(
% 0.78/1.05    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.78/1.05    inference(cnf_transformation,[],[f19])).
% 0.78/1.05  
% 0.78/1.05  fof(f48,plain,(
% 0.78/1.05    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 0.78/1.05    inference(definition_unfolding,[],[f35,f39])).
% 0.78/1.05  
% 0.78/1.05  fof(f23,plain,(
% 0.78/1.05    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.78/1.05    inference(cnf_transformation,[],[f14])).
% 0.78/1.05  
% 0.78/1.05  fof(f43,plain,(
% 0.78/1.05    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.78/1.05    inference(definition_unfolding,[],[f23,f40])).
% 0.78/1.05  
% 0.78/1.05  fof(f51,plain,(
% 0.78/1.05    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 0.78/1.05    inference(equality_resolution,[],[f43])).
% 0.78/1.05  
% 0.78/1.05  fof(f52,plain,(
% 0.78/1.05    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 0.78/1.05    inference(equality_resolution,[],[f51])).
% 0.78/1.05  
% 0.78/1.05  fof(f32,plain,(
% 0.78/1.05    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.78/1.05    inference(cnf_transformation,[],[f17])).
% 0.78/1.05  
% 0.78/1.05  fof(f46,plain,(
% 0.78/1.05    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0) )),
% 0.78/1.05    inference(definition_unfolding,[],[f32,f40])).
% 0.78/1.05  
% 0.78/1.05  cnf(c_7,plain,
% 0.78/1.05      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 0.78/1.05      inference(cnf_transformation,[],[f45]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_399,plain,
% 0.78/1.05      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 0.78/1.05      | r2_hidden(X1,X0) = iProver_top ),
% 0.78/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_12,negated_conjecture,
% 0.78/1.05      ( k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) = k1_xboole_0
% 0.78/1.05      | k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 0.78/1.05      inference(cnf_transformation,[],[f50]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_6,plain,
% 0.78/1.05      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 0.78/1.05      | k1_xboole_0 = X1
% 0.78/1.05      | k1_xboole_0 = X0 ),
% 0.78/1.05      inference(cnf_transformation,[],[f29]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_832,plain,
% 0.78/1.05      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 0.78/1.05      | k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0
% 0.78/1.05      | sK1 = k1_xboole_0 ),
% 0.78/1.05      inference(superposition,[status(thm)],[c_12,c_6]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_13,negated_conjecture,
% 0.78/1.05      ( k1_xboole_0 != sK1 ),
% 0.78/1.05      inference(cnf_transformation,[],[f37]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_27,plain,
% 0.78/1.05      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 0.78/1.05      | k1_xboole_0 = k1_xboole_0 ),
% 0.78/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_5,plain,
% 0.78/1.05      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.78/1.05      inference(cnf_transformation,[],[f55]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_28,plain,
% 0.78/1.05      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 0.78/1.05      inference(instantiation,[status(thm)],[c_5]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_148,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_480,plain,
% 0.78/1.05      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 0.78/1.05      inference(instantiation,[status(thm)],[c_148]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_481,plain,
% 0.78/1.05      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 0.78/1.05      inference(instantiation,[status(thm)],[c_480]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_958,plain,
% 0.78/1.05      ( k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0
% 0.78/1.05      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 0.78/1.05      inference(global_propositional_subsumption,
% 0.78/1.05                [status(thm)],
% 0.78/1.05                [c_832,c_13,c_27,c_28,c_481]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_959,plain,
% 0.78/1.05      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 0.78/1.05      | k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 0.78/1.05      inference(renaming,[status(thm)],[c_958]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_962,plain,
% 0.78/1.05      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 0.78/1.05      inference(superposition,[status(thm)],[c_959,c_6]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_963,plain,
% 0.78/1.05      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 0.78/1.05      inference(global_propositional_subsumption,
% 0.78/1.05                [status(thm)],
% 0.78/1.05                [c_962,c_13,c_27,c_28,c_481]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_3,plain,
% 0.78/1.05      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 0.78/1.05      inference(cnf_transformation,[],[f53]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_400,plain,
% 0.78/1.05      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 0.78/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_970,plain,
% 0.78/1.05      ( sK2 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.78/1.05      inference(superposition,[status(thm)],[c_963,c_400]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1102,plain,
% 0.78/1.05      ( k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 0.78/1.05      | sK2 = X0 ),
% 0.78/1.05      inference(superposition,[status(thm)],[c_399,c_970]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_10,plain,
% 0.78/1.05      ( r2_hidden(X0,X1)
% 0.78/1.05      | k4_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) != k1_xboole_0 ),
% 0.78/1.05      inference(cnf_transformation,[],[f48]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_396,plain,
% 0.78/1.05      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k1_xboole_0
% 0.78/1.05      | r2_hidden(X1,X2) = iProver_top ),
% 0.78/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_971,plain,
% 0.78/1.05      ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 0.78/1.05      | r2_hidden(sK2,X0) = iProver_top ),
% 0.78/1.05      inference(superposition,[status(thm)],[c_963,c_396]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1381,plain,
% 0.78/1.05      ( sK2 = X0 | r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 0.78/1.05      inference(superposition,[status(thm)],[c_1102,c_971]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1392,plain,
% 0.78/1.05      ( sK2 = X0 ),
% 0.78/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_1381,c_400]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_2,plain,
% 0.78/1.05      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 0.78/1.05      inference(cnf_transformation,[],[f52]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_401,plain,
% 0.78/1.05      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 0.78/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1396,plain,
% 0.78/1.05      ( r2_hidden(X0,sK2) = iProver_top ),
% 0.78/1.05      inference(demodulation,[status(thm)],[c_1392,c_401]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1399,plain,
% 0.78/1.05      ( X0 = X1 | r2_hidden(X1,sK2) != iProver_top ),
% 0.78/1.05      inference(demodulation,[status(thm)],[c_1392,c_400]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1437,plain,
% 0.78/1.05      ( X0 = X1 ),
% 0.78/1.05      inference(backward_subsumption_resolution,[status(thm)],[c_1396,c_1399]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_8,plain,
% 0.78/1.05      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
% 0.78/1.05      inference(cnf_transformation,[],[f46]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_398,plain,
% 0.78/1.05      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
% 0.78/1.05      | r2_hidden(X1,X0) != iProver_top ),
% 0.78/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1397,plain,
% 0.78/1.05      ( k4_xboole_0(X0,sK2) != X0 | r2_hidden(X1,X0) != iProver_top ),
% 0.78/1.05      inference(demodulation,[status(thm)],[c_1392,c_398]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1439,plain,
% 0.78/1.05      ( X0 != X0 | r2_hidden(X1,X0) != iProver_top ),
% 0.78/1.05      inference(demodulation,[status(thm)],[c_1437,c_1397]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1449,plain,
% 0.78/1.05      ( r2_hidden(X0,X1) != iProver_top ),
% 0.78/1.05      inference(equality_resolution_simp,[status(thm)],[c_1439]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1401,plain,
% 0.78/1.05      ( k4_xboole_0(sK2,X0) != k1_xboole_0 | r2_hidden(X1,X0) = iProver_top ),
% 0.78/1.05      inference(demodulation,[status(thm)],[c_1392,c_396]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1441,plain,
% 0.78/1.05      ( k1_xboole_0 != X0 | r2_hidden(X1,X0) = iProver_top ),
% 0.78/1.05      inference(demodulation,[status(thm)],[c_1437,c_1401]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1447,plain,
% 0.78/1.05      ( r2_hidden(X0,X1) = iProver_top ),
% 0.78/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_1441,c_1437]) ).
% 0.78/1.05  
% 0.78/1.05  cnf(c_1451,plain,
% 0.78/1.05      ( $false ),
% 0.78/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_1449,c_1447]) ).
% 0.78/1.05  
% 0.78/1.05  
% 0.78/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.78/1.05  
% 0.78/1.05  ------                               Statistics
% 0.78/1.05  
% 0.78/1.05  ------ General
% 0.78/1.05  
% 0.78/1.05  abstr_ref_over_cycles:                  0
% 0.78/1.05  abstr_ref_under_cycles:                 0
% 0.78/1.05  gc_basic_clause_elim:                   0
% 0.78/1.05  forced_gc_time:                         0
% 0.78/1.05  parsing_time:                           0.014
% 0.78/1.05  unif_index_cands_time:                  0.
% 0.78/1.05  unif_index_add_time:                    0.
% 0.78/1.05  orderings_time:                         0.
% 0.78/1.05  out_proof_time:                         0.006
% 0.78/1.05  total_time:                             0.134
% 0.78/1.05  num_of_symbols:                         39
% 0.78/1.05  num_of_terms:                           1708
% 0.78/1.05  
% 0.78/1.05  ------ Preprocessing
% 0.78/1.05  
% 0.78/1.05  num_of_splits:                          0
% 0.78/1.05  num_of_split_atoms:                     0
% 0.78/1.05  num_of_reused_defs:                     0
% 0.78/1.05  num_eq_ax_congr_red:                    4
% 0.78/1.05  num_of_sem_filtered_clauses:            1
% 0.78/1.05  num_of_subtypes:                        0
% 0.78/1.05  monotx_restored_types:                  0
% 0.78/1.05  sat_num_of_epr_types:                   0
% 0.78/1.05  sat_num_of_non_cyclic_types:            0
% 0.78/1.05  sat_guarded_non_collapsed_types:        0
% 0.78/1.05  num_pure_diseq_elim:                    0
% 0.78/1.05  simp_replaced_by:                       0
% 0.78/1.05  res_preprocessed:                       55
% 0.78/1.05  prep_upred:                             0
% 0.78/1.05  prep_unflattend:                        0
% 0.78/1.05  smt_new_axioms:                         0
% 0.78/1.05  pred_elim_cands:                        1
% 0.78/1.05  pred_elim:                              0
% 0.78/1.05  pred_elim_cl:                           0
% 0.78/1.05  pred_elim_cycles:                       1
% 0.78/1.05  merged_defs:                            6
% 0.78/1.05  merged_defs_ncl:                        0
% 0.78/1.05  bin_hyper_res:                          6
% 0.78/1.05  prep_cycles:                            3
% 0.78/1.05  pred_elim_time:                         0.
% 0.78/1.05  splitting_time:                         0.
% 0.78/1.05  sem_filter_time:                        0.
% 0.78/1.05  monotx_time:                            0.
% 0.78/1.05  subtype_inf_time:                       0.
% 0.78/1.05  
% 0.78/1.05  ------ Problem properties
% 0.78/1.05  
% 0.78/1.05  clauses:                                14
% 0.78/1.05  conjectures:                            2
% 0.78/1.05  epr:                                    1
% 0.78/1.05  horn:                                   10
% 0.78/1.05  ground:                                 2
% 0.78/1.05  unary:                                  4
% 0.78/1.05  binary:                                 6
% 0.78/1.05  lits:                                   28
% 0.78/1.05  lits_eq:                                18
% 0.78/1.05  fd_pure:                                0
% 0.78/1.05  fd_pseudo:                              0
% 0.78/1.05  fd_cond:                                1
% 0.78/1.05  fd_pseudo_cond:                         2
% 0.78/1.05  ac_symbols:                             0
% 0.78/1.05  
% 0.78/1.05  ------ Propositional Solver
% 0.78/1.05  
% 0.78/1.05  prop_solver_calls:                      21
% 0.78/1.05  prop_fast_solver_calls:                 288
% 0.78/1.05  smt_solver_calls:                       0
% 0.78/1.05  smt_fast_solver_calls:                  0
% 0.78/1.05  prop_num_of_clauses:                    508
% 0.78/1.05  prop_preprocess_simplified:             2152
% 0.78/1.05  prop_fo_subsumed:                       2
% 0.78/1.06  prop_solver_time:                       0.
% 0.78/1.06  smt_solver_time:                        0.
% 0.78/1.06  smt_fast_solver_time:                   0.
% 0.78/1.06  prop_fast_solver_time:                  0.
% 0.78/1.06  prop_unsat_core_time:                   0.
% 0.78/1.06  
% 0.78/1.06  ------ QBF
% 0.78/1.06  
% 0.78/1.06  qbf_q_res:                              0
% 0.78/1.06  qbf_num_tautologies:                    0
% 0.78/1.06  qbf_prep_cycles:                        0
% 0.78/1.06  
% 0.78/1.06  ------ BMC1
% 0.78/1.06  
% 0.78/1.06  bmc1_current_bound:                     -1
% 0.78/1.06  bmc1_last_solved_bound:                 -1
% 0.78/1.06  bmc1_unsat_core_size:                   -1
% 0.78/1.06  bmc1_unsat_core_parents_size:           -1
% 0.78/1.06  bmc1_merge_next_fun:                    0
% 0.78/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.78/1.06  
% 0.78/1.06  ------ Instantiation
% 0.78/1.06  
% 0.78/1.06  inst_num_of_clauses:                    184
% 0.78/1.06  inst_num_in_passive:                    13
% 0.78/1.06  inst_num_in_active:                     85
% 0.78/1.06  inst_num_in_unprocessed:                86
% 0.78/1.06  inst_num_of_loops:                      100
% 0.78/1.06  inst_num_of_learning_restarts:          0
% 0.78/1.06  inst_num_moves_active_passive:          14
% 0.78/1.06  inst_lit_activity:                      0
% 0.78/1.06  inst_lit_activity_moves:                0
% 0.78/1.06  inst_num_tautologies:                   0
% 0.78/1.06  inst_num_prop_implied:                  0
% 0.78/1.06  inst_num_existing_simplified:           0
% 0.78/1.06  inst_num_eq_res_simplified:             0
% 0.78/1.06  inst_num_child_elim:                    0
% 0.78/1.06  inst_num_of_dismatching_blockings:      67
% 0.78/1.06  inst_num_of_non_proper_insts:           153
% 0.78/1.06  inst_num_of_duplicates:                 0
% 0.78/1.06  inst_inst_num_from_inst_to_res:         0
% 0.78/1.06  inst_dismatching_checking_time:         0.
% 0.78/1.06  
% 0.78/1.06  ------ Resolution
% 0.78/1.06  
% 0.78/1.06  res_num_of_clauses:                     0
% 0.78/1.06  res_num_in_passive:                     0
% 0.78/1.06  res_num_in_active:                      0
% 0.78/1.06  res_num_of_loops:                       58
% 0.78/1.06  res_forward_subset_subsumed:            14
% 0.78/1.06  res_backward_subset_subsumed:           0
% 0.78/1.06  res_forward_subsumed:                   0
% 0.78/1.06  res_backward_subsumed:                  0
% 0.78/1.06  res_forward_subsumption_resolution:     0
% 0.78/1.06  res_backward_subsumption_resolution:    0
% 0.78/1.06  res_clause_to_clause_subsumption:       87
% 0.78/1.06  res_orphan_elimination:                 0
% 0.78/1.06  res_tautology_del:                      26
% 0.78/1.06  res_num_eq_res_simplified:              0
% 0.78/1.06  res_num_sel_changes:                    0
% 0.78/1.06  res_moves_from_active_to_pass:          0
% 0.78/1.06  
% 0.78/1.06  ------ Superposition
% 0.78/1.06  
% 0.78/1.06  sup_time_total:                         0.
% 0.78/1.06  sup_time_generating:                    0.
% 0.78/1.06  sup_time_sim_full:                      0.
% 0.78/1.06  sup_time_sim_immed:                     0.
% 0.78/1.06  
% 0.78/1.06  sup_num_of_clauses:                     12
% 0.78/1.06  sup_num_in_active:                      5
% 0.78/1.06  sup_num_in_passive:                     7
% 0.78/1.06  sup_num_of_loops:                       19
% 0.78/1.06  sup_fw_superposition:                   8
% 0.78/1.06  sup_bw_superposition:                   10
% 0.78/1.06  sup_immediate_simplified:               1
% 0.78/1.06  sup_given_eliminated:                   0
% 0.78/1.06  comparisons_done:                       0
% 0.78/1.06  comparisons_avoided:                    3
% 0.78/1.06  
% 0.78/1.06  ------ Simplifications
% 0.78/1.06  
% 0.78/1.06  
% 0.78/1.06  sim_fw_subset_subsumed:                 0
% 0.78/1.06  sim_bw_subset_subsumed:                 2
% 0.78/1.06  sim_fw_subsumed:                        0
% 0.78/1.06  sim_bw_subsumed:                        2
% 0.78/1.06  sim_fw_subsumption_res:                 3
% 0.78/1.06  sim_bw_subsumption_res:                 3
% 0.78/1.06  sim_tautology_del:                      0
% 0.78/1.06  sim_eq_tautology_del:                   6
% 0.78/1.06  sim_eq_res_simp:                        1
% 0.78/1.06  sim_fw_demodulated:                     1
% 0.78/1.06  sim_bw_demodulated:                     15
% 0.78/1.06  sim_light_normalised:                   0
% 0.78/1.06  sim_joinable_taut:                      0
% 0.78/1.06  sim_joinable_simp:                      0
% 0.78/1.06  sim_ac_normalised:                      0
% 0.78/1.06  sim_smt_subsumption:                    0
% 0.78/1.06  
%------------------------------------------------------------------------------
