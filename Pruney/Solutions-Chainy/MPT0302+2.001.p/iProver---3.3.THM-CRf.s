%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:03 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 386 expanded)
%              Number of clauses        :   69 ( 159 expanded)
%              Number of leaves         :   16 (  88 expanded)
%              Depth                    :   26
%              Number of atoms          :  230 ( 903 expanded)
%              Number of equality atoms :  150 ( 573 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f41])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f44])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f31,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f32,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f31])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK4 != sK5
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( sK4 != sK5
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f46])).

fof(f78,plain,(
    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f80,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_860,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_853,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_848,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25,negated_conjecture,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_847,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2679,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_847])).

cnf(c_3682,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_2679])).

cnf(c_4788,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_3682])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_454,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_468,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_455,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_892,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_893,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_4793,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4788,c_24,c_468,c_893])).

cnf(c_9828,plain,
    ( r2_hidden(sK0(sK5,X0),sK4) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_4793])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_861,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_19925,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_9828,c_861])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_852,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_20935,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19925,c_852])).

cnf(c_21513,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_20935])).

cnf(c_4799,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_4793])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_887,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_888,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_4957,plain,
    ( r2_hidden(sK3(sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4799,c_23,c_468,c_888])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_846,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1293,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_846])).

cnf(c_3681,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_1293])).

cnf(c_4961,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK3(sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4957,c_3681])).

cnf(c_884,plain,
    ( r2_hidden(sK3(sK5),sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_885,plain,
    ( k1_xboole_0 = sK5
    | r2_hidden(sK3(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_884])).

cnf(c_4982,plain,
    ( r2_hidden(sK3(sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4961,c_23,c_885])).

cnf(c_9827,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK0(sK4,X1),sK5) = iProver_top
    | r1_tarski(sK4,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_3681])).

cnf(c_10311,plain,
    ( r2_hidden(sK0(sK4,X0),sK5) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4982,c_9827])).

cnf(c_19924,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_10311,c_861])).

cnf(c_20243,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19924,c_852])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_879,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_16,c_1])).

cnf(c_17,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1300,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_17,c_16])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1191,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_14,c_1])).

cnf(c_1304,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1300,c_1191])).

cnf(c_1944,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_1304])).

cnf(c_4386,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_879,c_1944])).

cnf(c_21001,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_20243,c_4386])).

cnf(c_21035,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = k3_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_21001,c_14])).

cnf(c_2373,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1304,c_1944])).

cnf(c_21036,plain,
    ( k3_xboole_0(sK4,sK5) = sK4 ),
    inference(demodulation,[status(thm)],[c_21035,c_2373])).

cnf(c_21723,plain,
    ( k5_xboole_0(sK5,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21513,c_21036])).

cnf(c_878,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_16,c_1])).

cnf(c_4314,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_878,c_1944])).

cnf(c_22088,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK4),k5_xboole_0(X0,k1_xboole_0)) = sK5 ),
    inference(superposition,[status(thm)],[c_21723,c_4314])).

cnf(c_22092,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK4),X0) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_22088,c_14])).

cnf(c_2378,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1944,c_1944])).

cnf(c_22093,plain,
    ( sK5 = sK4 ),
    inference(demodulation,[status(thm)],[c_22092,c_2378])).

cnf(c_22,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_22984,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_22093,c_22])).

cnf(c_22985,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22984])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.37/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/1.49  
% 7.37/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.37/1.49  
% 7.37/1.49  ------  iProver source info
% 7.37/1.49  
% 7.37/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.37/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.37/1.49  git: non_committed_changes: false
% 7.37/1.49  git: last_make_outside_of_git: false
% 7.37/1.49  
% 7.37/1.49  ------ 
% 7.37/1.49  
% 7.37/1.49  ------ Input Options
% 7.37/1.49  
% 7.37/1.49  --out_options                           all
% 7.37/1.49  --tptp_safe_out                         true
% 7.37/1.49  --problem_path                          ""
% 7.37/1.49  --include_path                          ""
% 7.37/1.49  --clausifier                            res/vclausify_rel
% 7.37/1.49  --clausifier_options                    ""
% 7.37/1.49  --stdin                                 false
% 7.37/1.49  --stats_out                             all
% 7.37/1.49  
% 7.37/1.49  ------ General Options
% 7.37/1.49  
% 7.37/1.49  --fof                                   false
% 7.37/1.49  --time_out_real                         305.
% 7.37/1.49  --time_out_virtual                      -1.
% 7.37/1.49  --symbol_type_check                     false
% 7.37/1.49  --clausify_out                          false
% 7.37/1.49  --sig_cnt_out                           false
% 7.37/1.49  --trig_cnt_out                          false
% 7.37/1.49  --trig_cnt_out_tolerance                1.
% 7.37/1.49  --trig_cnt_out_sk_spl                   false
% 7.37/1.49  --abstr_cl_out                          false
% 7.37/1.49  
% 7.37/1.49  ------ Global Options
% 7.37/1.49  
% 7.37/1.49  --schedule                              default
% 7.37/1.49  --add_important_lit                     false
% 7.37/1.49  --prop_solver_per_cl                    1000
% 7.37/1.49  --min_unsat_core                        false
% 7.37/1.49  --soft_assumptions                      false
% 7.37/1.49  --soft_lemma_size                       3
% 7.37/1.49  --prop_impl_unit_size                   0
% 7.37/1.49  --prop_impl_unit                        []
% 7.37/1.49  --share_sel_clauses                     true
% 7.37/1.49  --reset_solvers                         false
% 7.37/1.49  --bc_imp_inh                            [conj_cone]
% 7.37/1.49  --conj_cone_tolerance                   3.
% 7.37/1.49  --extra_neg_conj                        none
% 7.37/1.49  --large_theory_mode                     true
% 7.37/1.49  --prolific_symb_bound                   200
% 7.37/1.49  --lt_threshold                          2000
% 7.37/1.49  --clause_weak_htbl                      true
% 7.37/1.49  --gc_record_bc_elim                     false
% 7.37/1.49  
% 7.37/1.49  ------ Preprocessing Options
% 7.37/1.49  
% 7.37/1.49  --preprocessing_flag                    true
% 7.37/1.49  --time_out_prep_mult                    0.1
% 7.37/1.49  --splitting_mode                        input
% 7.37/1.49  --splitting_grd                         true
% 7.37/1.49  --splitting_cvd                         false
% 7.37/1.49  --splitting_cvd_svl                     false
% 7.37/1.49  --splitting_nvd                         32
% 7.37/1.49  --sub_typing                            true
% 7.37/1.49  --prep_gs_sim                           true
% 7.37/1.49  --prep_unflatten                        true
% 7.37/1.49  --prep_res_sim                          true
% 7.37/1.49  --prep_upred                            true
% 7.37/1.49  --prep_sem_filter                       exhaustive
% 7.37/1.49  --prep_sem_filter_out                   false
% 7.37/1.49  --pred_elim                             true
% 7.37/1.49  --res_sim_input                         true
% 7.37/1.49  --eq_ax_congr_red                       true
% 7.37/1.49  --pure_diseq_elim                       true
% 7.37/1.49  --brand_transform                       false
% 7.37/1.49  --non_eq_to_eq                          false
% 7.37/1.49  --prep_def_merge                        true
% 7.37/1.49  --prep_def_merge_prop_impl              false
% 7.37/1.49  --prep_def_merge_mbd                    true
% 7.37/1.49  --prep_def_merge_tr_red                 false
% 7.37/1.49  --prep_def_merge_tr_cl                  false
% 7.37/1.49  --smt_preprocessing                     true
% 7.37/1.49  --smt_ac_axioms                         fast
% 7.37/1.49  --preprocessed_out                      false
% 7.37/1.49  --preprocessed_stats                    false
% 7.37/1.49  
% 7.37/1.49  ------ Abstraction refinement Options
% 7.37/1.49  
% 7.37/1.49  --abstr_ref                             []
% 7.37/1.49  --abstr_ref_prep                        false
% 7.37/1.49  --abstr_ref_until_sat                   false
% 7.37/1.49  --abstr_ref_sig_restrict                funpre
% 7.37/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.49  --abstr_ref_under                       []
% 7.37/1.49  
% 7.37/1.49  ------ SAT Options
% 7.37/1.49  
% 7.37/1.49  --sat_mode                              false
% 7.37/1.49  --sat_fm_restart_options                ""
% 7.37/1.49  --sat_gr_def                            false
% 7.37/1.49  --sat_epr_types                         true
% 7.37/1.49  --sat_non_cyclic_types                  false
% 7.37/1.49  --sat_finite_models                     false
% 7.37/1.49  --sat_fm_lemmas                         false
% 7.37/1.49  --sat_fm_prep                           false
% 7.37/1.49  --sat_fm_uc_incr                        true
% 7.37/1.50  --sat_out_model                         small
% 7.37/1.50  --sat_out_clauses                       false
% 7.37/1.50  
% 7.37/1.50  ------ QBF Options
% 7.37/1.50  
% 7.37/1.50  --qbf_mode                              false
% 7.37/1.50  --qbf_elim_univ                         false
% 7.37/1.50  --qbf_dom_inst                          none
% 7.37/1.50  --qbf_dom_pre_inst                      false
% 7.37/1.50  --qbf_sk_in                             false
% 7.37/1.50  --qbf_pred_elim                         true
% 7.37/1.50  --qbf_split                             512
% 7.37/1.50  
% 7.37/1.50  ------ BMC1 Options
% 7.37/1.50  
% 7.37/1.50  --bmc1_incremental                      false
% 7.37/1.50  --bmc1_axioms                           reachable_all
% 7.37/1.50  --bmc1_min_bound                        0
% 7.37/1.50  --bmc1_max_bound                        -1
% 7.37/1.50  --bmc1_max_bound_default                -1
% 7.37/1.50  --bmc1_symbol_reachability              true
% 7.37/1.50  --bmc1_property_lemmas                  false
% 7.37/1.50  --bmc1_k_induction                      false
% 7.37/1.50  --bmc1_non_equiv_states                 false
% 7.37/1.50  --bmc1_deadlock                         false
% 7.37/1.50  --bmc1_ucm                              false
% 7.37/1.50  --bmc1_add_unsat_core                   none
% 7.37/1.50  --bmc1_unsat_core_children              false
% 7.37/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.50  --bmc1_out_stat                         full
% 7.37/1.50  --bmc1_ground_init                      false
% 7.37/1.50  --bmc1_pre_inst_next_state              false
% 7.37/1.50  --bmc1_pre_inst_state                   false
% 7.37/1.50  --bmc1_pre_inst_reach_state             false
% 7.37/1.50  --bmc1_out_unsat_core                   false
% 7.37/1.50  --bmc1_aig_witness_out                  false
% 7.37/1.50  --bmc1_verbose                          false
% 7.37/1.50  --bmc1_dump_clauses_tptp                false
% 7.37/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.50  --bmc1_dump_file                        -
% 7.37/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.50  --bmc1_ucm_extend_mode                  1
% 7.37/1.50  --bmc1_ucm_init_mode                    2
% 7.37/1.50  --bmc1_ucm_cone_mode                    none
% 7.37/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.50  --bmc1_ucm_relax_model                  4
% 7.37/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.50  --bmc1_ucm_layered_model                none
% 7.37/1.50  --bmc1_ucm_max_lemma_size               10
% 7.37/1.50  
% 7.37/1.50  ------ AIG Options
% 7.37/1.50  
% 7.37/1.50  --aig_mode                              false
% 7.37/1.50  
% 7.37/1.50  ------ Instantiation Options
% 7.37/1.50  
% 7.37/1.50  --instantiation_flag                    true
% 7.37/1.50  --inst_sos_flag                         true
% 7.37/1.50  --inst_sos_phase                        true
% 7.37/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.50  --inst_lit_sel_side                     num_symb
% 7.37/1.50  --inst_solver_per_active                1400
% 7.37/1.50  --inst_solver_calls_frac                1.
% 7.37/1.50  --inst_passive_queue_type               priority_queues
% 7.37/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.50  --inst_passive_queues_freq              [25;2]
% 7.37/1.50  --inst_dismatching                      true
% 7.37/1.50  --inst_eager_unprocessed_to_passive     true
% 7.37/1.50  --inst_prop_sim_given                   true
% 7.37/1.50  --inst_prop_sim_new                     false
% 7.37/1.50  --inst_subs_new                         false
% 7.37/1.50  --inst_eq_res_simp                      false
% 7.37/1.50  --inst_subs_given                       false
% 7.37/1.50  --inst_orphan_elimination               true
% 7.37/1.50  --inst_learning_loop_flag               true
% 7.37/1.50  --inst_learning_start                   3000
% 7.37/1.50  --inst_learning_factor                  2
% 7.37/1.50  --inst_start_prop_sim_after_learn       3
% 7.37/1.50  --inst_sel_renew                        solver
% 7.37/1.50  --inst_lit_activity_flag                true
% 7.37/1.50  --inst_restr_to_given                   false
% 7.37/1.50  --inst_activity_threshold               500
% 7.37/1.50  --inst_out_proof                        true
% 7.37/1.50  
% 7.37/1.50  ------ Resolution Options
% 7.37/1.50  
% 7.37/1.50  --resolution_flag                       true
% 7.37/1.50  --res_lit_sel                           adaptive
% 7.37/1.50  --res_lit_sel_side                      none
% 7.37/1.50  --res_ordering                          kbo
% 7.37/1.50  --res_to_prop_solver                    active
% 7.37/1.50  --res_prop_simpl_new                    false
% 7.37/1.50  --res_prop_simpl_given                  true
% 7.37/1.50  --res_passive_queue_type                priority_queues
% 7.37/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.50  --res_passive_queues_freq               [15;5]
% 7.37/1.50  --res_forward_subs                      full
% 7.37/1.50  --res_backward_subs                     full
% 7.37/1.50  --res_forward_subs_resolution           true
% 7.37/1.50  --res_backward_subs_resolution          true
% 7.37/1.50  --res_orphan_elimination                true
% 7.37/1.50  --res_time_limit                        2.
% 7.37/1.50  --res_out_proof                         true
% 7.37/1.50  
% 7.37/1.50  ------ Superposition Options
% 7.37/1.50  
% 7.37/1.50  --superposition_flag                    true
% 7.37/1.50  --sup_passive_queue_type                priority_queues
% 7.37/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.50  --demod_completeness_check              fast
% 7.37/1.50  --demod_use_ground                      true
% 7.37/1.50  --sup_to_prop_solver                    passive
% 7.37/1.50  --sup_prop_simpl_new                    true
% 7.37/1.50  --sup_prop_simpl_given                  true
% 7.37/1.50  --sup_fun_splitting                     true
% 7.37/1.50  --sup_smt_interval                      50000
% 7.37/1.50  
% 7.37/1.50  ------ Superposition Simplification Setup
% 7.37/1.50  
% 7.37/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.37/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.37/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.37/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.37/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.37/1.50  --sup_immed_triv                        [TrivRules]
% 7.37/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.50  --sup_immed_bw_main                     []
% 7.37/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.37/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.50  --sup_input_bw                          []
% 7.37/1.50  
% 7.37/1.50  ------ Combination Options
% 7.37/1.50  
% 7.37/1.50  --comb_res_mult                         3
% 7.37/1.50  --comb_sup_mult                         2
% 7.37/1.50  --comb_inst_mult                        10
% 7.37/1.50  
% 7.37/1.50  ------ Debug Options
% 7.37/1.50  
% 7.37/1.50  --dbg_backtrace                         false
% 7.37/1.50  --dbg_dump_prop_clauses                 false
% 7.37/1.50  --dbg_dump_prop_clauses_file            -
% 7.37/1.50  --dbg_out_stat                          false
% 7.37/1.50  ------ Parsing...
% 7.37/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.37/1.50  ------ Proving...
% 7.37/1.50  ------ Problem Properties 
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  clauses                                 26
% 7.37/1.50  conjectures                             4
% 7.37/1.50  EPR                                     5
% 7.37/1.50  Horn                                    21
% 7.37/1.50  unary                                   12
% 7.37/1.50  binary                                  11
% 7.37/1.50  lits                                    43
% 7.37/1.50  lits eq                                 13
% 7.37/1.50  fd_pure                                 0
% 7.37/1.50  fd_pseudo                               0
% 7.37/1.50  fd_cond                                 1
% 7.37/1.50  fd_pseudo_cond                          0
% 7.37/1.50  AC symbols                              1
% 7.37/1.50  
% 7.37/1.50  ------ Schedule dynamic 5 is on 
% 7.37/1.50  
% 7.37/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  ------ 
% 7.37/1.50  Current options:
% 7.37/1.50  ------ 
% 7.37/1.50  
% 7.37/1.50  ------ Input Options
% 7.37/1.50  
% 7.37/1.50  --out_options                           all
% 7.37/1.50  --tptp_safe_out                         true
% 7.37/1.50  --problem_path                          ""
% 7.37/1.50  --include_path                          ""
% 7.37/1.50  --clausifier                            res/vclausify_rel
% 7.37/1.50  --clausifier_options                    ""
% 7.37/1.50  --stdin                                 false
% 7.37/1.50  --stats_out                             all
% 7.37/1.50  
% 7.37/1.50  ------ General Options
% 7.37/1.50  
% 7.37/1.50  --fof                                   false
% 7.37/1.50  --time_out_real                         305.
% 7.37/1.50  --time_out_virtual                      -1.
% 7.37/1.50  --symbol_type_check                     false
% 7.37/1.50  --clausify_out                          false
% 7.37/1.50  --sig_cnt_out                           false
% 7.37/1.50  --trig_cnt_out                          false
% 7.37/1.50  --trig_cnt_out_tolerance                1.
% 7.37/1.50  --trig_cnt_out_sk_spl                   false
% 7.37/1.50  --abstr_cl_out                          false
% 7.37/1.50  
% 7.37/1.50  ------ Global Options
% 7.37/1.50  
% 7.37/1.50  --schedule                              default
% 7.37/1.50  --add_important_lit                     false
% 7.37/1.50  --prop_solver_per_cl                    1000
% 7.37/1.50  --min_unsat_core                        false
% 7.37/1.50  --soft_assumptions                      false
% 7.37/1.50  --soft_lemma_size                       3
% 7.37/1.50  --prop_impl_unit_size                   0
% 7.37/1.50  --prop_impl_unit                        []
% 7.37/1.50  --share_sel_clauses                     true
% 7.37/1.50  --reset_solvers                         false
% 7.37/1.50  --bc_imp_inh                            [conj_cone]
% 7.37/1.50  --conj_cone_tolerance                   3.
% 7.37/1.50  --extra_neg_conj                        none
% 7.37/1.50  --large_theory_mode                     true
% 7.37/1.50  --prolific_symb_bound                   200
% 7.37/1.50  --lt_threshold                          2000
% 7.37/1.50  --clause_weak_htbl                      true
% 7.37/1.50  --gc_record_bc_elim                     false
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing Options
% 7.37/1.50  
% 7.37/1.50  --preprocessing_flag                    true
% 7.37/1.50  --time_out_prep_mult                    0.1
% 7.37/1.50  --splitting_mode                        input
% 7.37/1.50  --splitting_grd                         true
% 7.37/1.50  --splitting_cvd                         false
% 7.37/1.50  --splitting_cvd_svl                     false
% 7.37/1.50  --splitting_nvd                         32
% 7.37/1.50  --sub_typing                            true
% 7.37/1.50  --prep_gs_sim                           true
% 7.37/1.50  --prep_unflatten                        true
% 7.37/1.50  --prep_res_sim                          true
% 7.37/1.50  --prep_upred                            true
% 7.37/1.50  --prep_sem_filter                       exhaustive
% 7.37/1.50  --prep_sem_filter_out                   false
% 7.37/1.50  --pred_elim                             true
% 7.37/1.50  --res_sim_input                         true
% 7.37/1.50  --eq_ax_congr_red                       true
% 7.37/1.50  --pure_diseq_elim                       true
% 7.37/1.50  --brand_transform                       false
% 7.37/1.50  --non_eq_to_eq                          false
% 7.37/1.50  --prep_def_merge                        true
% 7.37/1.50  --prep_def_merge_prop_impl              false
% 7.37/1.50  --prep_def_merge_mbd                    true
% 7.37/1.50  --prep_def_merge_tr_red                 false
% 7.37/1.50  --prep_def_merge_tr_cl                  false
% 7.37/1.50  --smt_preprocessing                     true
% 7.37/1.50  --smt_ac_axioms                         fast
% 7.37/1.50  --preprocessed_out                      false
% 7.37/1.50  --preprocessed_stats                    false
% 7.37/1.50  
% 7.37/1.50  ------ Abstraction refinement Options
% 7.37/1.50  
% 7.37/1.50  --abstr_ref                             []
% 7.37/1.50  --abstr_ref_prep                        false
% 7.37/1.50  --abstr_ref_until_sat                   false
% 7.37/1.50  --abstr_ref_sig_restrict                funpre
% 7.37/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.50  --abstr_ref_under                       []
% 7.37/1.50  
% 7.37/1.50  ------ SAT Options
% 7.37/1.50  
% 7.37/1.50  --sat_mode                              false
% 7.37/1.50  --sat_fm_restart_options                ""
% 7.37/1.50  --sat_gr_def                            false
% 7.37/1.50  --sat_epr_types                         true
% 7.37/1.50  --sat_non_cyclic_types                  false
% 7.37/1.50  --sat_finite_models                     false
% 7.37/1.50  --sat_fm_lemmas                         false
% 7.37/1.50  --sat_fm_prep                           false
% 7.37/1.50  --sat_fm_uc_incr                        true
% 7.37/1.50  --sat_out_model                         small
% 7.37/1.50  --sat_out_clauses                       false
% 7.37/1.50  
% 7.37/1.50  ------ QBF Options
% 7.37/1.50  
% 7.37/1.50  --qbf_mode                              false
% 7.37/1.50  --qbf_elim_univ                         false
% 7.37/1.50  --qbf_dom_inst                          none
% 7.37/1.50  --qbf_dom_pre_inst                      false
% 7.37/1.50  --qbf_sk_in                             false
% 7.37/1.50  --qbf_pred_elim                         true
% 7.37/1.50  --qbf_split                             512
% 7.37/1.50  
% 7.37/1.50  ------ BMC1 Options
% 7.37/1.50  
% 7.37/1.50  --bmc1_incremental                      false
% 7.37/1.50  --bmc1_axioms                           reachable_all
% 7.37/1.50  --bmc1_min_bound                        0
% 7.37/1.50  --bmc1_max_bound                        -1
% 7.37/1.50  --bmc1_max_bound_default                -1
% 7.37/1.50  --bmc1_symbol_reachability              true
% 7.37/1.50  --bmc1_property_lemmas                  false
% 7.37/1.50  --bmc1_k_induction                      false
% 7.37/1.50  --bmc1_non_equiv_states                 false
% 7.37/1.50  --bmc1_deadlock                         false
% 7.37/1.50  --bmc1_ucm                              false
% 7.37/1.50  --bmc1_add_unsat_core                   none
% 7.37/1.50  --bmc1_unsat_core_children              false
% 7.37/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.50  --bmc1_out_stat                         full
% 7.37/1.50  --bmc1_ground_init                      false
% 7.37/1.50  --bmc1_pre_inst_next_state              false
% 7.37/1.50  --bmc1_pre_inst_state                   false
% 7.37/1.50  --bmc1_pre_inst_reach_state             false
% 7.37/1.50  --bmc1_out_unsat_core                   false
% 7.37/1.50  --bmc1_aig_witness_out                  false
% 7.37/1.50  --bmc1_verbose                          false
% 7.37/1.50  --bmc1_dump_clauses_tptp                false
% 7.37/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.50  --bmc1_dump_file                        -
% 7.37/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.50  --bmc1_ucm_extend_mode                  1
% 7.37/1.50  --bmc1_ucm_init_mode                    2
% 7.37/1.50  --bmc1_ucm_cone_mode                    none
% 7.37/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.50  --bmc1_ucm_relax_model                  4
% 7.37/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.50  --bmc1_ucm_layered_model                none
% 7.37/1.50  --bmc1_ucm_max_lemma_size               10
% 7.37/1.50  
% 7.37/1.50  ------ AIG Options
% 7.37/1.50  
% 7.37/1.50  --aig_mode                              false
% 7.37/1.50  
% 7.37/1.50  ------ Instantiation Options
% 7.37/1.50  
% 7.37/1.50  --instantiation_flag                    true
% 7.37/1.50  --inst_sos_flag                         true
% 7.37/1.50  --inst_sos_phase                        true
% 7.37/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.50  --inst_lit_sel_side                     none
% 7.37/1.50  --inst_solver_per_active                1400
% 7.37/1.50  --inst_solver_calls_frac                1.
% 7.37/1.50  --inst_passive_queue_type               priority_queues
% 7.37/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.50  --inst_passive_queues_freq              [25;2]
% 7.37/1.50  --inst_dismatching                      true
% 7.37/1.50  --inst_eager_unprocessed_to_passive     true
% 7.37/1.50  --inst_prop_sim_given                   true
% 7.37/1.50  --inst_prop_sim_new                     false
% 7.37/1.50  --inst_subs_new                         false
% 7.37/1.50  --inst_eq_res_simp                      false
% 7.37/1.50  --inst_subs_given                       false
% 7.37/1.50  --inst_orphan_elimination               true
% 7.37/1.50  --inst_learning_loop_flag               true
% 7.37/1.50  --inst_learning_start                   3000
% 7.37/1.50  --inst_learning_factor                  2
% 7.37/1.50  --inst_start_prop_sim_after_learn       3
% 7.37/1.50  --inst_sel_renew                        solver
% 7.37/1.50  --inst_lit_activity_flag                true
% 7.37/1.50  --inst_restr_to_given                   false
% 7.37/1.50  --inst_activity_threshold               500
% 7.37/1.50  --inst_out_proof                        true
% 7.37/1.50  
% 7.37/1.50  ------ Resolution Options
% 7.37/1.50  
% 7.37/1.50  --resolution_flag                       false
% 7.37/1.50  --res_lit_sel                           adaptive
% 7.37/1.50  --res_lit_sel_side                      none
% 7.37/1.50  --res_ordering                          kbo
% 7.37/1.50  --res_to_prop_solver                    active
% 7.37/1.50  --res_prop_simpl_new                    false
% 7.37/1.50  --res_prop_simpl_given                  true
% 7.37/1.50  --res_passive_queue_type                priority_queues
% 7.37/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.50  --res_passive_queues_freq               [15;5]
% 7.37/1.50  --res_forward_subs                      full
% 7.37/1.50  --res_backward_subs                     full
% 7.37/1.50  --res_forward_subs_resolution           true
% 7.37/1.50  --res_backward_subs_resolution          true
% 7.37/1.50  --res_orphan_elimination                true
% 7.37/1.50  --res_time_limit                        2.
% 7.37/1.50  --res_out_proof                         true
% 7.37/1.50  
% 7.37/1.50  ------ Superposition Options
% 7.37/1.50  
% 7.37/1.50  --superposition_flag                    true
% 7.37/1.50  --sup_passive_queue_type                priority_queues
% 7.37/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.50  --demod_completeness_check              fast
% 7.37/1.50  --demod_use_ground                      true
% 7.37/1.50  --sup_to_prop_solver                    passive
% 7.37/1.50  --sup_prop_simpl_new                    true
% 7.37/1.50  --sup_prop_simpl_given                  true
% 7.37/1.50  --sup_fun_splitting                     true
% 7.37/1.50  --sup_smt_interval                      50000
% 7.37/1.50  
% 7.37/1.50  ------ Superposition Simplification Setup
% 7.37/1.50  
% 7.37/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.37/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.37/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.37/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.37/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.37/1.50  --sup_immed_triv                        [TrivRules]
% 7.37/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.50  --sup_immed_bw_main                     []
% 7.37/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.37/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.50  --sup_input_bw                          []
% 7.37/1.50  
% 7.37/1.50  ------ Combination Options
% 7.37/1.50  
% 7.37/1.50  --comb_res_mult                         3
% 7.37/1.50  --comb_sup_mult                         2
% 7.37/1.50  --comb_inst_mult                        10
% 7.37/1.50  
% 7.37/1.50  ------ Debug Options
% 7.37/1.50  
% 7.37/1.50  --dbg_backtrace                         false
% 7.37/1.50  --dbg_dump_prop_clauses                 false
% 7.37/1.50  --dbg_dump_prop_clauses_file            -
% 7.37/1.50  --dbg_out_stat                          false
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  ------ Proving...
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  % SZS status Theorem for theBenchmark.p
% 7.37/1.50  
% 7.37/1.50   Resolution empty clause
% 7.37/1.50  
% 7.37/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.37/1.50  
% 7.37/1.50  fof(f1,axiom,(
% 7.37/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f48,plain,(
% 7.37/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f1])).
% 7.37/1.50  
% 7.37/1.50  fof(f3,axiom,(
% 7.37/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f27,plain,(
% 7.37/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.37/1.50    inference(ennf_transformation,[],[f3])).
% 7.37/1.50  
% 7.37/1.50  fof(f33,plain,(
% 7.37/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.37/1.50    inference(nnf_transformation,[],[f27])).
% 7.37/1.50  
% 7.37/1.50  fof(f34,plain,(
% 7.37/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.37/1.50    inference(rectify,[],[f33])).
% 7.37/1.50  
% 7.37/1.50  fof(f35,plain,(
% 7.37/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.37/1.50    introduced(choice_axiom,[])).
% 7.37/1.50  
% 7.37/1.50  fof(f36,plain,(
% 7.37/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.37/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 7.37/1.50  
% 7.37/1.50  fof(f51,plain,(
% 7.37/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f36])).
% 7.37/1.50  
% 7.37/1.50  fof(f6,axiom,(
% 7.37/1.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f30,plain,(
% 7.37/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.37/1.50    inference(ennf_transformation,[],[f6])).
% 7.37/1.50  
% 7.37/1.50  fof(f41,plain,(
% 7.37/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 7.37/1.50    introduced(choice_axiom,[])).
% 7.37/1.50  
% 7.37/1.50  fof(f42,plain,(
% 7.37/1.50    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 7.37/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f41])).
% 7.37/1.50  
% 7.37/1.50  fof(f58,plain,(
% 7.37/1.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 7.37/1.50    inference(cnf_transformation,[],[f42])).
% 7.37/1.50  
% 7.37/1.50  fof(f22,axiom,(
% 7.37/1.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f44,plain,(
% 7.37/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.37/1.50    inference(nnf_transformation,[],[f22])).
% 7.37/1.50  
% 7.37/1.50  fof(f45,plain,(
% 7.37/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.37/1.50    inference(flattening,[],[f44])).
% 7.37/1.50  
% 7.37/1.50  fof(f77,plain,(
% 7.37/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f45])).
% 7.37/1.50  
% 7.37/1.50  fof(f23,conjecture,(
% 7.37/1.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f24,negated_conjecture,(
% 7.37/1.50    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.37/1.50    inference(negated_conjecture,[],[f23])).
% 7.37/1.50  
% 7.37/1.50  fof(f31,plain,(
% 7.37/1.50    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 7.37/1.50    inference(ennf_transformation,[],[f24])).
% 7.37/1.50  
% 7.37/1.50  fof(f32,plain,(
% 7.37/1.50    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 7.37/1.50    inference(flattening,[],[f31])).
% 7.37/1.50  
% 7.37/1.50  fof(f46,plain,(
% 7.37/1.50    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK4 != sK5 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK5,sK4))),
% 7.37/1.50    introduced(choice_axiom,[])).
% 7.37/1.50  
% 7.37/1.50  fof(f47,plain,(
% 7.37/1.50    sK4 != sK5 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK5,sK4)),
% 7.37/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f46])).
% 7.37/1.50  
% 7.37/1.50  fof(f78,plain,(
% 7.37/1.50    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK5,sK4)),
% 7.37/1.50    inference(cnf_transformation,[],[f47])).
% 7.37/1.50  
% 7.37/1.50  fof(f76,plain,(
% 7.37/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.37/1.50    inference(cnf_transformation,[],[f45])).
% 7.37/1.50  
% 7.37/1.50  fof(f79,plain,(
% 7.37/1.50    k1_xboole_0 != sK4),
% 7.37/1.50    inference(cnf_transformation,[],[f47])).
% 7.37/1.50  
% 7.37/1.50  fof(f52,plain,(
% 7.37/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f36])).
% 7.37/1.50  
% 7.37/1.50  fof(f7,axiom,(
% 7.37/1.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f43,plain,(
% 7.37/1.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.37/1.50    inference(nnf_transformation,[],[f7])).
% 7.37/1.50  
% 7.37/1.50  fof(f60,plain,(
% 7.37/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f43])).
% 7.37/1.50  
% 7.37/1.50  fof(f9,axiom,(
% 7.37/1.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f62,plain,(
% 7.37/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f9])).
% 7.37/1.50  
% 7.37/1.50  fof(f88,plain,(
% 7.37/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.37/1.50    inference(definition_unfolding,[],[f60,f62])).
% 7.37/1.50  
% 7.37/1.50  fof(f80,plain,(
% 7.37/1.50    k1_xboole_0 != sK5),
% 7.37/1.50    inference(cnf_transformation,[],[f47])).
% 7.37/1.50  
% 7.37/1.50  fof(f75,plain,(
% 7.37/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.37/1.50    inference(cnf_transformation,[],[f45])).
% 7.37/1.50  
% 7.37/1.50  fof(f12,axiom,(
% 7.37/1.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f65,plain,(
% 7.37/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f12])).
% 7.37/1.50  
% 7.37/1.50  fof(f2,axiom,(
% 7.37/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f49,plain,(
% 7.37/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f2])).
% 7.37/1.50  
% 7.37/1.50  fof(f13,axiom,(
% 7.37/1.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f66,plain,(
% 7.37/1.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.37/1.50    inference(cnf_transformation,[],[f13])).
% 7.37/1.50  
% 7.37/1.50  fof(f10,axiom,(
% 7.37/1.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.37/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f63,plain,(
% 7.37/1.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.37/1.50    inference(cnf_transformation,[],[f10])).
% 7.37/1.50  
% 7.37/1.50  fof(f81,plain,(
% 7.37/1.50    sK4 != sK5),
% 7.37/1.50    inference(cnf_transformation,[],[f47])).
% 7.37/1.50  
% 7.37/1.50  cnf(c_0,plain,
% 7.37/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.37/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_3,plain,
% 7.37/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.37/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_860,plain,
% 7.37/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.37/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_10,plain,
% 7.37/1.50      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 7.37/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_853,plain,
% 7.37/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_19,plain,
% 7.37/1.50      ( ~ r2_hidden(X0,X1)
% 7.37/1.50      | ~ r2_hidden(X2,X3)
% 7.37/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.37/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_848,plain,
% 7.37/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.37/1.50      | r2_hidden(X2,X3) != iProver_top
% 7.37/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_25,negated_conjecture,
% 7.37/1.50      ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK5,sK4) ),
% 7.37/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_20,plain,
% 7.37/1.50      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.37/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_847,plain,
% 7.37/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.37/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2679,plain,
% 7.37/1.50      ( r2_hidden(X0,sK4) = iProver_top
% 7.37/1.50      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_25,c_847]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_3682,plain,
% 7.37/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.37/1.50      | r2_hidden(X1,sK4) != iProver_top
% 7.37/1.50      | r2_hidden(X0,sK4) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_848,c_2679]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4788,plain,
% 7.37/1.50      ( sK4 = k1_xboole_0
% 7.37/1.50      | r2_hidden(X0,sK5) != iProver_top
% 7.37/1.50      | r2_hidden(X0,sK4) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_853,c_3682]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_24,negated_conjecture,
% 7.37/1.50      ( k1_xboole_0 != sK4 ),
% 7.37/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_454,plain,( X0 = X0 ),theory(equality) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_468,plain,
% 7.37/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_454]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_455,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_892,plain,
% 7.37/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_455]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_893,plain,
% 7.37/1.50      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_892]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4793,plain,
% 7.37/1.50      ( r2_hidden(X0,sK5) != iProver_top | r2_hidden(X0,sK4) = iProver_top ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_4788,c_24,c_468,c_893]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_9828,plain,
% 7.37/1.50      ( r2_hidden(sK0(sK5,X0),sK4) = iProver_top
% 7.37/1.50      | r1_tarski(sK5,X0) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_860,c_4793]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2,plain,
% 7.37/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.37/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_861,plain,
% 7.37/1.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.37/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_19925,plain,
% 7.37/1.50      ( r1_tarski(sK5,sK4) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_9828,c_861]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11,plain,
% 7.37/1.50      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.37/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_852,plain,
% 7.37/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 7.37/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_20935,plain,
% 7.37/1.50      ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK4)) = k1_xboole_0 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_19925,c_852]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_21513,plain,
% 7.37/1.50      ( k5_xboole_0(sK5,k3_xboole_0(sK4,sK5)) = k1_xboole_0 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_0,c_20935]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4799,plain,
% 7.37/1.50      ( sK5 = k1_xboole_0 | r2_hidden(sK3(sK5),sK4) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_853,c_4793]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_23,negated_conjecture,
% 7.37/1.50      ( k1_xboole_0 != sK5 ),
% 7.37/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_887,plain,
% 7.37/1.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_455]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_888,plain,
% 7.37/1.50      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_887]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4957,plain,
% 7.37/1.50      ( r2_hidden(sK3(sK5),sK4) = iProver_top ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_4799,c_23,c_468,c_888]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_21,plain,
% 7.37/1.50      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.37/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_846,plain,
% 7.37/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.37/1.50      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1293,plain,
% 7.37/1.50      ( r2_hidden(X0,sK5) = iProver_top
% 7.37/1.50      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_25,c_846]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_3681,plain,
% 7.37/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.37/1.50      | r2_hidden(X1,sK5) = iProver_top
% 7.37/1.50      | r2_hidden(X1,sK4) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_848,c_1293]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4961,plain,
% 7.37/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.37/1.50      | r2_hidden(sK3(sK5),sK5) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_4957,c_3681]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_884,plain,
% 7.37/1.50      ( r2_hidden(sK3(sK5),sK5) | k1_xboole_0 = sK5 ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_885,plain,
% 7.37/1.50      ( k1_xboole_0 = sK5 | r2_hidden(sK3(sK5),sK5) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_884]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4982,plain,
% 7.37/1.50      ( r2_hidden(sK3(sK5),sK5) = iProver_top ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_4961,c_23,c_885]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_9827,plain,
% 7.37/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.37/1.50      | r2_hidden(sK0(sK4,X1),sK5) = iProver_top
% 7.37/1.50      | r1_tarski(sK4,X1) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_860,c_3681]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_10311,plain,
% 7.37/1.50      ( r2_hidden(sK0(sK4,X0),sK5) = iProver_top
% 7.37/1.50      | r1_tarski(sK4,X0) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_4982,c_9827]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_19924,plain,
% 7.37/1.50      ( r1_tarski(sK4,sK5) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_10311,c_861]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_20243,plain,
% 7.37/1.50      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k1_xboole_0 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_19924,c_852]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_16,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.37/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1,plain,
% 7.37/1.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.37/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_879,plain,
% 7.37/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_16,c_1]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_17,plain,
% 7.37/1.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.37/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1300,plain,
% 7.37/1.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_17,c_16]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_14,plain,
% 7.37/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.37/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1191,plain,
% 7.37/1.50      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_14,c_1]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1304,plain,
% 7.37/1.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.37/1.50      inference(demodulation,[status(thm)],[c_1300,c_1191]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1944,plain,
% 7.37/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_1,c_1304]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4386,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_879,c_1944]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_21001,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(sK4,sK5) ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_20243,c_4386]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_21035,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = k3_xboole_0(sK4,sK5) ),
% 7.37/1.50      inference(light_normalisation,[status(thm)],[c_21001,c_14]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2373,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_1304,c_1944]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_21036,plain,
% 7.37/1.50      ( k3_xboole_0(sK4,sK5) = sK4 ),
% 7.37/1.50      inference(demodulation,[status(thm)],[c_21035,c_2373]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_21723,plain,
% 7.37/1.50      ( k5_xboole_0(sK5,sK4) = k1_xboole_0 ),
% 7.37/1.50      inference(demodulation,[status(thm)],[c_21513,c_21036]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_878,plain,
% 7.37/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_16,c_1]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4314,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_878,c_1944]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_22088,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(X0,sK4),k5_xboole_0(X0,k1_xboole_0)) = sK5 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_21723,c_4314]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_22092,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(X0,sK4),X0) = sK5 ),
% 7.37/1.50      inference(light_normalisation,[status(thm)],[c_22088,c_14]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2378,plain,
% 7.37/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_1944,c_1944]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_22093,plain,
% 7.37/1.50      ( sK5 = sK4 ),
% 7.37/1.50      inference(demodulation,[status(thm)],[c_22092,c_2378]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_22,negated_conjecture,
% 7.37/1.50      ( sK4 != sK5 ),
% 7.37/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_22984,plain,
% 7.37/1.50      ( sK4 != sK4 ),
% 7.37/1.50      inference(demodulation,[status(thm)],[c_22093,c_22]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_22985,plain,
% 7.37/1.50      ( $false ),
% 7.37/1.50      inference(equality_resolution_simp,[status(thm)],[c_22984]) ).
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.37/1.50  
% 7.37/1.50  ------                               Statistics
% 7.37/1.50  
% 7.37/1.50  ------ General
% 7.37/1.50  
% 7.37/1.50  abstr_ref_over_cycles:                  0
% 7.37/1.50  abstr_ref_under_cycles:                 0
% 7.37/1.50  gc_basic_clause_elim:                   0
% 7.37/1.50  forced_gc_time:                         0
% 7.37/1.50  parsing_time:                           0.009
% 7.37/1.50  unif_index_cands_time:                  0.
% 7.37/1.50  unif_index_add_time:                    0.
% 7.37/1.50  orderings_time:                         0.
% 7.37/1.50  out_proof_time:                         0.009
% 7.37/1.50  total_time:                             0.551
% 7.37/1.50  num_of_symbols:                         47
% 7.37/1.50  num_of_terms:                           32341
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing
% 7.37/1.50  
% 7.37/1.50  num_of_splits:                          0
% 7.37/1.50  num_of_split_atoms:                     0
% 7.37/1.50  num_of_reused_defs:                     0
% 7.37/1.50  num_eq_ax_congr_red:                    40
% 7.37/1.50  num_of_sem_filtered_clauses:            1
% 7.37/1.50  num_of_subtypes:                        0
% 7.37/1.50  monotx_restored_types:                  0
% 7.37/1.50  sat_num_of_epr_types:                   0
% 7.37/1.50  sat_num_of_non_cyclic_types:            0
% 7.37/1.50  sat_guarded_non_collapsed_types:        0
% 7.37/1.50  num_pure_diseq_elim:                    0
% 7.37/1.50  simp_replaced_by:                       0
% 7.37/1.50  res_preprocessed:                       95
% 7.37/1.50  prep_upred:                             0
% 7.37/1.50  prep_unflattend:                        14
% 7.37/1.50  smt_new_axioms:                         0
% 7.37/1.50  pred_elim_cands:                        3
% 7.37/1.50  pred_elim:                              0
% 7.37/1.50  pred_elim_cl:                           0
% 7.37/1.50  pred_elim_cycles:                       2
% 7.37/1.50  merged_defs:                            6
% 7.37/1.50  merged_defs_ncl:                        0
% 7.37/1.50  bin_hyper_res:                          6
% 7.37/1.50  prep_cycles:                            3
% 7.37/1.50  pred_elim_time:                         0.004
% 7.37/1.50  splitting_time:                         0.
% 7.37/1.50  sem_filter_time:                        0.
% 7.37/1.50  monotx_time:                            0.
% 7.37/1.50  subtype_inf_time:                       0.
% 7.37/1.50  
% 7.37/1.50  ------ Problem properties
% 7.37/1.50  
% 7.37/1.50  clauses:                                26
% 7.37/1.50  conjectures:                            4
% 7.37/1.50  epr:                                    5
% 7.37/1.50  horn:                                   21
% 7.37/1.50  ground:                                 4
% 7.37/1.50  unary:                                  12
% 7.37/1.50  binary:                                 11
% 7.37/1.50  lits:                                   43
% 7.37/1.50  lits_eq:                                13
% 7.37/1.50  fd_pure:                                0
% 7.37/1.50  fd_pseudo:                              0
% 7.37/1.50  fd_cond:                                1
% 7.37/1.50  fd_pseudo_cond:                         0
% 7.37/1.50  ac_symbols:                             1
% 7.37/1.50  
% 7.37/1.50  ------ Propositional Solver
% 7.37/1.50  
% 7.37/1.50  prop_solver_calls:                      28
% 7.37/1.50  prop_fast_solver_calls:                 601
% 7.37/1.50  smt_solver_calls:                       0
% 7.37/1.50  smt_fast_solver_calls:                  0
% 7.37/1.50  prop_num_of_clauses:                    8045
% 7.37/1.50  prop_preprocess_simplified:             13372
% 7.37/1.50  prop_fo_subsumed:                       7
% 7.37/1.50  prop_solver_time:                       0.
% 7.37/1.50  smt_solver_time:                        0.
% 7.37/1.50  smt_fast_solver_time:                   0.
% 7.37/1.50  prop_fast_solver_time:                  0.
% 7.37/1.50  prop_unsat_core_time:                   0.
% 7.37/1.50  
% 7.37/1.50  ------ QBF
% 7.37/1.50  
% 7.37/1.50  qbf_q_res:                              0
% 7.37/1.50  qbf_num_tautologies:                    0
% 7.37/1.50  qbf_prep_cycles:                        0
% 7.37/1.50  
% 7.37/1.50  ------ BMC1
% 7.37/1.50  
% 7.37/1.50  bmc1_current_bound:                     -1
% 7.37/1.50  bmc1_last_solved_bound:                 -1
% 7.37/1.50  bmc1_unsat_core_size:                   -1
% 7.37/1.50  bmc1_unsat_core_parents_size:           -1
% 7.37/1.50  bmc1_merge_next_fun:                    0
% 7.37/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.37/1.50  
% 7.37/1.50  ------ Instantiation
% 7.37/1.50  
% 7.37/1.50  inst_num_of_clauses:                    1870
% 7.37/1.50  inst_num_in_passive:                    577
% 7.37/1.50  inst_num_in_active:                     398
% 7.37/1.50  inst_num_in_unprocessed:                895
% 7.37/1.50  inst_num_of_loops:                      650
% 7.37/1.50  inst_num_of_learning_restarts:          0
% 7.37/1.50  inst_num_moves_active_passive:          249
% 7.37/1.50  inst_lit_activity:                      0
% 7.37/1.50  inst_lit_activity_moves:                1
% 7.37/1.50  inst_num_tautologies:                   0
% 7.37/1.50  inst_num_prop_implied:                  0
% 7.37/1.50  inst_num_existing_simplified:           0
% 7.37/1.50  inst_num_eq_res_simplified:             0
% 7.37/1.50  inst_num_child_elim:                    0
% 7.37/1.50  inst_num_of_dismatching_blockings:      1031
% 7.37/1.50  inst_num_of_non_proper_insts:           1779
% 7.37/1.50  inst_num_of_duplicates:                 0
% 7.37/1.50  inst_inst_num_from_inst_to_res:         0
% 7.37/1.50  inst_dismatching_checking_time:         0.
% 7.37/1.50  
% 7.37/1.50  ------ Resolution
% 7.37/1.50  
% 7.37/1.50  res_num_of_clauses:                     0
% 7.37/1.50  res_num_in_passive:                     0
% 7.37/1.50  res_num_in_active:                      0
% 7.37/1.50  res_num_of_loops:                       98
% 7.37/1.50  res_forward_subset_subsumed:            32
% 7.37/1.50  res_backward_subset_subsumed:           4
% 7.37/1.50  res_forward_subsumed:                   0
% 7.37/1.50  res_backward_subsumed:                  0
% 7.37/1.50  res_forward_subsumption_resolution:     0
% 7.37/1.50  res_backward_subsumption_resolution:    0
% 7.37/1.50  res_clause_to_clause_subsumption:       15896
% 7.37/1.50  res_orphan_elimination:                 0
% 7.37/1.50  res_tautology_del:                      35
% 7.37/1.50  res_num_eq_res_simplified:              0
% 7.37/1.50  res_num_sel_changes:                    0
% 7.37/1.50  res_moves_from_active_to_pass:          0
% 7.37/1.50  
% 7.37/1.50  ------ Superposition
% 7.37/1.50  
% 7.37/1.50  sup_time_total:                         0.
% 7.37/1.50  sup_time_generating:                    0.
% 7.37/1.50  sup_time_sim_full:                      0.
% 7.37/1.50  sup_time_sim_immed:                     0.
% 7.37/1.50  
% 7.37/1.50  sup_num_of_clauses:                     864
% 7.37/1.50  sup_num_in_active:                      99
% 7.37/1.50  sup_num_in_passive:                     765
% 7.37/1.50  sup_num_of_loops:                       128
% 7.37/1.50  sup_fw_superposition:                   3751
% 7.37/1.50  sup_bw_superposition:                   2400
% 7.37/1.50  sup_immediate_simplified:               2440
% 7.37/1.50  sup_given_eliminated:                   7
% 7.37/1.50  comparisons_done:                       0
% 7.37/1.50  comparisons_avoided:                    0
% 7.37/1.50  
% 7.37/1.50  ------ Simplifications
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  sim_fw_subset_subsumed:                 9
% 7.37/1.50  sim_bw_subset_subsumed:                 0
% 7.37/1.50  sim_fw_subsumed:                        227
% 7.37/1.50  sim_bw_subsumed:                        7
% 7.37/1.50  sim_fw_subsumption_res:                 0
% 7.37/1.50  sim_bw_subsumption_res:                 0
% 7.37/1.50  sim_tautology_del:                      5
% 7.37/1.50  sim_eq_tautology_del:                   387
% 7.37/1.50  sim_eq_res_simp:                        1
% 7.37/1.50  sim_fw_demodulated:                     1927
% 7.37/1.50  sim_bw_demodulated:                     59
% 7.37/1.50  sim_light_normalised:                   901
% 7.37/1.50  sim_joinable_taut:                      101
% 7.37/1.50  sim_joinable_simp:                      0
% 7.37/1.50  sim_ac_normalised:                      0
% 7.37/1.50  sim_smt_subsumption:                    0
% 7.37/1.50  
%------------------------------------------------------------------------------
