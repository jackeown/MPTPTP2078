%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:42 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :  146 (2865 expanded)
%              Number of clauses        :   98 (1054 expanded)
%              Number of leaves         :   13 ( 558 expanded)
%              Depth                    :   27
%              Number of atoms          :  398 (9869 expanded)
%              Number of equality atoms :  221 (4459 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK4 != sK6
        | sK3 != sK5 )
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( sK4 != sK6
      | sK3 != sK5 )
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f30])).

fof(f47,plain,(
    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,
    ( sK4 != sK6
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_475,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_472,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_165,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_166,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_464,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(c_1771,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_464])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_465,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK2(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1813,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_465])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_469,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,negated_conjecture,
    ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_467,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1045,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_467])).

cnf(c_1691,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_469,c_1045])).

cnf(c_1911,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1691])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_33,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_37,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_266,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_527,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_528,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_2569,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1911,c_17,c_33,c_37,c_528])).

cnf(c_2575,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_475,c_2569])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_510,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_511,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_2021,plain,
    ( ~ r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_2022,plain,
    ( r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_2577,plain,
    ( sK4 = X0
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_2569])).

cnf(c_2588,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2577])).

cnf(c_2783,plain,
    ( r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2575,c_16,c_33,c_37,c_511,c_2022,c_2588])).

cnf(c_1687,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_469])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_468,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1754,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_468])).

cnf(c_2791,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2783,c_1754])).

cnf(c_3337,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | r2_hidden(sK0(sK6,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_475,c_2791])).

cnf(c_4065,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | r2_hidden(sK2(sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3337,c_465])).

cnf(c_502,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK4),sK4)
    | r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_506,plain,
    ( k1_xboole_0 = sK4
    | r2_hidden(sK1(k1_xboole_0,sK4),sK4) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_1088,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK2(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2905,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK4),sK4)
    | r2_hidden(sK2(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_2906,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK4),sK4) != iProver_top
    | r2_hidden(sK2(sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2905])).

cnf(c_3463,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_3464,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3463])).

cnf(c_4615,plain,
    ( r2_hidden(sK2(sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4065,c_16,c_506,c_2906,c_3464])).

cnf(c_1909,plain,
    ( sK3 = X0
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK1(X0,sK3),X0) = iProver_top
    | r2_hidden(sK1(X0,sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_1691])).

cnf(c_5735,plain,
    ( sK3 = X0
    | r2_hidden(sK1(X0,sK3),X0) = iProver_top
    | r2_hidden(sK1(X0,sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4615,c_1909])).

cnf(c_1755,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_467])).

cnf(c_14803,plain,
    ( sK3 = X0
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(sK1(X0,sK3),X0) = iProver_top
    | r2_hidden(sK1(X0,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5735,c_1755])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_476,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4066,plain,
    ( r1_tarski(sK6,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3337,c_476])).

cnf(c_1126,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_468])).

cnf(c_1692,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_469,c_1126])).

cnf(c_2037,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1692])).

cnf(c_2374,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2037,c_17,c_33,c_37,c_528])).

cnf(c_2380,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | r2_hidden(sK0(sK4,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_475,c_2374])).

cnf(c_2937,plain,
    ( r1_tarski(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2380,c_476])).

cnf(c_471,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3747,plain,
    ( sK6 = sK4
    | r1_tarski(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2937,c_471])).

cnf(c_4612,plain,
    ( sK6 = sK4 ),
    inference(superposition,[status(thm)],[c_4066,c_3747])).

cnf(c_14854,plain,
    ( sK3 = X0
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK1(X0,sK3),X0) = iProver_top
    | r2_hidden(sK1(X0,sK3),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14803,c_4612])).

cnf(c_691,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1412,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_705,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_1557,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1990,plain,
    ( r2_hidden(sK1(X0,sK3),X0)
    | r2_hidden(sK1(X0,sK3),sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1994,plain,
    ( X0 = sK3
    | r2_hidden(sK1(X0,sK3),X0) = iProver_top
    | r2_hidden(sK1(X0,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1990])).

cnf(c_1406,plain,
    ( r1_tarski(sK3,X0)
    | ~ r2_hidden(sK0(sK3,X0),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2691,plain,
    ( r1_tarski(sK3,sK3)
    | ~ r2_hidden(sK0(sK3,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1407,plain,
    ( r1_tarski(sK3,X0)
    | r2_hidden(sK0(sK3,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2692,plain,
    ( r1_tarski(sK3,sK3)
    | r2_hidden(sK0(sK3,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_16568,plain,
    ( sK3 = X0
    | r2_hidden(sK1(X0,sK3),X0) = iProver_top
    | r2_hidden(sK1(X0,sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14854,c_1412,c_1557,c_1994,c_2691,c_2692])).

cnf(c_16632,plain,
    ( sK5 = sK3
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK1(sK5,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_16568,c_1755])).

cnf(c_16643,plain,
    ( sK5 = sK3
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK1(sK5,sK3),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16632,c_4612])).

cnf(c_15,negated_conjecture,
    ( sK3 != sK5
    | sK4 != sK6 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_531,plain,
    ( ~ r1_tarski(sK6,sK4)
    | ~ r1_tarski(sK4,sK6)
    | sK4 = sK6 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_532,plain,
    ( sK4 = sK6
    | r1_tarski(sK6,sK4) != iProver_top
    | r1_tarski(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_499,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_1395,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_654,plain,
    ( ~ r2_hidden(sK1(sK5,X0),X0)
    | ~ r2_hidden(sK1(sK5,X0),sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3315,plain,
    ( ~ r2_hidden(sK1(sK5,sK3),sK5)
    | ~ r2_hidden(sK1(sK5,sK3),sK3)
    | sK5 = sK3 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_3319,plain,
    ( sK5 = sK3
    | r2_hidden(sK1(sK5,sK3),sK5) != iProver_top
    | r2_hidden(sK1(sK5,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3315])).

cnf(c_14845,plain,
    ( sK5 = sK3
    | r2_hidden(sK1(sK5,sK3),sK5) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_5735])).

cnf(c_14847,plain,
    ( sK5 = sK3
    | r2_hidden(sK1(sK5,sK3),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14845])).

cnf(c_16771,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK1(sK5,sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16643,c_15,c_532,c_1395,c_1412,c_2691,c_2692,c_2937,c_3319,c_4066,c_14847])).

cnf(c_16795,plain,
    ( r2_hidden(sK1(sK5,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4615,c_16771])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16795,c_14847,c_4066,c_3319,c_2937,c_2692,c_2691,c_1412,c_1395,c_532,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.20/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/1.49  
% 7.20/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.20/1.49  
% 7.20/1.49  ------  iProver source info
% 7.20/1.49  
% 7.20/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.20/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.20/1.49  git: non_committed_changes: false
% 7.20/1.49  git: last_make_outside_of_git: false
% 7.20/1.49  
% 7.20/1.49  ------ 
% 7.20/1.49  
% 7.20/1.49  ------ Input Options
% 7.20/1.49  
% 7.20/1.49  --out_options                           all
% 7.20/1.49  --tptp_safe_out                         true
% 7.20/1.49  --problem_path                          ""
% 7.20/1.49  --include_path                          ""
% 7.20/1.49  --clausifier                            res/vclausify_rel
% 7.20/1.49  --clausifier_options                    ""
% 7.20/1.49  --stdin                                 false
% 7.20/1.49  --stats_out                             all
% 7.20/1.49  
% 7.20/1.49  ------ General Options
% 7.20/1.49  
% 7.20/1.49  --fof                                   false
% 7.20/1.49  --time_out_real                         305.
% 7.20/1.49  --time_out_virtual                      -1.
% 7.20/1.49  --symbol_type_check                     false
% 7.20/1.49  --clausify_out                          false
% 7.20/1.49  --sig_cnt_out                           false
% 7.20/1.49  --trig_cnt_out                          false
% 7.20/1.49  --trig_cnt_out_tolerance                1.
% 7.20/1.49  --trig_cnt_out_sk_spl                   false
% 7.20/1.49  --abstr_cl_out                          false
% 7.20/1.49  
% 7.20/1.49  ------ Global Options
% 7.20/1.49  
% 7.20/1.49  --schedule                              default
% 7.20/1.49  --add_important_lit                     false
% 7.20/1.49  --prop_solver_per_cl                    1000
% 7.20/1.49  --min_unsat_core                        false
% 7.20/1.49  --soft_assumptions                      false
% 7.20/1.49  --soft_lemma_size                       3
% 7.20/1.49  --prop_impl_unit_size                   0
% 7.20/1.49  --prop_impl_unit                        []
% 7.20/1.49  --share_sel_clauses                     true
% 7.20/1.49  --reset_solvers                         false
% 7.20/1.49  --bc_imp_inh                            [conj_cone]
% 7.20/1.49  --conj_cone_tolerance                   3.
% 7.20/1.49  --extra_neg_conj                        none
% 7.20/1.49  --large_theory_mode                     true
% 7.20/1.49  --prolific_symb_bound                   200
% 7.20/1.49  --lt_threshold                          2000
% 7.20/1.49  --clause_weak_htbl                      true
% 7.20/1.49  --gc_record_bc_elim                     false
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing Options
% 7.20/1.49  
% 7.20/1.49  --preprocessing_flag                    true
% 7.20/1.49  --time_out_prep_mult                    0.1
% 7.20/1.49  --splitting_mode                        input
% 7.20/1.49  --splitting_grd                         true
% 7.20/1.49  --splitting_cvd                         false
% 7.20/1.49  --splitting_cvd_svl                     false
% 7.20/1.49  --splitting_nvd                         32
% 7.20/1.49  --sub_typing                            true
% 7.20/1.49  --prep_gs_sim                           true
% 7.20/1.49  --prep_unflatten                        true
% 7.20/1.49  --prep_res_sim                          true
% 7.20/1.49  --prep_upred                            true
% 7.20/1.49  --prep_sem_filter                       exhaustive
% 7.20/1.49  --prep_sem_filter_out                   false
% 7.20/1.49  --pred_elim                             true
% 7.20/1.49  --res_sim_input                         true
% 7.20/1.49  --eq_ax_congr_red                       true
% 7.20/1.49  --pure_diseq_elim                       true
% 7.20/1.49  --brand_transform                       false
% 7.20/1.49  --non_eq_to_eq                          false
% 7.20/1.49  --prep_def_merge                        true
% 7.20/1.49  --prep_def_merge_prop_impl              false
% 7.20/1.49  --prep_def_merge_mbd                    true
% 7.20/1.49  --prep_def_merge_tr_red                 false
% 7.20/1.49  --prep_def_merge_tr_cl                  false
% 7.20/1.49  --smt_preprocessing                     true
% 7.20/1.49  --smt_ac_axioms                         fast
% 7.20/1.49  --preprocessed_out                      false
% 7.20/1.49  --preprocessed_stats                    false
% 7.20/1.49  
% 7.20/1.49  ------ Abstraction refinement Options
% 7.20/1.49  
% 7.20/1.49  --abstr_ref                             []
% 7.20/1.49  --abstr_ref_prep                        false
% 7.20/1.49  --abstr_ref_until_sat                   false
% 7.20/1.49  --abstr_ref_sig_restrict                funpre
% 7.20/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.20/1.49  --abstr_ref_under                       []
% 7.20/1.49  
% 7.20/1.49  ------ SAT Options
% 7.20/1.49  
% 7.20/1.49  --sat_mode                              false
% 7.20/1.49  --sat_fm_restart_options                ""
% 7.20/1.49  --sat_gr_def                            false
% 7.20/1.49  --sat_epr_types                         true
% 7.20/1.49  --sat_non_cyclic_types                  false
% 7.20/1.49  --sat_finite_models                     false
% 7.20/1.49  --sat_fm_lemmas                         false
% 7.20/1.49  --sat_fm_prep                           false
% 7.20/1.49  --sat_fm_uc_incr                        true
% 7.20/1.49  --sat_out_model                         small
% 7.20/1.49  --sat_out_clauses                       false
% 7.20/1.49  
% 7.20/1.49  ------ QBF Options
% 7.20/1.49  
% 7.20/1.49  --qbf_mode                              false
% 7.20/1.49  --qbf_elim_univ                         false
% 7.20/1.49  --qbf_dom_inst                          none
% 7.20/1.49  --qbf_dom_pre_inst                      false
% 7.20/1.49  --qbf_sk_in                             false
% 7.20/1.49  --qbf_pred_elim                         true
% 7.20/1.49  --qbf_split                             512
% 7.20/1.49  
% 7.20/1.49  ------ BMC1 Options
% 7.20/1.49  
% 7.20/1.49  --bmc1_incremental                      false
% 7.20/1.49  --bmc1_axioms                           reachable_all
% 7.20/1.49  --bmc1_min_bound                        0
% 7.20/1.49  --bmc1_max_bound                        -1
% 7.20/1.49  --bmc1_max_bound_default                -1
% 7.20/1.49  --bmc1_symbol_reachability              true
% 7.20/1.49  --bmc1_property_lemmas                  false
% 7.20/1.49  --bmc1_k_induction                      false
% 7.20/1.49  --bmc1_non_equiv_states                 false
% 7.20/1.49  --bmc1_deadlock                         false
% 7.20/1.49  --bmc1_ucm                              false
% 7.20/1.49  --bmc1_add_unsat_core                   none
% 7.20/1.49  --bmc1_unsat_core_children              false
% 7.20/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.20/1.49  --bmc1_out_stat                         full
% 7.20/1.49  --bmc1_ground_init                      false
% 7.20/1.49  --bmc1_pre_inst_next_state              false
% 7.20/1.49  --bmc1_pre_inst_state                   false
% 7.20/1.49  --bmc1_pre_inst_reach_state             false
% 7.20/1.49  --bmc1_out_unsat_core                   false
% 7.20/1.49  --bmc1_aig_witness_out                  false
% 7.20/1.49  --bmc1_verbose                          false
% 7.20/1.49  --bmc1_dump_clauses_tptp                false
% 7.20/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.20/1.49  --bmc1_dump_file                        -
% 7.20/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.20/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.20/1.49  --bmc1_ucm_extend_mode                  1
% 7.20/1.49  --bmc1_ucm_init_mode                    2
% 7.20/1.49  --bmc1_ucm_cone_mode                    none
% 7.20/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.20/1.49  --bmc1_ucm_relax_model                  4
% 7.20/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.20/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.20/1.49  --bmc1_ucm_layered_model                none
% 7.20/1.49  --bmc1_ucm_max_lemma_size               10
% 7.20/1.49  
% 7.20/1.49  ------ AIG Options
% 7.20/1.49  
% 7.20/1.49  --aig_mode                              false
% 7.20/1.49  
% 7.20/1.49  ------ Instantiation Options
% 7.20/1.49  
% 7.20/1.49  --instantiation_flag                    true
% 7.20/1.49  --inst_sos_flag                         true
% 7.20/1.49  --inst_sos_phase                        true
% 7.20/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.20/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.20/1.49  --inst_lit_sel_side                     num_symb
% 7.20/1.49  --inst_solver_per_active                1400
% 7.20/1.49  --inst_solver_calls_frac                1.
% 7.20/1.49  --inst_passive_queue_type               priority_queues
% 7.20/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.20/1.49  --inst_passive_queues_freq              [25;2]
% 7.20/1.49  --inst_dismatching                      true
% 7.20/1.49  --inst_eager_unprocessed_to_passive     true
% 7.20/1.49  --inst_prop_sim_given                   true
% 7.20/1.49  --inst_prop_sim_new                     false
% 7.20/1.49  --inst_subs_new                         false
% 7.20/1.49  --inst_eq_res_simp                      false
% 7.20/1.49  --inst_subs_given                       false
% 7.20/1.49  --inst_orphan_elimination               true
% 7.20/1.49  --inst_learning_loop_flag               true
% 7.20/1.49  --inst_learning_start                   3000
% 7.20/1.49  --inst_learning_factor                  2
% 7.20/1.49  --inst_start_prop_sim_after_learn       3
% 7.20/1.49  --inst_sel_renew                        solver
% 7.20/1.49  --inst_lit_activity_flag                true
% 7.20/1.49  --inst_restr_to_given                   false
% 7.20/1.49  --inst_activity_threshold               500
% 7.20/1.49  --inst_out_proof                        true
% 7.20/1.49  
% 7.20/1.49  ------ Resolution Options
% 7.20/1.49  
% 7.20/1.49  --resolution_flag                       true
% 7.20/1.49  --res_lit_sel                           adaptive
% 7.20/1.49  --res_lit_sel_side                      none
% 7.20/1.49  --res_ordering                          kbo
% 7.20/1.49  --res_to_prop_solver                    active
% 7.20/1.49  --res_prop_simpl_new                    false
% 7.20/1.49  --res_prop_simpl_given                  true
% 7.20/1.49  --res_passive_queue_type                priority_queues
% 7.20/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.20/1.49  --res_passive_queues_freq               [15;5]
% 7.20/1.49  --res_forward_subs                      full
% 7.20/1.49  --res_backward_subs                     full
% 7.20/1.49  --res_forward_subs_resolution           true
% 7.20/1.49  --res_backward_subs_resolution          true
% 7.20/1.49  --res_orphan_elimination                true
% 7.20/1.49  --res_time_limit                        2.
% 7.20/1.49  --res_out_proof                         true
% 7.20/1.49  
% 7.20/1.49  ------ Superposition Options
% 7.20/1.49  
% 7.20/1.49  --superposition_flag                    true
% 7.20/1.49  --sup_passive_queue_type                priority_queues
% 7.20/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.20/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.20/1.49  --demod_completeness_check              fast
% 7.20/1.49  --demod_use_ground                      true
% 7.20/1.49  --sup_to_prop_solver                    passive
% 7.20/1.49  --sup_prop_simpl_new                    true
% 7.20/1.49  --sup_prop_simpl_given                  true
% 7.20/1.49  --sup_fun_splitting                     true
% 7.20/1.49  --sup_smt_interval                      50000
% 7.20/1.49  
% 7.20/1.49  ------ Superposition Simplification Setup
% 7.20/1.49  
% 7.20/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.20/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.20/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.20/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.20/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.20/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.20/1.49  --sup_immed_triv                        [TrivRules]
% 7.20/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.49  --sup_immed_bw_main                     []
% 7.20/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.20/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.20/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.49  --sup_input_bw                          []
% 7.20/1.49  
% 7.20/1.49  ------ Combination Options
% 7.20/1.49  
% 7.20/1.49  --comb_res_mult                         3
% 7.20/1.49  --comb_sup_mult                         2
% 7.20/1.49  --comb_inst_mult                        10
% 7.20/1.49  
% 7.20/1.49  ------ Debug Options
% 7.20/1.49  
% 7.20/1.49  --dbg_backtrace                         false
% 7.20/1.49  --dbg_dump_prop_clauses                 false
% 7.20/1.49  --dbg_dump_prop_clauses_file            -
% 7.20/1.49  --dbg_out_stat                          false
% 7.20/1.49  ------ Parsing...
% 7.20/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.49  ------ Proving...
% 7.20/1.49  ------ Problem Properties 
% 7.20/1.49  
% 7.20/1.49  
% 7.20/1.49  clauses                                 17
% 7.20/1.49  conjectures                             4
% 7.20/1.49  EPR                                     7
% 7.20/1.49  Horn                                    15
% 7.20/1.49  unary                                   5
% 7.20/1.49  binary                                  6
% 7.20/1.49  lits                                    35
% 7.20/1.49  lits eq                                 8
% 7.20/1.49  fd_pure                                 0
% 7.20/1.49  fd_pseudo                               0
% 7.20/1.49  fd_cond                                 0
% 7.20/1.49  fd_pseudo_cond                          3
% 7.20/1.49  AC symbols                              0
% 7.20/1.49  
% 7.20/1.49  ------ Schedule dynamic 5 is on 
% 7.20/1.49  
% 7.20/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.20/1.49  
% 7.20/1.49  
% 7.20/1.49  ------ 
% 7.20/1.49  Current options:
% 7.20/1.49  ------ 
% 7.20/1.49  
% 7.20/1.49  ------ Input Options
% 7.20/1.49  
% 7.20/1.49  --out_options                           all
% 7.20/1.49  --tptp_safe_out                         true
% 7.20/1.49  --problem_path                          ""
% 7.20/1.49  --include_path                          ""
% 7.20/1.49  --clausifier                            res/vclausify_rel
% 7.20/1.49  --clausifier_options                    ""
% 7.20/1.49  --stdin                                 false
% 7.20/1.49  --stats_out                             all
% 7.20/1.49  
% 7.20/1.49  ------ General Options
% 7.20/1.49  
% 7.20/1.49  --fof                                   false
% 7.20/1.49  --time_out_real                         305.
% 7.20/1.49  --time_out_virtual                      -1.
% 7.20/1.49  --symbol_type_check                     false
% 7.20/1.49  --clausify_out                          false
% 7.20/1.49  --sig_cnt_out                           false
% 7.20/1.49  --trig_cnt_out                          false
% 7.20/1.49  --trig_cnt_out_tolerance                1.
% 7.20/1.49  --trig_cnt_out_sk_spl                   false
% 7.20/1.49  --abstr_cl_out                          false
% 7.20/1.49  
% 7.20/1.49  ------ Global Options
% 7.20/1.49  
% 7.20/1.49  --schedule                              default
% 7.20/1.49  --add_important_lit                     false
% 7.20/1.49  --prop_solver_per_cl                    1000
% 7.20/1.49  --min_unsat_core                        false
% 7.20/1.49  --soft_assumptions                      false
% 7.20/1.49  --soft_lemma_size                       3
% 7.20/1.49  --prop_impl_unit_size                   0
% 7.20/1.49  --prop_impl_unit                        []
% 7.20/1.49  --share_sel_clauses                     true
% 7.20/1.49  --reset_solvers                         false
% 7.20/1.49  --bc_imp_inh                            [conj_cone]
% 7.20/1.49  --conj_cone_tolerance                   3.
% 7.20/1.49  --extra_neg_conj                        none
% 7.20/1.49  --large_theory_mode                     true
% 7.20/1.49  --prolific_symb_bound                   200
% 7.20/1.49  --lt_threshold                          2000
% 7.20/1.49  --clause_weak_htbl                      true
% 7.20/1.49  --gc_record_bc_elim                     false
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing Options
% 7.20/1.49  
% 7.20/1.49  --preprocessing_flag                    true
% 7.20/1.49  --time_out_prep_mult                    0.1
% 7.20/1.49  --splitting_mode                        input
% 7.20/1.49  --splitting_grd                         true
% 7.20/1.49  --splitting_cvd                         false
% 7.20/1.49  --splitting_cvd_svl                     false
% 7.20/1.49  --splitting_nvd                         32
% 7.20/1.49  --sub_typing                            true
% 7.20/1.49  --prep_gs_sim                           true
% 7.20/1.49  --prep_unflatten                        true
% 7.20/1.49  --prep_res_sim                          true
% 7.20/1.49  --prep_upred                            true
% 7.20/1.49  --prep_sem_filter                       exhaustive
% 7.20/1.49  --prep_sem_filter_out                   false
% 7.20/1.49  --pred_elim                             true
% 7.20/1.49  --res_sim_input                         true
% 7.20/1.49  --eq_ax_congr_red                       true
% 7.20/1.49  --pure_diseq_elim                       true
% 7.20/1.49  --brand_transform                       false
% 7.20/1.50  --non_eq_to_eq                          false
% 7.20/1.50  --prep_def_merge                        true
% 7.20/1.50  --prep_def_merge_prop_impl              false
% 7.20/1.50  --prep_def_merge_mbd                    true
% 7.20/1.50  --prep_def_merge_tr_red                 false
% 7.20/1.50  --prep_def_merge_tr_cl                  false
% 7.20/1.50  --smt_preprocessing                     true
% 7.20/1.50  --smt_ac_axioms                         fast
% 7.20/1.50  --preprocessed_out                      false
% 7.20/1.50  --preprocessed_stats                    false
% 7.20/1.50  
% 7.20/1.50  ------ Abstraction refinement Options
% 7.20/1.50  
% 7.20/1.50  --abstr_ref                             []
% 7.20/1.50  --abstr_ref_prep                        false
% 7.20/1.50  --abstr_ref_until_sat                   false
% 7.20/1.50  --abstr_ref_sig_restrict                funpre
% 7.20/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.20/1.50  --abstr_ref_under                       []
% 7.20/1.50  
% 7.20/1.50  ------ SAT Options
% 7.20/1.50  
% 7.20/1.50  --sat_mode                              false
% 7.20/1.50  --sat_fm_restart_options                ""
% 7.20/1.50  --sat_gr_def                            false
% 7.20/1.50  --sat_epr_types                         true
% 7.20/1.50  --sat_non_cyclic_types                  false
% 7.20/1.50  --sat_finite_models                     false
% 7.20/1.50  --sat_fm_lemmas                         false
% 7.20/1.50  --sat_fm_prep                           false
% 7.20/1.50  --sat_fm_uc_incr                        true
% 7.20/1.50  --sat_out_model                         small
% 7.20/1.50  --sat_out_clauses                       false
% 7.20/1.50  
% 7.20/1.50  ------ QBF Options
% 7.20/1.50  
% 7.20/1.50  --qbf_mode                              false
% 7.20/1.50  --qbf_elim_univ                         false
% 7.20/1.50  --qbf_dom_inst                          none
% 7.20/1.50  --qbf_dom_pre_inst                      false
% 7.20/1.50  --qbf_sk_in                             false
% 7.20/1.50  --qbf_pred_elim                         true
% 7.20/1.50  --qbf_split                             512
% 7.20/1.50  
% 7.20/1.50  ------ BMC1 Options
% 7.20/1.50  
% 7.20/1.50  --bmc1_incremental                      false
% 7.20/1.50  --bmc1_axioms                           reachable_all
% 7.20/1.50  --bmc1_min_bound                        0
% 7.20/1.50  --bmc1_max_bound                        -1
% 7.20/1.50  --bmc1_max_bound_default                -1
% 7.20/1.50  --bmc1_symbol_reachability              true
% 7.20/1.50  --bmc1_property_lemmas                  false
% 7.20/1.50  --bmc1_k_induction                      false
% 7.20/1.50  --bmc1_non_equiv_states                 false
% 7.20/1.50  --bmc1_deadlock                         false
% 7.20/1.50  --bmc1_ucm                              false
% 7.20/1.50  --bmc1_add_unsat_core                   none
% 7.20/1.50  --bmc1_unsat_core_children              false
% 7.20/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.20/1.50  --bmc1_out_stat                         full
% 7.20/1.50  --bmc1_ground_init                      false
% 7.20/1.50  --bmc1_pre_inst_next_state              false
% 7.20/1.50  --bmc1_pre_inst_state                   false
% 7.20/1.50  --bmc1_pre_inst_reach_state             false
% 7.20/1.50  --bmc1_out_unsat_core                   false
% 7.20/1.50  --bmc1_aig_witness_out                  false
% 7.20/1.50  --bmc1_verbose                          false
% 7.20/1.50  --bmc1_dump_clauses_tptp                false
% 7.20/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.20/1.50  --bmc1_dump_file                        -
% 7.20/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.20/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.20/1.50  --bmc1_ucm_extend_mode                  1
% 7.20/1.50  --bmc1_ucm_init_mode                    2
% 7.20/1.50  --bmc1_ucm_cone_mode                    none
% 7.20/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.20/1.50  --bmc1_ucm_relax_model                  4
% 7.20/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.20/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.20/1.50  --bmc1_ucm_layered_model                none
% 7.20/1.50  --bmc1_ucm_max_lemma_size               10
% 7.20/1.50  
% 7.20/1.50  ------ AIG Options
% 7.20/1.50  
% 7.20/1.50  --aig_mode                              false
% 7.20/1.50  
% 7.20/1.50  ------ Instantiation Options
% 7.20/1.50  
% 7.20/1.50  --instantiation_flag                    true
% 7.20/1.50  --inst_sos_flag                         true
% 7.20/1.50  --inst_sos_phase                        true
% 7.20/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.20/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.20/1.50  --inst_lit_sel_side                     none
% 7.20/1.50  --inst_solver_per_active                1400
% 7.20/1.50  --inst_solver_calls_frac                1.
% 7.20/1.50  --inst_passive_queue_type               priority_queues
% 7.20/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.20/1.50  --inst_passive_queues_freq              [25;2]
% 7.20/1.50  --inst_dismatching                      true
% 7.20/1.50  --inst_eager_unprocessed_to_passive     true
% 7.20/1.50  --inst_prop_sim_given                   true
% 7.20/1.50  --inst_prop_sim_new                     false
% 7.20/1.50  --inst_subs_new                         false
% 7.20/1.50  --inst_eq_res_simp                      false
% 7.20/1.50  --inst_subs_given                       false
% 7.20/1.50  --inst_orphan_elimination               true
% 7.20/1.50  --inst_learning_loop_flag               true
% 7.20/1.50  --inst_learning_start                   3000
% 7.20/1.50  --inst_learning_factor                  2
% 7.20/1.50  --inst_start_prop_sim_after_learn       3
% 7.20/1.50  --inst_sel_renew                        solver
% 7.20/1.50  --inst_lit_activity_flag                true
% 7.20/1.50  --inst_restr_to_given                   false
% 7.20/1.50  --inst_activity_threshold               500
% 7.20/1.50  --inst_out_proof                        true
% 7.20/1.50  
% 7.20/1.50  ------ Resolution Options
% 7.20/1.50  
% 7.20/1.50  --resolution_flag                       false
% 7.20/1.50  --res_lit_sel                           adaptive
% 7.20/1.50  --res_lit_sel_side                      none
% 7.20/1.50  --res_ordering                          kbo
% 7.20/1.50  --res_to_prop_solver                    active
% 7.20/1.50  --res_prop_simpl_new                    false
% 7.20/1.50  --res_prop_simpl_given                  true
% 7.20/1.50  --res_passive_queue_type                priority_queues
% 7.20/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.20/1.50  --res_passive_queues_freq               [15;5]
% 7.20/1.50  --res_forward_subs                      full
% 7.20/1.50  --res_backward_subs                     full
% 7.20/1.50  --res_forward_subs_resolution           true
% 7.20/1.50  --res_backward_subs_resolution          true
% 7.20/1.50  --res_orphan_elimination                true
% 7.20/1.50  --res_time_limit                        2.
% 7.20/1.50  --res_out_proof                         true
% 7.20/1.50  
% 7.20/1.50  ------ Superposition Options
% 7.20/1.50  
% 7.20/1.50  --superposition_flag                    true
% 7.20/1.50  --sup_passive_queue_type                priority_queues
% 7.20/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.20/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.20/1.50  --demod_completeness_check              fast
% 7.20/1.50  --demod_use_ground                      true
% 7.20/1.50  --sup_to_prop_solver                    passive
% 7.20/1.50  --sup_prop_simpl_new                    true
% 7.20/1.50  --sup_prop_simpl_given                  true
% 7.20/1.50  --sup_fun_splitting                     true
% 7.20/1.50  --sup_smt_interval                      50000
% 7.20/1.50  
% 7.20/1.50  ------ Superposition Simplification Setup
% 7.20/1.50  
% 7.20/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.20/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.20/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.20/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.20/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.20/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.20/1.50  --sup_immed_triv                        [TrivRules]
% 7.20/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.50  --sup_immed_bw_main                     []
% 7.20/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.20/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.20/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.50  --sup_input_bw                          []
% 7.20/1.50  
% 7.20/1.50  ------ Combination Options
% 7.20/1.50  
% 7.20/1.50  --comb_res_mult                         3
% 7.20/1.50  --comb_sup_mult                         2
% 7.20/1.50  --comb_inst_mult                        10
% 7.20/1.50  
% 7.20/1.50  ------ Debug Options
% 7.20/1.50  
% 7.20/1.50  --dbg_backtrace                         false
% 7.20/1.50  --dbg_dump_prop_clauses                 false
% 7.20/1.50  --dbg_dump_prop_clauses_file            -
% 7.20/1.50  --dbg_out_stat                          false
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  ------ Proving...
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  % SZS status Theorem for theBenchmark.p
% 7.20/1.50  
% 7.20/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.20/1.50  
% 7.20/1.50  fof(f2,axiom,(
% 7.20/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f12,plain,(
% 7.20/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.20/1.50    inference(ennf_transformation,[],[f2])).
% 7.20/1.50  
% 7.20/1.50  fof(f17,plain,(
% 7.20/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.20/1.50    inference(nnf_transformation,[],[f12])).
% 7.20/1.50  
% 7.20/1.50  fof(f18,plain,(
% 7.20/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.20/1.50    inference(rectify,[],[f17])).
% 7.20/1.50  
% 7.20/1.50  fof(f19,plain,(
% 7.20/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.20/1.50    introduced(choice_axiom,[])).
% 7.20/1.50  
% 7.20/1.50  fof(f20,plain,(
% 7.20/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.20/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 7.20/1.50  
% 7.20/1.50  fof(f34,plain,(
% 7.20/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f20])).
% 7.20/1.50  
% 7.20/1.50  fof(f4,axiom,(
% 7.20/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f13,plain,(
% 7.20/1.50    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 7.20/1.50    inference(ennf_transformation,[],[f4])).
% 7.20/1.50  
% 7.20/1.50  fof(f21,plain,(
% 7.20/1.50    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 7.20/1.50    inference(nnf_transformation,[],[f13])).
% 7.20/1.50  
% 7.20/1.50  fof(f22,plain,(
% 7.20/1.50    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 7.20/1.50    introduced(choice_axiom,[])).
% 7.20/1.50  
% 7.20/1.50  fof(f23,plain,(
% 7.20/1.50    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 7.20/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 7.20/1.50  
% 7.20/1.50  fof(f37,plain,(
% 7.20/1.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f23])).
% 7.20/1.50  
% 7.20/1.50  fof(f1,axiom,(
% 7.20/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f10,plain,(
% 7.20/1.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 7.20/1.50    inference(unused_predicate_definition_removal,[],[f1])).
% 7.20/1.50  
% 7.20/1.50  fof(f11,plain,(
% 7.20/1.50    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 7.20/1.50    inference(ennf_transformation,[],[f10])).
% 7.20/1.50  
% 7.20/1.50  fof(f32,plain,(
% 7.20/1.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f11])).
% 7.20/1.50  
% 7.20/1.50  fof(f3,axiom,(
% 7.20/1.50    v1_xboole_0(k1_xboole_0)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f36,plain,(
% 7.20/1.50    v1_xboole_0(k1_xboole_0)),
% 7.20/1.50    inference(cnf_transformation,[],[f3])).
% 7.20/1.50  
% 7.20/1.50  fof(f7,axiom,(
% 7.20/1.50    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f14,plain,(
% 7.20/1.50    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 7.20/1.50    inference(ennf_transformation,[],[f7])).
% 7.20/1.50  
% 7.20/1.50  fof(f28,plain,(
% 7.20/1.50    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 7.20/1.50    introduced(choice_axiom,[])).
% 7.20/1.50  
% 7.20/1.50  fof(f29,plain,(
% 7.20/1.50    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 7.20/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f28])).
% 7.20/1.50  
% 7.20/1.50  fof(f45,plain,(
% 7.20/1.50    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f29])).
% 7.20/1.50  
% 7.20/1.50  fof(f6,axiom,(
% 7.20/1.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f26,plain,(
% 7.20/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.20/1.50    inference(nnf_transformation,[],[f6])).
% 7.20/1.50  
% 7.20/1.50  fof(f27,plain,(
% 7.20/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.20/1.50    inference(flattening,[],[f26])).
% 7.20/1.50  
% 7.20/1.50  fof(f44,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f27])).
% 7.20/1.50  
% 7.20/1.50  fof(f8,conjecture,(
% 7.20/1.50    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f9,negated_conjecture,(
% 7.20/1.50    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.20/1.50    inference(negated_conjecture,[],[f8])).
% 7.20/1.50  
% 7.20/1.50  fof(f15,plain,(
% 7.20/1.50    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.20/1.50    inference(ennf_transformation,[],[f9])).
% 7.20/1.50  
% 7.20/1.50  fof(f16,plain,(
% 7.20/1.50    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.20/1.50    inference(flattening,[],[f15])).
% 7.20/1.50  
% 7.20/1.50  fof(f30,plain,(
% 7.20/1.50    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK4 != sK6 | sK3 != sK5) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6))),
% 7.20/1.50    introduced(choice_axiom,[])).
% 7.20/1.50  
% 7.20/1.50  fof(f31,plain,(
% 7.20/1.50    (sK4 != sK6 | sK3 != sK5) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6)),
% 7.20/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f30])).
% 7.20/1.50  
% 7.20/1.50  fof(f47,plain,(
% 7.20/1.50    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6)),
% 7.20/1.50    inference(cnf_transformation,[],[f31])).
% 7.20/1.50  
% 7.20/1.50  fof(f42,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.20/1.50    inference(cnf_transformation,[],[f27])).
% 7.20/1.50  
% 7.20/1.50  fof(f48,plain,(
% 7.20/1.50    k1_xboole_0 != sK3),
% 7.20/1.50    inference(cnf_transformation,[],[f31])).
% 7.20/1.50  
% 7.20/1.50  fof(f5,axiom,(
% 7.20/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f24,plain,(
% 7.20/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.20/1.50    inference(nnf_transformation,[],[f5])).
% 7.20/1.50  
% 7.20/1.50  fof(f25,plain,(
% 7.20/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.20/1.50    inference(flattening,[],[f24])).
% 7.20/1.50  
% 7.20/1.50  fof(f39,plain,(
% 7.20/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.20/1.50    inference(cnf_transformation,[],[f25])).
% 7.20/1.50  
% 7.20/1.50  fof(f52,plain,(
% 7.20/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.20/1.50    inference(equality_resolution,[],[f39])).
% 7.20/1.50  
% 7.20/1.50  fof(f41,plain,(
% 7.20/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f25])).
% 7.20/1.50  
% 7.20/1.50  fof(f49,plain,(
% 7.20/1.50    k1_xboole_0 != sK4),
% 7.20/1.50    inference(cnf_transformation,[],[f31])).
% 7.20/1.50  
% 7.20/1.50  fof(f43,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.20/1.50    inference(cnf_transformation,[],[f27])).
% 7.20/1.50  
% 7.20/1.50  fof(f35,plain,(
% 7.20/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f20])).
% 7.20/1.50  
% 7.20/1.50  fof(f50,plain,(
% 7.20/1.50    sK4 != sK6 | sK3 != sK5),
% 7.20/1.50    inference(cnf_transformation,[],[f31])).
% 7.20/1.50  
% 7.20/1.50  fof(f38,plain,(
% 7.20/1.50    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f23])).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2,plain,
% 7.20/1.50      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 7.20/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_475,plain,
% 7.20/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.20/1.50      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_6,plain,
% 7.20/1.50      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X0 = X1 ),
% 7.20/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_472,plain,
% 7.20/1.50      ( X0 = X1
% 7.20/1.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_0,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.20/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4,plain,
% 7.20/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.20/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_165,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 7.20/1.50      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_166,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.20/1.50      inference(unflattening,[status(thm)],[c_165]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_464,plain,
% 7.20/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_166]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1771,plain,
% 7.20/1.50      ( k1_xboole_0 = X0
% 7.20/1.50      | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_472,c_464]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1) ),
% 7.20/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_465,plain,
% 7.20/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.20/1.50      | r2_hidden(sK2(X1),X1) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1813,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_1771,c_465]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_10,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,X1)
% 7.20/1.50      | ~ r2_hidden(X2,X3)
% 7.20/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.20/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_469,plain,
% 7.20/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.20/1.50      | r2_hidden(X2,X3) != iProver_top
% 7.20/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_18,negated_conjecture,
% 7.20/1.50      ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
% 7.20/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_12,plain,
% 7.20/1.50      ( r2_hidden(X0,X1)
% 7.20/1.50      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.20/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_467,plain,
% 7.20/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.20/1.50      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1045,plain,
% 7.20/1.50      ( r2_hidden(X0,sK5) = iProver_top
% 7.20/1.50      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_18,c_467]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1691,plain,
% 7.20/1.50      ( r2_hidden(X0,sK5) = iProver_top
% 7.20/1.50      | r2_hidden(X0,sK3) != iProver_top
% 7.20/1.50      | r2_hidden(X1,sK4) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_469,c_1045]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1911,plain,
% 7.20/1.50      ( sK3 = k1_xboole_0
% 7.20/1.50      | r2_hidden(X0,sK4) != iProver_top
% 7.20/1.50      | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_1813,c_1691]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_17,negated_conjecture,
% 7.20/1.50      ( k1_xboole_0 != sK3 ),
% 7.20/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_9,plain,
% 7.20/1.50      ( r1_tarski(X0,X0) ),
% 7.20/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_33,plain,
% 7.20/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_7,plain,
% 7.20/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.20/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_37,plain,
% 7.20/1.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.20/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_266,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_527,plain,
% 7.20/1.50      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_266]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_528,plain,
% 7.20/1.50      ( sK3 != k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = sK3
% 7.20/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_527]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2569,plain,
% 7.20/1.50      ( r2_hidden(X0,sK4) != iProver_top
% 7.20/1.50      | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_1911,c_17,c_33,c_37,c_528]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2575,plain,
% 7.20/1.50      ( r1_tarski(sK4,X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_475,c_2569]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_16,negated_conjecture,
% 7.20/1.50      ( k1_xboole_0 != sK4 ),
% 7.20/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_510,plain,
% 7.20/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_266]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_511,plain,
% 7.20/1.50      ( sK4 != k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = sK4
% 7.20/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_510]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2021,plain,
% 7.20/1.50      ( ~ r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_166]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2022,plain,
% 7.20/1.50      ( r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2577,plain,
% 7.20/1.50      ( sK4 = X0
% 7.20/1.50      | r2_hidden(sK1(sK4,X0),X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_472,c_2569]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2588,plain,
% 7.20/1.50      ( sK4 = k1_xboole_0
% 7.20/1.50      | r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top
% 7.20/1.50      | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_2577]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2783,plain,
% 7.20/1.50      ( r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_2575,c_16,c_33,c_37,c_511,c_2022,c_2588]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1687,plain,
% 7.20/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.20/1.50      | r2_hidden(X1,sK6) != iProver_top
% 7.20/1.50      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_18,c_469]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_11,plain,
% 7.20/1.50      ( r2_hidden(X0,X1)
% 7.20/1.50      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.20/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_468,plain,
% 7.20/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.20/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1754,plain,
% 7.20/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.20/1.50      | r2_hidden(X1,sK6) != iProver_top
% 7.20/1.50      | r2_hidden(X1,sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_1687,c_468]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2791,plain,
% 7.20/1.50      ( r2_hidden(X0,sK6) != iProver_top
% 7.20/1.50      | r2_hidden(X0,sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_2783,c_1754]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3337,plain,
% 7.20/1.50      ( r1_tarski(sK6,X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK0(sK6,X0),sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_475,c_2791]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4065,plain,
% 7.20/1.50      ( r1_tarski(sK6,X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK2(sK4),sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3337,c_465]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_502,plain,
% 7.20/1.50      ( r2_hidden(sK1(k1_xboole_0,sK4),sK4)
% 7.20/1.50      | r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0)
% 7.20/1.50      | k1_xboole_0 = sK4 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_506,plain,
% 7.20/1.50      ( k1_xboole_0 = sK4
% 7.20/1.50      | r2_hidden(sK1(k1_xboole_0,sK4),sK4) = iProver_top
% 7.20/1.50      | r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1088,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,sK4) | r2_hidden(sK2(sK4),sK4) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2905,plain,
% 7.20/1.50      ( ~ r2_hidden(sK1(k1_xboole_0,sK4),sK4) | r2_hidden(sK2(sK4),sK4) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_1088]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2906,plain,
% 7.20/1.50      ( r2_hidden(sK1(k1_xboole_0,sK4),sK4) != iProver_top
% 7.20/1.50      | r2_hidden(sK2(sK4),sK4) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_2905]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3463,plain,
% 7.20/1.50      ( ~ r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_166]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3464,plain,
% 7.20/1.50      ( r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_3463]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4615,plain,
% 7.20/1.50      ( r2_hidden(sK2(sK4),sK4) = iProver_top ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_4065,c_16,c_506,c_2906,c_3464]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1909,plain,
% 7.20/1.50      ( sK3 = X0
% 7.20/1.50      | r2_hidden(X1,sK4) != iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_472,c_1691]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_5735,plain,
% 7.20/1.50      ( sK3 = X0
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_4615,c_1909]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1755,plain,
% 7.20/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.20/1.50      | r2_hidden(X0,sK3) = iProver_top
% 7.20/1.50      | r2_hidden(X1,sK6) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_1687,c_467]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14803,plain,
% 7.20/1.50      ( sK3 = X0
% 7.20/1.50      | r2_hidden(X1,sK6) != iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),sK3) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_5735,c_1755]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1,plain,
% 7.20/1.50      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 7.20/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_476,plain,
% 7.20/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.20/1.50      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4066,plain,
% 7.20/1.50      ( r1_tarski(sK6,sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3337,c_476]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1126,plain,
% 7.20/1.50      ( r2_hidden(X0,sK6) = iProver_top
% 7.20/1.50      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_18,c_468]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1692,plain,
% 7.20/1.50      ( r2_hidden(X0,sK3) != iProver_top
% 7.20/1.50      | r2_hidden(X1,sK6) = iProver_top
% 7.20/1.50      | r2_hidden(X1,sK4) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_469,c_1126]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2037,plain,
% 7.20/1.50      ( sK3 = k1_xboole_0
% 7.20/1.50      | r2_hidden(X0,sK6) = iProver_top
% 7.20/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_1813,c_1692]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2374,plain,
% 7.20/1.50      ( r2_hidden(X0,sK6) = iProver_top
% 7.20/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_2037,c_17,c_33,c_37,c_528]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2380,plain,
% 7.20/1.50      ( r1_tarski(sK4,X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK0(sK4,X0),sK6) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_475,c_2374]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2937,plain,
% 7.20/1.50      ( r1_tarski(sK4,sK6) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_2380,c_476]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_471,plain,
% 7.20/1.50      ( X0 = X1
% 7.20/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.20/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3747,plain,
% 7.20/1.50      ( sK6 = sK4 | r1_tarski(sK6,sK4) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_2937,c_471]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4612,plain,
% 7.20/1.50      ( sK6 = sK4 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_4066,c_3747]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14854,plain,
% 7.20/1.50      ( sK3 = X0
% 7.20/1.50      | r2_hidden(X1,sK4) != iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),sK3) = iProver_top ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_14803,c_4612]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_691,plain,
% 7.20/1.50      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1412,plain,
% 7.20/1.50      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_691]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_705,plain,
% 7.20/1.50      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_266]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1557,plain,
% 7.20/1.50      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_705]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1990,plain,
% 7.20/1.50      ( r2_hidden(sK1(X0,sK3),X0)
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),sK3)
% 7.20/1.50      | X0 = sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1994,plain,
% 7.20/1.50      ( X0 = sK3
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),sK3) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_1990]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1406,plain,
% 7.20/1.50      ( r1_tarski(sK3,X0) | ~ r2_hidden(sK0(sK3,X0),X0) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2691,plain,
% 7.20/1.50      ( r1_tarski(sK3,sK3) | ~ r2_hidden(sK0(sK3,sK3),sK3) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_1406]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1407,plain,
% 7.20/1.50      ( r1_tarski(sK3,X0) | r2_hidden(sK0(sK3,X0),sK3) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2692,plain,
% 7.20/1.50      ( r1_tarski(sK3,sK3) | r2_hidden(sK0(sK3,sK3),sK3) ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_1407]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_16568,plain,
% 7.20/1.50      ( sK3 = X0
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),X0) = iProver_top
% 7.20/1.50      | r2_hidden(sK1(X0,sK3),sK3) = iProver_top ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_14854,c_1412,c_1557,c_1994,c_2691,c_2692]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_16632,plain,
% 7.20/1.50      ( sK5 = sK3
% 7.20/1.50      | r2_hidden(X0,sK6) != iProver_top
% 7.20/1.50      | r2_hidden(sK1(sK5,sK3),sK3) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_16568,c_1755]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_16643,plain,
% 7.20/1.50      ( sK5 = sK3
% 7.20/1.50      | r2_hidden(X0,sK4) != iProver_top
% 7.20/1.50      | r2_hidden(sK1(sK5,sK3),sK3) = iProver_top ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_16632,c_4612]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_15,negated_conjecture,
% 7.20/1.50      ( sK3 != sK5 | sK4 != sK6 ),
% 7.20/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_531,plain,
% 7.20/1.50      ( ~ r1_tarski(sK6,sK4) | ~ r1_tarski(sK4,sK6) | sK4 = sK6 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_532,plain,
% 7.20/1.50      ( sK4 = sK6
% 7.20/1.50      | r1_tarski(sK6,sK4) != iProver_top
% 7.20/1.50      | r1_tarski(sK4,sK6) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_499,plain,
% 7.20/1.50      ( sK5 != X0 | sK3 != X0 | sK3 = sK5 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_266]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1395,plain,
% 7.20/1.50      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_499]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_5,plain,
% 7.20/1.50      ( ~ r2_hidden(sK1(X0,X1),X1)
% 7.20/1.50      | ~ r2_hidden(sK1(X0,X1),X0)
% 7.20/1.50      | X0 = X1 ),
% 7.20/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_654,plain,
% 7.20/1.50      ( ~ r2_hidden(sK1(sK5,X0),X0)
% 7.20/1.50      | ~ r2_hidden(sK1(sK5,X0),sK5)
% 7.20/1.50      | sK5 = X0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3315,plain,
% 7.20/1.50      ( ~ r2_hidden(sK1(sK5,sK3),sK5)
% 7.20/1.50      | ~ r2_hidden(sK1(sK5,sK3),sK3)
% 7.20/1.50      | sK5 = sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_654]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3319,plain,
% 7.20/1.50      ( sK5 = sK3
% 7.20/1.50      | r2_hidden(sK1(sK5,sK3),sK5) != iProver_top
% 7.20/1.50      | r2_hidden(sK1(sK5,sK3),sK3) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_3315]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14845,plain,
% 7.20/1.50      ( sK5 = sK3
% 7.20/1.50      | r2_hidden(sK1(sK5,sK3),sK5) = iProver_top
% 7.20/1.50      | iProver_top != iProver_top ),
% 7.20/1.50      inference(equality_factoring,[status(thm)],[c_5735]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14847,plain,
% 7.20/1.50      ( sK5 = sK3 | r2_hidden(sK1(sK5,sK3),sK5) = iProver_top ),
% 7.20/1.50      inference(equality_resolution_simp,[status(thm)],[c_14845]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_16771,plain,
% 7.20/1.50      ( r2_hidden(X0,sK4) != iProver_top
% 7.20/1.50      | r2_hidden(sK1(sK5,sK3),sK3) = iProver_top ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_16643,c_15,c_532,c_1395,c_1412,c_2691,c_2692,c_2937,
% 7.20/1.50                 c_3319,c_4066,c_14847]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_16795,plain,
% 7.20/1.50      ( r2_hidden(sK1(sK5,sK3),sK3) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_4615,c_16771]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(contradiction,plain,
% 7.20/1.50      ( $false ),
% 7.20/1.50      inference(minisat,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_16795,c_14847,c_4066,c_3319,c_2937,c_2692,c_2691,
% 7.20/1.50                 c_1412,c_1395,c_532,c_15]) ).
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.20/1.50  
% 7.20/1.50  ------                               Statistics
% 7.20/1.50  
% 7.20/1.50  ------ General
% 7.20/1.50  
% 7.20/1.50  abstr_ref_over_cycles:                  0
% 7.20/1.50  abstr_ref_under_cycles:                 0
% 7.20/1.50  gc_basic_clause_elim:                   0
% 7.20/1.50  forced_gc_time:                         0
% 7.20/1.50  parsing_time:                           0.009
% 7.20/1.50  unif_index_cands_time:                  0.
% 7.20/1.50  unif_index_add_time:                    0.
% 7.20/1.50  orderings_time:                         0.
% 7.20/1.50  out_proof_time:                         0.011
% 7.20/1.50  total_time:                             0.517
% 7.20/1.50  num_of_symbols:                         44
% 7.20/1.50  num_of_terms:                           12065
% 7.20/1.50  
% 7.20/1.50  ------ Preprocessing
% 7.20/1.50  
% 7.20/1.50  num_of_splits:                          0
% 7.20/1.50  num_of_split_atoms:                     0
% 7.20/1.50  num_of_reused_defs:                     0
% 7.20/1.50  num_eq_ax_congr_red:                    27
% 7.20/1.50  num_of_sem_filtered_clauses:            1
% 7.20/1.50  num_of_subtypes:                        0
% 7.20/1.50  monotx_restored_types:                  0
% 7.20/1.50  sat_num_of_epr_types:                   0
% 7.20/1.50  sat_num_of_non_cyclic_types:            0
% 7.20/1.50  sat_guarded_non_collapsed_types:        0
% 7.20/1.50  num_pure_diseq_elim:                    0
% 7.20/1.50  simp_replaced_by:                       0
% 7.20/1.50  res_preprocessed:                       78
% 7.20/1.50  prep_upred:                             0
% 7.20/1.50  prep_unflattend:                        1
% 7.20/1.50  smt_new_axioms:                         0
% 7.20/1.50  pred_elim_cands:                        2
% 7.20/1.50  pred_elim:                              1
% 7.20/1.50  pred_elim_cl:                           1
% 7.20/1.50  pred_elim_cycles:                       3
% 7.20/1.50  merged_defs:                            0
% 7.20/1.50  merged_defs_ncl:                        0
% 7.20/1.50  bin_hyper_res:                          0
% 7.20/1.50  prep_cycles:                            4
% 7.20/1.50  pred_elim_time:                         0.
% 7.20/1.50  splitting_time:                         0.
% 7.20/1.50  sem_filter_time:                        0.
% 7.20/1.50  monotx_time:                            0.001
% 7.20/1.50  subtype_inf_time:                       0.
% 7.20/1.50  
% 7.20/1.50  ------ Problem properties
% 7.20/1.50  
% 7.20/1.50  clauses:                                17
% 7.20/1.50  conjectures:                            4
% 7.20/1.50  epr:                                    7
% 7.20/1.50  horn:                                   15
% 7.20/1.50  ground:                                 4
% 7.20/1.50  unary:                                  5
% 7.20/1.50  binary:                                 6
% 7.20/1.50  lits:                                   35
% 7.20/1.50  lits_eq:                                8
% 7.20/1.50  fd_pure:                                0
% 7.20/1.50  fd_pseudo:                              0
% 7.20/1.50  fd_cond:                                0
% 7.20/1.50  fd_pseudo_cond:                         3
% 7.20/1.50  ac_symbols:                             0
% 7.20/1.50  
% 7.20/1.50  ------ Propositional Solver
% 7.20/1.50  
% 7.20/1.50  prop_solver_calls:                      30
% 7.20/1.50  prop_fast_solver_calls:                 1420
% 7.20/1.50  smt_solver_calls:                       0
% 7.20/1.50  smt_fast_solver_calls:                  0
% 7.20/1.50  prop_num_of_clauses:                    7235
% 7.20/1.50  prop_preprocess_simplified:             14773
% 7.20/1.50  prop_fo_subsumed:                       102
% 7.20/1.50  prop_solver_time:                       0.
% 7.20/1.50  smt_solver_time:                        0.
% 7.20/1.50  smt_fast_solver_time:                   0.
% 7.20/1.50  prop_fast_solver_time:                  0.
% 7.20/1.50  prop_unsat_core_time:                   0.001
% 7.20/1.50  
% 7.20/1.50  ------ QBF
% 7.20/1.50  
% 7.20/1.50  qbf_q_res:                              0
% 7.20/1.50  qbf_num_tautologies:                    0
% 7.20/1.50  qbf_prep_cycles:                        0
% 7.20/1.50  
% 7.20/1.50  ------ BMC1
% 7.20/1.50  
% 7.20/1.50  bmc1_current_bound:                     -1
% 7.20/1.50  bmc1_last_solved_bound:                 -1
% 7.20/1.50  bmc1_unsat_core_size:                   -1
% 7.20/1.50  bmc1_unsat_core_parents_size:           -1
% 7.20/1.50  bmc1_merge_next_fun:                    0
% 7.20/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.20/1.50  
% 7.20/1.50  ------ Instantiation
% 7.20/1.50  
% 7.20/1.50  inst_num_of_clauses:                    1752
% 7.20/1.50  inst_num_in_passive:                    289
% 7.20/1.50  inst_num_in_active:                     661
% 7.20/1.50  inst_num_in_unprocessed:                814
% 7.20/1.50  inst_num_of_loops:                      840
% 7.20/1.50  inst_num_of_learning_restarts:          0
% 7.20/1.50  inst_num_moves_active_passive:          179
% 7.20/1.50  inst_lit_activity:                      0
% 7.20/1.50  inst_lit_activity_moves:                0
% 7.20/1.50  inst_num_tautologies:                   0
% 7.20/1.50  inst_num_prop_implied:                  0
% 7.20/1.50  inst_num_existing_simplified:           0
% 7.20/1.50  inst_num_eq_res_simplified:             0
% 7.20/1.50  inst_num_child_elim:                    0
% 7.20/1.50  inst_num_of_dismatching_blockings:      1090
% 7.20/1.50  inst_num_of_non_proper_insts:           2013
% 7.20/1.50  inst_num_of_duplicates:                 0
% 7.20/1.50  inst_inst_num_from_inst_to_res:         0
% 7.20/1.50  inst_dismatching_checking_time:         0.
% 7.20/1.50  
% 7.20/1.50  ------ Resolution
% 7.20/1.50  
% 7.20/1.50  res_num_of_clauses:                     0
% 7.20/1.50  res_num_in_passive:                     0
% 7.20/1.50  res_num_in_active:                      0
% 7.20/1.50  res_num_of_loops:                       82
% 7.20/1.50  res_forward_subset_subsumed:            679
% 7.20/1.50  res_backward_subset_subsumed:           30
% 7.20/1.50  res_forward_subsumed:                   0
% 7.20/1.50  res_backward_subsumed:                  0
% 7.20/1.50  res_forward_subsumption_resolution:     0
% 7.20/1.50  res_backward_subsumption_resolution:    0
% 7.20/1.50  res_clause_to_clause_subsumption:       10774
% 7.20/1.50  res_orphan_elimination:                 0
% 7.20/1.50  res_tautology_del:                      229
% 7.20/1.50  res_num_eq_res_simplified:              0
% 7.20/1.50  res_num_sel_changes:                    0
% 7.20/1.50  res_moves_from_active_to_pass:          0
% 7.20/1.50  
% 7.20/1.50  ------ Superposition
% 7.20/1.50  
% 7.20/1.50  sup_time_total:                         0.
% 7.20/1.50  sup_time_generating:                    0.
% 7.20/1.50  sup_time_sim_full:                      0.
% 7.20/1.50  sup_time_sim_immed:                     0.
% 7.20/1.50  
% 7.20/1.50  sup_num_of_clauses:                     871
% 7.20/1.50  sup_num_in_active:                      106
% 7.20/1.50  sup_num_in_passive:                     765
% 7.20/1.50  sup_num_of_loops:                       166
% 7.20/1.50  sup_fw_superposition:                   1834
% 7.20/1.50  sup_bw_superposition:                   678
% 7.20/1.50  sup_immediate_simplified:               510
% 7.20/1.50  sup_given_eliminated:                   52
% 7.20/1.50  comparisons_done:                       0
% 7.20/1.50  comparisons_avoided:                    0
% 7.20/1.50  
% 7.20/1.50  ------ Simplifications
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  sim_fw_subset_subsumed:                 123
% 7.20/1.50  sim_bw_subset_subsumed:                 3
% 7.20/1.50  sim_fw_subsumed:                        129
% 7.20/1.50  sim_bw_subsumed:                        254
% 7.20/1.50  sim_fw_subsumption_res:                 0
% 7.20/1.50  sim_bw_subsumption_res:                 0
% 7.20/1.50  sim_tautology_del:                      17
% 7.20/1.50  sim_eq_tautology_del:                   37
% 7.20/1.50  sim_eq_res_simp:                        2
% 7.20/1.50  sim_fw_demodulated:                     4
% 7.20/1.50  sim_bw_demodulated:                     1
% 7.20/1.50  sim_light_normalised:                   245
% 7.20/1.50  sim_joinable_taut:                      0
% 7.20/1.50  sim_joinable_simp:                      0
% 7.20/1.50  sim_ac_normalised:                      0
% 7.20/1.50  sim_smt_subsumption:                    0
% 7.20/1.50  
%------------------------------------------------------------------------------
