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
% DateTime   : Thu Dec  3 11:37:09 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 350 expanded)
%              Number of clauses        :   64 ( 138 expanded)
%              Number of leaves         :   10 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :  294 (1234 expanded)
%              Number of equality atoms :  150 ( 369 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) )
   => ( sK2 != sK3
      & k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK3,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( sK2 != sK3
    & k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK3,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f10,f20])).

fof(f34,plain,(
    k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK3,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_315,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_317,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,negated_conjecture,
    ( k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK3,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_309,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_951,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_309])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_308,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_979,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_308])).

cnf(c_1094,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_317,c_979])).

cnf(c_1200,plain,
    ( r2_hidden(sK0(sK3,X0),sK2) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_317,c_1094])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_318,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1321,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_318])).

cnf(c_1348,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_4119,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1321,c_1348])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_310,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4124,plain,
    ( k3_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_4119,c_310])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_312,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4379,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4124,c_312])).

cnf(c_6668,plain,
    ( k3_xboole_0(X0,sK3) = X1
    | r2_hidden(sK1(X0,sK3,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,sK3,X1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_315,c_4379])).

cnf(c_16109,plain,
    ( k3_xboole_0(X0,sK3) = sK3
    | r2_hidden(sK1(X0,sK3,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6668,c_4379])).

cnf(c_16280,plain,
    ( k3_xboole_0(sK2,sK3) = sK3
    | r2_hidden(sK1(sK2,sK3,sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_16109])).

cnf(c_5767,plain,
    ( ~ r1_tarski(X0,sK3)
    | k3_xboole_0(X0,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5769,plain,
    ( ~ r1_tarski(sK2,sK3)
    | k3_xboole_0(sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_5767])).

cnf(c_118,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_513,plain,
    ( k3_xboole_0(X0,X1) != X2
    | sK2 != X2
    | sK2 = k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_5162,plain,
    ( k3_xboole_0(X0,sK3) != X1
    | sK2 != X1
    | sK2 = k3_xboole_0(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_5163,plain,
    ( k3_xboole_0(sK2,sK3) != sK2
    | sK2 = k3_xboole_0(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5162])).

cnf(c_677,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_308])).

cnf(c_955,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_309,c_677])).

cnf(c_1088,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK0(sK2,X1),sK3) = iProver_top
    | r1_tarski(sK2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_317,c_955])).

cnf(c_1208,plain,
    ( r2_hidden(sK0(sK2,X0),sK3) = iProver_top
    | r1_tarski(sK2,X1) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_317,c_1088])).

cnf(c_1356,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_318])).

cnf(c_4391,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1356])).

cnf(c_4393,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4391])).

cnf(c_4398,plain,
    ( r1_tarski(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4393])).

cnf(c_414,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_485,plain,
    ( sK3 != k3_xboole_0(X0,X1)
    | sK2 != k3_xboole_0(X0,X1)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_2530,plain,
    ( sK3 != k3_xboole_0(X0,sK3)
    | sK2 != k3_xboole_0(X0,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_2531,plain,
    ( sK3 != k3_xboole_0(sK2,sK3)
    | sK2 != k3_xboole_0(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_433,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_461,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_466,plain,
    ( k3_xboole_0(X0,X1) != sK3
    | sK3 = k3_xboole_0(X0,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_750,plain,
    ( k3_xboole_0(X0,sK3) != sK3
    | sK3 = k3_xboole_0(X0,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_751,plain,
    ( k3_xboole_0(sK2,sK3) != sK3
    | sK3 = k3_xboole_0(sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_469,plain,
    ( r2_hidden(sK1(X0,X1,sK3),X1)
    | r2_hidden(sK1(X0,X1,sK3),sK3)
    | k3_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_648,plain,
    ( r2_hidden(sK1(X0,sK3,sK3),sK3)
    | k3_xboole_0(X0,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_653,plain,
    ( k3_xboole_0(X0,sK3) = sK3
    | r2_hidden(sK1(X0,sK3,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_655,plain,
    ( k3_xboole_0(sK2,sK3) = sK3
    | r2_hidden(sK1(sK2,sK3,sK3),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_467,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
    | ~ r2_hidden(sK1(X0,X1,sK3),X0)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | k3_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_647,plain,
    ( ~ r2_hidden(sK1(X0,sK3,sK3),X0)
    | ~ r2_hidden(sK1(X0,sK3,sK3),sK3)
    | k3_xboole_0(X0,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_649,plain,
    ( k3_xboole_0(X0,sK3) = sK3
    | r2_hidden(sK1(X0,sK3,sK3),X0) != iProver_top
    | r2_hidden(sK1(X0,sK3,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_651,plain,
    ( k3_xboole_0(sK2,sK3) = sK3
    | r2_hidden(sK1(sK2,sK3,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK2,sK3,sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_117,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_462,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_124,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_12,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16280,c_5769,c_5163,c_4398,c_2531,c_751,c_655,c_651,c_462,c_124,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 21:26:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.45/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.99  
% 3.45/0.99  ------  iProver source info
% 3.45/0.99  
% 3.45/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.99  git: non_committed_changes: false
% 3.45/0.99  git: last_make_outside_of_git: false
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  ------ Parsing...
% 3.45/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 14
% 3.45/0.99  conjectures                             2
% 3.45/0.99  EPR                                     1
% 3.45/0.99  Horn                                    11
% 3.45/0.99  unary                                   2
% 3.45/0.99  binary                                  7
% 3.45/0.99  lits                                    32
% 3.45/0.99  lits eq                                 6
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 0
% 3.45/0.99  fd_pseudo_cond                          3
% 3.45/0.99  AC symbols                              0
% 3.45/0.99  
% 3.45/0.99  ------ Input Options Time Limit: Unbounded
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  Current options:
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ Proving...
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS status Theorem for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  fof(f2,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f13,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.45/0.99    inference(nnf_transformation,[],[f2])).
% 3.45/0.99  
% 3.45/0.99  fof(f14,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.45/0.99    inference(flattening,[],[f13])).
% 3.45/0.99  
% 3.45/0.99  fof(f15,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.45/0.99    inference(rectify,[],[f14])).
% 3.45/0.99  
% 3.45/0.99  fof(f16,plain,(
% 3.45/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f17,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 3.45/0.99  
% 3.45/0.99  fof(f28,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f1,axiom,(
% 3.45/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f7,plain,(
% 3.45/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.45/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.45/0.99  
% 3.45/0.99  fof(f8,plain,(
% 3.45/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f7])).
% 3.45/0.99  
% 3.45/0.99  fof(f11,plain,(
% 3.45/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f12,plain,(
% 3.45/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).
% 3.45/0.99  
% 3.45/0.99  fof(f22,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f12])).
% 3.45/0.99  
% 3.45/0.99  fof(f5,conjecture,(
% 3.45/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f6,negated_conjecture,(
% 3.45/0.99    ~! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 3.45/0.99    inference(negated_conjecture,[],[f5])).
% 3.45/0.99  
% 3.45/0.99  fof(f10,plain,(
% 3.45/0.99    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f6])).
% 3.45/0.99  
% 3.45/0.99  fof(f20,plain,(
% 3.45/0.99    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)) => (sK2 != sK3 & k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK3,sK3))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f21,plain,(
% 3.45/0.99    sK2 != sK3 & k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK3,sK3)),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f10,f20])).
% 3.45/0.99  
% 3.45/0.99  fof(f34,plain,(
% 3.45/0.99    k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK3,sK3)),
% 3.45/0.99    inference(cnf_transformation,[],[f21])).
% 3.45/0.99  
% 3.45/0.99  fof(f4,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f18,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.45/0.99    inference(nnf_transformation,[],[f4])).
% 3.45/0.99  
% 3.45/0.99  fof(f19,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.45/0.99    inference(flattening,[],[f18])).
% 3.45/0.99  
% 3.45/0.99  fof(f33,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f19])).
% 3.45/0.99  
% 3.45/0.99  fof(f32,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f19])).
% 3.45/0.99  
% 3.45/0.99  fof(f23,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f12])).
% 3.45/0.99  
% 3.45/0.99  fof(f3,axiom,(
% 3.45/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f9,plain,(
% 3.45/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f3])).
% 3.45/0.99  
% 3.45/0.99  fof(f30,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f9])).
% 3.45/0.99  
% 3.45/0.99  fof(f25,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.45/0.99    inference(cnf_transformation,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f37,plain,(
% 3.45/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.45/0.99    inference(equality_resolution,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f29,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f35,plain,(
% 3.45/0.99    sK2 != sK3),
% 3.45/0.99    inference(cnf_transformation,[],[f21])).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3,plain,
% 3.45/0.99      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.45/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.45/0.99      | k3_xboole_0(X0,X1) = X2 ),
% 3.45/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_315,plain,
% 3.45/0.99      ( k3_xboole_0(X0,X1) = X2
% 3.45/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 3.45/0.99      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1,plain,
% 3.45/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_317,plain,
% 3.45/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.45/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_13,negated_conjecture,
% 3.45/0.99      ( k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK3,sK3) ),
% 3.45/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,X1)
% 3.45/0.99      | ~ r2_hidden(X2,X3)
% 3.45/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_309,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.45/0.99      | r2_hidden(X2,X3) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_951,plain,
% 3.45/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.45/0.99      | r2_hidden(X1,sK3) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_13,c_309]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_10,plain,
% 3.45/0.99      ( r2_hidden(X0,X1)
% 3.45/0.99      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_308,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_979,plain,
% 3.45/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.45/0.99      | r2_hidden(X1,sK3) != iProver_top
% 3.45/0.99      | r2_hidden(X1,sK2) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_951,c_308]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1094,plain,
% 3.45/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.45/0.99      | r2_hidden(X0,sK2) = iProver_top
% 3.45/0.99      | r1_tarski(sK3,X1) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_317,c_979]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1200,plain,
% 3.45/0.99      ( r2_hidden(sK0(sK3,X0),sK2) = iProver_top
% 3.45/0.99      | r1_tarski(sK3,X0) = iProver_top
% 3.45/0.99      | r1_tarski(sK3,X1) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_317,c_1094]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_0,plain,
% 3.45/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_318,plain,
% 3.45/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.45/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1321,plain,
% 3.45/0.99      ( r1_tarski(sK3,X0) = iProver_top
% 3.45/0.99      | r1_tarski(sK3,sK2) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1200,c_318]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1348,plain,
% 3.45/0.99      ( r1_tarski(sK3,sK2) = iProver_top ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1321]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4119,plain,
% 3.45/0.99      ( r1_tarski(sK3,sK2) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_1321,c_1348]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_8,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.45/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_310,plain,
% 3.45/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4124,plain,
% 3.45/0.99      ( k3_xboole_0(sK3,sK2) = sK3 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4119,c_310]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_312,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.45/0.99      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4379,plain,
% 3.45/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.45/0.99      | r2_hidden(X0,sK2) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4124,c_312]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6668,plain,
% 3.45/0.99      ( k3_xboole_0(X0,sK3) = X1
% 3.45/0.99      | r2_hidden(sK1(X0,sK3,X1),X1) = iProver_top
% 3.45/0.99      | r2_hidden(sK1(X0,sK3,X1),sK2) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_315,c_4379]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_16109,plain,
% 3.45/0.99      ( k3_xboole_0(X0,sK3) = sK3
% 3.45/0.99      | r2_hidden(sK1(X0,sK3,sK3),sK2) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_6668,c_4379]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_16280,plain,
% 3.45/0.99      ( k3_xboole_0(sK2,sK3) = sK3
% 3.45/0.99      | r2_hidden(sK1(sK2,sK3,sK3),sK2) = iProver_top ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_16109]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5767,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,sK3) | k3_xboole_0(X0,sK3) = X0 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5769,plain,
% 3.45/0.99      ( ~ r1_tarski(sK2,sK3) | k3_xboole_0(sK2,sK3) = sK2 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_5767]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_118,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_513,plain,
% 3.45/0.99      ( k3_xboole_0(X0,X1) != X2 | sK2 != X2 | sK2 = k3_xboole_0(X0,X1) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_118]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5162,plain,
% 3.45/0.99      ( k3_xboole_0(X0,sK3) != X1
% 3.45/0.99      | sK2 != X1
% 3.45/0.99      | sK2 = k3_xboole_0(X0,sK3) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_513]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5163,plain,
% 3.45/0.99      ( k3_xboole_0(sK2,sK3) != sK2
% 3.45/0.99      | sK2 = k3_xboole_0(sK2,sK3)
% 3.45/0.99      | sK2 != sK2 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_5162]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_677,plain,
% 3.45/0.99      ( r2_hidden(X0,sK3) = iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK2)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_13,c_308]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_955,plain,
% 3.45/0.99      ( r2_hidden(X0,sK3) = iProver_top
% 3.45/0.99      | r2_hidden(X1,sK2) != iProver_top
% 3.45/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_309,c_677]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1088,plain,
% 3.45/0.99      ( r2_hidden(X0,sK2) != iProver_top
% 3.45/0.99      | r2_hidden(sK0(sK2,X1),sK3) = iProver_top
% 3.45/0.99      | r1_tarski(sK2,X1) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_317,c_955]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1208,plain,
% 3.45/0.99      ( r2_hidden(sK0(sK2,X0),sK3) = iProver_top
% 3.45/0.99      | r1_tarski(sK2,X1) = iProver_top
% 3.45/0.99      | r1_tarski(sK2,X0) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_317,c_1088]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1356,plain,
% 3.45/0.99      ( r1_tarski(sK2,X0) = iProver_top
% 3.45/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1208,c_318]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4391,plain,
% 3.45/0.99      ( r1_tarski(sK2,sK3) = iProver_top | iProver_top != iProver_top ),
% 3.45/0.99      inference(equality_factoring,[status(thm)],[c_1356]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4393,plain,
% 3.45/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.45/0.99      inference(equality_resolution_simp,[status(thm)],[c_4391]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4398,plain,
% 3.45/0.99      ( r1_tarski(sK2,sK3) ),
% 3.45/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4393]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_414,plain,
% 3.45/0.99      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_118]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_485,plain,
% 3.45/0.99      ( sK3 != k3_xboole_0(X0,X1)
% 3.45/0.99      | sK2 != k3_xboole_0(X0,X1)
% 3.45/0.99      | sK2 = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_414]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2530,plain,
% 3.45/0.99      ( sK3 != k3_xboole_0(X0,sK3)
% 3.45/0.99      | sK2 != k3_xboole_0(X0,sK3)
% 3.45/0.99      | sK2 = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_485]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2531,plain,
% 3.45/0.99      ( sK3 != k3_xboole_0(sK2,sK3)
% 3.45/0.99      | sK2 != k3_xboole_0(sK2,sK3)
% 3.45/0.99      | sK2 = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_2530]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_433,plain,
% 3.45/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_118]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_461,plain,
% 3.45/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_433]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_466,plain,
% 3.45/0.99      ( k3_xboole_0(X0,X1) != sK3
% 3.45/0.99      | sK3 = k3_xboole_0(X0,X1)
% 3.45/0.99      | sK3 != sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_461]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_750,plain,
% 3.45/0.99      ( k3_xboole_0(X0,sK3) != sK3
% 3.45/0.99      | sK3 = k3_xboole_0(X0,sK3)
% 3.45/0.99      | sK3 != sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_466]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_751,plain,
% 3.45/0.99      ( k3_xboole_0(sK2,sK3) != sK3
% 3.45/0.99      | sK3 = k3_xboole_0(sK2,sK3)
% 3.45/0.99      | sK3 != sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_750]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_469,plain,
% 3.45/0.99      ( r2_hidden(sK1(X0,X1,sK3),X1)
% 3.45/0.99      | r2_hidden(sK1(X0,X1,sK3),sK3)
% 3.45/0.99      | k3_xboole_0(X0,X1) = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_648,plain,
% 3.45/0.99      ( r2_hidden(sK1(X0,sK3,sK3),sK3) | k3_xboole_0(X0,sK3) = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_469]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_653,plain,
% 3.45/0.99      ( k3_xboole_0(X0,sK3) = sK3
% 3.45/0.99      | r2_hidden(sK1(X0,sK3,sK3),sK3) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_655,plain,
% 3.45/0.99      ( k3_xboole_0(sK2,sK3) = sK3
% 3.45/0.99      | r2_hidden(sK1(sK2,sK3,sK3),sK3) = iProver_top ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_653]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2,plain,
% 3.45/0.99      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 3.45/0.99      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.45/0.99      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.45/0.99      | k3_xboole_0(X0,X1) = X2 ),
% 3.45/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_467,plain,
% 3.45/0.99      ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
% 3.45/0.99      | ~ r2_hidden(sK1(X0,X1,sK3),X0)
% 3.45/0.99      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 3.45/0.99      | k3_xboole_0(X0,X1) = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_647,plain,
% 3.45/0.99      ( ~ r2_hidden(sK1(X0,sK3,sK3),X0)
% 3.45/0.99      | ~ r2_hidden(sK1(X0,sK3,sK3),sK3)
% 3.45/0.99      | k3_xboole_0(X0,sK3) = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_467]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_649,plain,
% 3.45/0.99      ( k3_xboole_0(X0,sK3) = sK3
% 3.45/0.99      | r2_hidden(sK1(X0,sK3,sK3),X0) != iProver_top
% 3.45/0.99      | r2_hidden(sK1(X0,sK3,sK3),sK3) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_651,plain,
% 3.45/0.99      ( k3_xboole_0(sK2,sK3) = sK3
% 3.45/0.99      | r2_hidden(sK1(sK2,sK3,sK3),sK3) != iProver_top
% 3.45/0.99      | r2_hidden(sK1(sK2,sK3,sK3),sK2) != iProver_top ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_649]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_117,plain,( X0 = X0 ),theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_462,plain,
% 3.45/0.99      ( sK3 = sK3 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_117]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_124,plain,
% 3.45/0.99      ( sK2 = sK2 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_117]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12,negated_conjecture,
% 3.45/0.99      ( sK2 != sK3 ),
% 3.45/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(contradiction,plain,
% 3.45/0.99      ( $false ),
% 3.45/0.99      inference(minisat,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_16280,c_5769,c_5163,c_4398,c_2531,c_751,c_655,c_651,
% 3.45/0.99                 c_462,c_124,c_12]) ).
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  ------                               Statistics
% 3.45/0.99  
% 3.45/0.99  ------ Selected
% 3.45/0.99  
% 3.45/0.99  total_time:                             0.432
% 3.45/0.99  
%------------------------------------------------------------------------------
