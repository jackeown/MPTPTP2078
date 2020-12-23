%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0352+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:05 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 172 expanded)
%              Number of clauses        :   39 (  70 expanded)
%              Number of leaves         :    7 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  143 ( 597 expanded)
%              Number of equality atoms :   44 (  82 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK2) )
        & ( r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15,f14])).

fof(f23,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_113,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_352,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_113])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_111,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_354,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_111])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_117,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_38))
    | m1_subset_1(k3_subset_1(X0_38,X0_36),k1_zfmisc_1(X0_38)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_348,plain,
    ( m1_subset_1(X0_36,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_38,X0_36),k1_zfmisc_1(X0_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_117])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_118,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_38))
    | k4_xboole_0(X0_38,X0_36) = k3_subset_1(X0_38,X0_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_347,plain,
    ( k4_xboole_0(X0_38,X0_36) = k3_subset_1(X0_38,X0_36)
    | m1_subset_1(X0_36,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118])).

cnf(c_591,plain,
    ( k4_xboole_0(X0_38,k3_subset_1(X0_38,X0_36)) = k3_subset_1(X0_38,k3_subset_1(X0_38,X0_36))
    | m1_subset_1(X0_36,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(superposition,[status(thm)],[c_348,c_347])).

cnf(c_1209,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_354,c_591])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_116,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_38))
    | k3_subset_1(X0_38,k3_subset_1(X0_38,X0_36)) = X0_36 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_349,plain,
    ( k3_subset_1(X0_38,k3_subset_1(X0_38,X0_36)) = X0_36
    | m1_subset_1(X0_36,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_116])).

cnf(c_637,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_354,c_349])).

cnf(c_1216,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1209,c_637])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_115,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(k4_xboole_0(X0_38,X1_36),k4_xboole_0(X0_38,X0_36)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_350,plain,
    ( r1_tarski(X0_36,X1_36) != iProver_top
    | r1_tarski(k4_xboole_0(X0_38,X1_36),k4_xboole_0(X0_38,X0_36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_1431,plain,
    ( r1_tarski(X0_36,k3_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,k4_xboole_0(sK0,X0_36)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_350])).

cnf(c_1640,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,k3_subset_1(sK0,sK2))) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_352,c_1431])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_112,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_353,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_112])).

cnf(c_1208,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_353,c_591])).

cnf(c_636,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_353,c_349])).

cnf(c_1219,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1208,c_636])).

cnf(c_1652,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1640,c_1219])).

cnf(c_528,plain,
    ( k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_354,c_347])).

cnf(c_527,plain,
    ( k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_353,c_347])).

cnf(c_654,plain,
    ( r1_tarski(X0_36,sK2) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,X0_36)) = iProver_top ),
    inference(superposition,[status(thm)],[c_527,c_350])).

cnf(c_881,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_654])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1112,plain,
    ( r1_tarski(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1652,c_1112])).


%------------------------------------------------------------------------------
