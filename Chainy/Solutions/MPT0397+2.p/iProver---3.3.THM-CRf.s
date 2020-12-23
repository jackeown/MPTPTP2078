%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0397+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 19.40s
% Output     : CNFRefutation 19.40s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 124 expanded)
%              Number of clauses        :   32 (  33 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 ( 333 expanded)
%              Number of equality atoms :   72 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f569,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f943,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f569])).

fof(f944,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f943])).

fof(f1273,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK101(X0,X1))
        & r2_hidden(sK101(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1274,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK101(X0,X1))
        & r2_hidden(sK101(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK101])],[f944,f1273])).

fof(f2173,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK101(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1274])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1282,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2648,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | o_0_0_xboole_0 = X0
      | r2_hidden(sK101(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f2173,f1282])).

fof(f546,axiom,(
    ! [X0,X1] :
      ( r2_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X3,X2)
                  & r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f585,plain,(
    ! [X0,X1] :
      ( r2_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X3,X2)
                  & r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f546])).

fof(f928,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X3,X2)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(X2,X1) )
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f585])).

fof(f1263,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & r2_hidden(X3,X0) )
     => ( r1_tarski(sK96(X0,X2),X2)
        & r2_hidden(sK96(X0,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1264,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(sK96(X0,X2),X2)
            & r2_hidden(sK96(X0,X2),X0) )
          | ~ r2_hidden(X2,X1) )
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96])],[f928,f1263])).

fof(f2147,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK96(X0,X2),X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1264])).

fof(f558,conjecture,(
    ! [X0,X1] :
      ( r2_setfam_1(X1,X0)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f559,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_setfam_1(X1,X0)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f558])).

fof(f933,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r2_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f559])).

fof(f934,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r2_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f933])).

fof(f1270,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r2_setfam_1(X1,X0) )
   => ( ~ r1_tarski(k1_setfam_1(sK100),k1_setfam_1(sK99))
      & k1_xboole_0 != sK99
      & r2_setfam_1(sK100,sK99) ) ),
    introduced(choice_axiom,[])).

fof(f1271,plain,
    ( ~ r1_tarski(k1_setfam_1(sK100),k1_setfam_1(sK99))
    & k1_xboole_0 != sK99
    & r2_setfam_1(sK100,sK99) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK99,sK100])],[f934,f1270])).

fof(f2160,plain,(
    r2_setfam_1(sK100,sK99) ),
    inference(cnf_transformation,[],[f1271])).

fof(f2146,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK96(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1264])).

fof(f571,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f947,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f571])).

fof(f948,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f947])).

fof(f2176,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f948])).

fof(f2174,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK101(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1274])).

fof(f2647,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X1,sK101(X0,X1)) ) ),
    inference(definition_unfolding,[],[f2174,f1282])).

fof(f511,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f872,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f511])).

fof(f1223,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f872])).

fof(f2084,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1223])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1968,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f2188,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f1968,f1282])).

fof(f2619,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | o_0_0_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f2084,f2188])).

fof(f2782,plain,(
    ! [X0] :
      ( r1_tarski(o_0_0_xboole_0,k3_subset_1(X0,o_0_0_xboole_0))
      | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f2619])).

fof(f2083,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1223])).

fof(f2620,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f2083,f2188])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2100,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f2624,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f2100,f1282])).

fof(f2162,plain,(
    ~ r1_tarski(k1_setfam_1(sK100),k1_setfam_1(sK99)) ),
    inference(cnf_transformation,[],[f1271])).

fof(f2161,plain,(
    k1_xboole_0 != sK99 ),
    inference(cnf_transformation,[],[f1271])).

fof(f2644,plain,(
    o_0_0_xboole_0 != sK99 ),
    inference(definition_unfolding,[],[f2161,f1282])).

cnf(c_885,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK101(X1,X0),X1)
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f2648])).

cnf(c_38214,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK101(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_857,plain,
    ( ~ r2_setfam_1(X0,X1)
    | r1_tarski(sK96(X0,X2),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f2147])).

cnf(c_873,negated_conjecture,
    ( r2_setfam_1(sK100,sK99) ),
    inference(cnf_transformation,[],[f2160])).

cnf(c_8491,plain,
    ( r1_tarski(sK96(X0,X1),X1)
    | ~ r2_hidden(X1,X2)
    | sK99 != X2
    | sK100 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_857,c_873])).

cnf(c_8492,plain,
    ( r1_tarski(sK96(sK100,X0),X0)
    | ~ r2_hidden(X0,sK99) ),
    inference(unflattening,[status(thm)],[c_8491])).

cnf(c_38178,plain,
    ( r1_tarski(sK96(sK100,X0),X0) = iProver_top
    | r2_hidden(X0,sK99) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8492])).

cnf(c_858,plain,
    ( ~ r2_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(sK96(X0,X2),X0) ),
    inference(cnf_transformation,[],[f2146])).

cnf(c_8479,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK96(X2,X0),X2)
    | sK99 != X1
    | sK100 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_858,c_873])).

cnf(c_8480,plain,
    ( ~ r2_hidden(X0,sK99)
    | r2_hidden(sK96(sK100,X0),sK100) ),
    inference(unflattening,[status(thm)],[c_8479])).

cnf(c_38179,plain,
    ( r2_hidden(X0,sK99) != iProver_top
    | r2_hidden(sK96(sK100,X0),sK100) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8480])).

cnf(c_887,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f2176])).

cnf(c_38212,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X2),X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_887])).

cnf(c_48076,plain,
    ( r1_tarski(sK96(sK100,X0),X1) != iProver_top
    | r1_tarski(k1_setfam_1(sK100),X1) = iProver_top
    | r2_hidden(X0,sK99) != iProver_top ),
    inference(superposition,[status(thm)],[c_38179,c_38212])).

cnf(c_48546,plain,
    ( r1_tarski(k1_setfam_1(sK100),X0) = iProver_top
    | r2_hidden(X0,sK99) != iProver_top ),
    inference(superposition,[status(thm)],[c_38178,c_48076])).

cnf(c_884,plain,
    ( ~ r1_tarski(X0,sK101(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f2647])).

cnf(c_38215,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X1,sK101(X0,X1)) != iProver_top
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_884])).

cnf(c_61258,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(k1_setfam_1(sK100),k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK101(X0,k1_setfam_1(sK100)),sK99) != iProver_top ),
    inference(superposition,[status(thm)],[c_48546,c_38215])).

cnf(c_62222,plain,
    ( sK99 = o_0_0_xboole_0
    | r1_tarski(k1_setfam_1(sK100),k1_setfam_1(sK99)) = iProver_top ),
    inference(superposition,[status(thm)],[c_38214,c_61258])).

cnf(c_26206,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_45418,plain,
    ( sK99 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK99 ),
    inference(instantiation,[status(thm)],[c_26206])).

cnf(c_45419,plain,
    ( sK99 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK99
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_45418])).

cnf(c_794,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))
    | r1_tarski(o_0_0_xboole_0,k3_subset_1(X0,o_0_0_xboole_0)) ),
    inference(cnf_transformation,[],[f2782])).

cnf(c_1102,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | r1_tarski(o_0_0_xboole_0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f2620])).

cnf(c_1099,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ r1_tarski(o_0_0_xboole_0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_811,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2624])).

cnf(c_1057,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_871,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK100),k1_setfam_1(sK99)) ),
    inference(cnf_transformation,[],[f2162])).

cnf(c_890,plain,
    ( r1_tarski(k1_setfam_1(sK100),k1_setfam_1(sK99)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_872,negated_conjecture,
    ( o_0_0_xboole_0 != sK99 ),
    inference(cnf_transformation,[],[f2644])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62222,c_45419,c_1102,c_1099,c_1057,c_890,c_872])).

%------------------------------------------------------------------------------
