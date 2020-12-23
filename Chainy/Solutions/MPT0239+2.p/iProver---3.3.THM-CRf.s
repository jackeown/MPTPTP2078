%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0239+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:29 EST 2020

% Result     : Theorem 7.99s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 360 expanded)
%              Number of clauses        :   37 ( 110 expanded)
%              Number of leaves         :    5 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  192 (1530 expanded)
%              Number of equality atoms :  110 ( 794 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f549,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f550,plain,(
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
    inference(rectify,[],[f549])).

fof(f551,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK20(X0,X1) != X0
          | ~ r2_hidden(sK20(X0,X1),X1) )
        & ( sK20(X0,X1) = X0
          | r2_hidden(sK20(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f552,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK20(X0,X1) != X0
            | ~ r2_hidden(sK20(X0,X1),X1) )
          & ( sK20(X0,X1) = X0
            | r2_hidden(sK20(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f550,f551])).

fof(f831,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f552])).

fof(f1351,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f831])).

fof(f1352,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1351])).

fof(f306,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f592,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f306])).

fof(f593,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f592])).

fof(f1007,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f593])).

fof(f331,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f332,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f331])).

fof(f474,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f332])).

fof(f595,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f474])).

fof(f596,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f595])).

fof(f597,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
        & ( ( X1 = X3
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) )
   => ( ( sK29 != sK31
        | sK28 != sK30
        | ~ r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) )
      & ( ( sK29 = sK31
          & sK28 = sK30 )
        | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) ) ) ),
    introduced(choice_axiom,[])).

fof(f598,plain,
    ( ( sK29 != sK31
      | sK28 != sK30
      | ~ r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) )
    & ( ( sK29 = sK31
        & sK28 = sK30 )
      | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30,sK31])],[f596,f597])).

fof(f1035,plain,
    ( sK29 = sK31
    | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) ),
    inference(cnf_transformation,[],[f598])).

fof(f1006,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f593])).

fof(f1036,plain,
    ( sK29 != sK31
    | sK28 != sK30
    | ~ r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) ),
    inference(cnf_transformation,[],[f598])).

fof(f830,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f552])).

fof(f1353,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f830])).

fof(f1005,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f593])).

fof(f1034,plain,
    ( sK28 = sK30
    | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) ),
    inference(cnf_transformation,[],[f598])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1352])).

cnf(c_12958,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_394,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1007])).

cnf(c_12881,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_424,negated_conjecture,
    ( r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31)))
    | sK29 = sK31 ),
    inference(cnf_transformation,[],[f1035])).

cnf(c_12870,plain,
    ( sK29 = sK31
    | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_395,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f1006])).

cnf(c_12880,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_15136,plain,
    ( sK31 = sK29
    | r2_hidden(sK29,k1_tarski(sK31)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12870,c_12880])).

cnf(c_423,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31)))
    | sK28 != sK30
    | sK29 != sK31 ),
    inference(cnf_transformation,[],[f1036])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f1353])).

cnf(c_13782,plain,
    ( ~ r2_hidden(sK28,k1_tarski(sK30))
    | sK28 = sK30 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_13783,plain,
    ( sK28 = sK30
    | r2_hidden(sK28,k1_tarski(sK30)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13782])).

cnf(c_14096,plain,
    ( ~ r2_hidden(sK29,k1_tarski(sK31))
    | sK29 = sK31 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_14097,plain,
    ( sK29 = sK31
    | r2_hidden(sK29,k1_tarski(sK31)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14096])).

cnf(c_14508,plain,
    ( r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31)))
    | ~ r2_hidden(sK28,k1_tarski(sK30))
    | ~ r2_hidden(sK29,k1_tarski(sK31)) ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_396,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1005])).

cnf(c_12879,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_14578,plain,
    ( sK31 = sK29
    | r2_hidden(sK28,k1_tarski(sK30)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12870,c_12879])).

cnf(c_14580,plain,
    ( r2_hidden(sK28,k1_tarski(sK30))
    | sK31 = sK29 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14578])).

cnf(c_15138,plain,
    ( r2_hidden(sK29,k1_tarski(sK31))
    | sK31 = sK29 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15136])).

cnf(c_15855,plain,
    ( sK31 = sK29 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15136,c_423,c_13783,c_14097,c_14508,c_14578,c_14580,c_15138])).

cnf(c_12871,plain,
    ( sK28 != sK30
    | sK29 != sK31
    | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_15859,plain,
    ( sK30 != sK28
    | sK29 != sK29
    | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK29))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15855,c_12871])).

cnf(c_15860,plain,
    ( sK30 != sK28
    | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK29))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15859])).

cnf(c_425,negated_conjecture,
    ( r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31)))
    | sK28 = sK30 ),
    inference(cnf_transformation,[],[f1034])).

cnf(c_12869,plain,
    ( sK28 = sK30
    | r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK31))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_15137,plain,
    ( sK30 = sK28
    | r2_hidden(sK29,k1_tarski(sK31)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12869,c_12880])).

cnf(c_14579,plain,
    ( sK30 = sK28
    | r2_hidden(sK28,k1_tarski(sK30)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12869,c_12879])).

cnf(c_14581,plain,
    ( r2_hidden(sK28,k1_tarski(sK30))
    | sK30 = sK28 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14579])).

cnf(c_15139,plain,
    ( r2_hidden(sK29,k1_tarski(sK31))
    | sK30 = sK28 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15137])).

cnf(c_15873,plain,
    ( sK30 = sK28 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15137,c_423,c_13783,c_14097,c_14508,c_14579,c_14581,c_15139])).

cnf(c_16107,plain,
    ( r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK30),k1_tarski(sK29))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15860,c_423,c_13783,c_14097,c_14508,c_14579,c_14581,c_15137,c_15139])).

cnf(c_16111,plain,
    ( r2_hidden(k4_tarski(sK28,sK29),k2_zfmisc_1(k1_tarski(sK28),k1_tarski(sK29))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16107,c_15873])).

cnf(c_16822,plain,
    ( r2_hidden(sK28,k1_tarski(sK28)) != iProver_top
    | r2_hidden(sK29,k1_tarski(sK29)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12881,c_16111])).

cnf(c_17515,plain,
    ( r2_hidden(sK29,k1_tarski(sK29)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12958,c_16822])).

cnf(c_17609,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_12958,c_17515])).

%------------------------------------------------------------------------------
