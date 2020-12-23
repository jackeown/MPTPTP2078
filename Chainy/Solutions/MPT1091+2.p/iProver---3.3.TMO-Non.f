%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1091+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Timeout 59.76s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   81 ( 142 expanded)
%              Number of clauses        :   33 (  36 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  260 ( 627 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1731,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3680,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1731])).

fof(f3681,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f3680])).

fof(f8554,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3681])).

fof(f1720,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3667,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1720])).

fof(f8503,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f3667])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8143,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f10228,plain,(
    ! [X0] :
      ( v1_finset_1(k9_setfam_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(definition_unfolding,[],[f8503,f8143])).

fof(f320,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5638,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f320])).

fof(f8849,plain,(
    ! [X0] : r1_tarski(X0,k9_setfam_1(k3_tarski(X0))) ),
    inference(definition_unfolding,[],[f5638,f8143])).

fof(f433,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1996,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f433])).

fof(f3961,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK106(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK106(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3962,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK106(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK106(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK106])],[f1996,f3961])).

fof(f5833,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK106(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3962])).

fof(f1063,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2785,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1063])).

fof(f4398,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f2785])).

fof(f4399,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f4398])).

fof(f4400,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK274(X0),X0)
        & r2_hidden(sK274(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4401,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK274(X0),X0)
          & r2_hidden(sK274(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK274])],[f4399,f4400])).

fof(f6931,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK274(X0),X0) ) ),
    inference(cnf_transformation,[],[f4401])).

fof(f1738,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1739,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f1738])).

fof(f3690,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f1739])).

fof(f5189,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(nnf_transformation,[],[f3690])).

fof(f5190,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(flattening,[],[f5189])).

fof(f5191,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(rectify,[],[f5190])).

fof(f5193,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK626)
        & r2_hidden(sK626,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f5192,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ? [X1] :
              ( ~ v1_finset_1(X1)
              & r2_hidden(X1,X0) )
          | ~ v1_finset_1(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | ( ! [X2] :
                ( v1_finset_1(X2)
                | ~ r2_hidden(X2,X0) )
            & v1_finset_1(X0) ) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK625))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,sK625) )
        | ~ v1_finset_1(sK625) )
      & ( v1_finset_1(k3_tarski(sK625))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,sK625) )
          & v1_finset_1(sK625) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f5194,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK625))
      | ( ~ v1_finset_1(sK626)
        & r2_hidden(sK626,sK625) )
      | ~ v1_finset_1(sK625) )
    & ( v1_finset_1(k3_tarski(sK625))
      | ( ! [X2] :
            ( v1_finset_1(X2)
            | ~ r2_hidden(X2,sK625) )
        & v1_finset_1(sK625) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK625,sK626])],[f5191,f5193,f5192])).

fof(f8563,plain,(
    ! [X2] :
      ( v1_finset_1(k3_tarski(sK625))
      | v1_finset_1(X2)
      | ~ r2_hidden(X2,sK625) ) ),
    inference(cnf_transformation,[],[f5194])).

fof(f8562,plain,
    ( v1_finset_1(k3_tarski(sK625))
    | v1_finset_1(sK625) ),
    inference(cnf_transformation,[],[f5194])).

fof(f1725,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3672,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1725])).

fof(f3673,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f3672])).

fof(f5144,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK607(X0))
        & r2_hidden(sK607(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f5145,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK607(X0))
        & r2_hidden(sK607(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK607])],[f3673,f5144])).

fof(f8509,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | r2_hidden(sK607(X0),X0)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f5145])).

fof(f8510,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(sK607(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f5145])).

fof(f441,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1999,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f441])).

fof(f5842,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1999])).

fof(f8565,plain,
    ( ~ v1_finset_1(k3_tarski(sK625))
    | ~ v1_finset_1(sK626)
    | ~ v1_finset_1(sK625) ),
    inference(cnf_transformation,[],[f5194])).

fof(f8564,plain,
    ( ~ v1_finset_1(k3_tarski(sK625))
    | r2_hidden(sK626,sK625)
    | ~ v1_finset_1(sK625) ),
    inference(cnf_transformation,[],[f5194])).

cnf(c_3333,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_finset_1(X1)
    | v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f8554])).

cnf(c_140823,plain,
    ( ~ r1_tarski(sK626,X0)
    | ~ v1_finset_1(X0)
    | v1_finset_1(sK626) ),
    inference(instantiation,[status(thm)],[c_3333])).

cnf(c_150801,plain,
    ( ~ r1_tarski(sK626,k3_tarski(X0))
    | ~ v1_finset_1(k3_tarski(X0))
    | v1_finset_1(sK626) ),
    inference(instantiation,[status(thm)],[c_140823])).

cnf(c_215113,plain,
    ( ~ r1_tarski(sK626,k3_tarski(sK625))
    | ~ v1_finset_1(k3_tarski(sK625))
    | v1_finset_1(sK626) ),
    inference(instantiation,[status(thm)],[c_150801])).

cnf(c_3282,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f10228])).

cnf(c_207614,plain,
    ( ~ v1_finset_1(k3_tarski(sK625))
    | v1_finset_1(k9_setfam_1(k3_tarski(sK625))) ),
    inference(instantiation,[status(thm)],[c_3282])).

cnf(c_431,plain,
    ( r1_tarski(X0,k9_setfam_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f8849])).

cnf(c_151153,plain,
    ( r1_tarski(sK625,k9_setfam_1(k3_tarski(sK625))) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_142306,plain,
    ( ~ r1_tarski(sK625,X0)
    | ~ v1_finset_1(X0)
    | v1_finset_1(sK625) ),
    inference(instantiation,[status(thm)],[c_3333])).

cnf(c_151152,plain,
    ( ~ r1_tarski(sK625,k9_setfam_1(k3_tarski(sK625)))
    | ~ v1_finset_1(k9_setfam_1(k3_tarski(sK625)))
    | v1_finset_1(sK625) ),
    inference(instantiation,[status(thm)],[c_142306])).

cnf(c_627,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK106(X1),X1) ),
    inference(cnf_transformation,[],[f5833])).

cnf(c_1721,plain,
    ( r2_hidden(sK274(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f6931])).

cnf(c_141085,plain,
    ( r2_hidden(sK106(X0),X0)
    | v1_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_627,c_1721])).

cnf(c_3343,negated_conjecture,
    ( ~ r2_hidden(X0,sK625)
    | v1_finset_1(X0)
    | v1_finset_1(k3_tarski(sK625)) ),
    inference(cnf_transformation,[],[f8563])).

cnf(c_142476,plain,
    ( v1_finset_1(sK106(sK625))
    | v1_finset_1(k3_tarski(sK625))
    | v1_ordinal1(sK625) ),
    inference(resolution,[status(thm)],[c_141085,c_3343])).

cnf(c_3344,negated_conjecture,
    ( v1_finset_1(k3_tarski(sK625))
    | v1_finset_1(sK625) ),
    inference(cnf_transformation,[],[f8562])).

cnf(c_3289,plain,
    ( r2_hidden(sK607(X0),X0)
    | ~ v1_finset_1(X0)
    | v1_finset_1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f8509])).

cnf(c_97016,plain,
    ( r2_hidden(sK607(X0),X0) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_finset_1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3289])).

cnf(c_96962,plain,
    ( r2_hidden(X0,sK625) != iProver_top
    | v1_finset_1(X0) = iProver_top
    | v1_finset_1(k3_tarski(sK625)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3343])).

cnf(c_141048,plain,
    ( v1_finset_1(sK607(sK625)) = iProver_top
    | v1_finset_1(k3_tarski(sK625)) = iProver_top
    | v1_finset_1(sK625) != iProver_top ),
    inference(superposition,[status(thm)],[c_97016,c_96962])).

cnf(c_3345,plain,
    ( v1_finset_1(k3_tarski(sK625)) = iProver_top
    | v1_finset_1(sK625) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3344])).

cnf(c_141517,plain,
    ( v1_finset_1(k3_tarski(sK625)) = iProver_top
    | v1_finset_1(sK607(sK625)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_141048,c_3345])).

cnf(c_141518,plain,
    ( v1_finset_1(sK607(sK625)) = iProver_top
    | v1_finset_1(k3_tarski(sK625)) = iProver_top ),
    inference(renaming,[status(thm)],[c_141517])).

cnf(c_3288,plain,
    ( ~ v1_finset_1(X0)
    | ~ v1_finset_1(sK607(X0))
    | v1_finset_1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f8510])).

cnf(c_97017,plain,
    ( v1_finset_1(X0) != iProver_top
    | v1_finset_1(sK607(X0)) != iProver_top
    | v1_finset_1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3288])).

cnf(c_142488,plain,
    ( v1_finset_1(k3_tarski(sK625)) = iProver_top
    | v1_finset_1(sK625) != iProver_top ),
    inference(superposition,[status(thm)],[c_141518,c_97017])).

cnf(c_142489,plain,
    ( v1_finset_1(k3_tarski(sK625))
    | ~ v1_finset_1(sK625) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_142488])).

cnf(c_142491,plain,
    ( v1_finset_1(k3_tarski(sK625)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_142476,c_3344,c_142489])).

cnf(c_635,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f5842])).

cnf(c_140876,plain,
    ( r1_tarski(sK626,k3_tarski(sK625))
    | ~ r2_hidden(sK626,sK625) ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_3341,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(sK625))
    | ~ v1_finset_1(sK626)
    | ~ v1_finset_1(sK625) ),
    inference(cnf_transformation,[],[f8565])).

cnf(c_3342,negated_conjecture,
    ( r2_hidden(sK626,sK625)
    | ~ v1_finset_1(k3_tarski(sK625))
    | ~ v1_finset_1(sK625) ),
    inference(cnf_transformation,[],[f8564])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_215113,c_207614,c_151153,c_151152,c_142491,c_140876,c_3341,c_3342])).

%------------------------------------------------------------------------------
