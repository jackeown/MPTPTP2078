%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0597+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Theorem 43.41s
% Output     : CNFRefutation 43.41s
% Verified   : 
% Statistics : Number of formulae       :   54 (  98 expanded)
%              Number of clauses        :   31 (  35 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   16
%              Number of atoms          :  143 ( 327 expanded)
%              Number of equality atoms :   90 ( 186 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1617,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f1618,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1617])).

fof(f2095,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1618])).

fof(f3934,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2095])).

fof(f794,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
           => k9_relat_1(X1,X0) = k9_relat_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f795,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
             => k9_relat_1(X1,X0) = k9_relat_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f794])).

fof(f1475,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
          & k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f795])).

fof(f1476,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
          & k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1475])).

fof(f2014,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
          & k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( k9_relat_1(sK164,X0) != k9_relat_1(X1,X0)
        & k7_relat_1(sK164,X0) = k7_relat_1(X1,X0)
        & v1_relat_1(sK164) ) ) ),
    introduced(choice_axiom,[])).

fof(f2013,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
            & k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k9_relat_1(sK163,sK162) != k9_relat_1(X2,sK162)
          & k7_relat_1(sK163,sK162) = k7_relat_1(X2,sK162)
          & v1_relat_1(X2) )
      & v1_relat_1(sK163) ) ),
    introduced(choice_axiom,[])).

fof(f2015,plain,
    ( k9_relat_1(sK163,sK162) != k9_relat_1(sK164,sK162)
    & k7_relat_1(sK163,sK162) = k7_relat_1(sK164,sK162)
    & v1_relat_1(sK164)
    & v1_relat_1(sK163) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK162,sK163,sK164])],[f1476,f2014,f2013])).

fof(f3256,plain,(
    k7_relat_1(sK163,sK162) = k7_relat_1(sK164,sK162) ),
    inference(cnf_transformation,[],[f2015])).

fof(f779,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1453,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              | k7_relat_1(X0,X3) != k7_relat_1(X1,X3)
              | ~ r1_tarski(X2,X3) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f779])).

fof(f1454,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              | k7_relat_1(X0,X3) != k7_relat_1(X1,X3)
              | ~ r1_tarski(X2,X3) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1453])).

fof(f3238,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | k7_relat_1(X0,X3) != k7_relat_1(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1454])).

fof(f3255,plain,(
    v1_relat_1(sK164) ),
    inference(cnf_transformation,[],[f2015])).

fof(f3254,plain,(
    v1_relat_1(sK163) ),
    inference(cnf_transformation,[],[f2015])).

fof(f739,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1405,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f739])).

fof(f3191,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1405])).

fof(f3257,plain,(
    k9_relat_1(sK163,sK162) != k9_relat_1(sK164,sK162) ),
    inference(cnf_transformation,[],[f2015])).

cnf(c_68,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3934])).

cnf(c_36242,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_1213,negated_conjecture,
    ( k7_relat_1(sK163,sK162) = k7_relat_1(sK164,sK162) ),
    inference(cnf_transformation,[],[f3256])).

cnf(c_1196,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k7_relat_1(X3,X1) != k7_relat_1(X2,X1)
    | k7_relat_1(X3,X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f3238])).

cnf(c_35495,plain,
    ( k7_relat_1(X0,X1) != k7_relat_1(X2,X1)
    | k7_relat_1(X0,X3) = k7_relat_1(X2,X3)
    | r1_tarski(X3,X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1196])).

cnf(c_89812,plain,
    ( k7_relat_1(X0,X1) = k7_relat_1(sK164,X1)
    | k7_relat_1(X0,sK162) != k7_relat_1(sK163,sK162)
    | r1_tarski(X1,sK162) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK164) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_35495])).

cnf(c_1214,negated_conjecture,
    ( v1_relat_1(sK164) ),
    inference(cnf_transformation,[],[f3255])).

cnf(c_1302,plain,
    ( v1_relat_1(sK164) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1214])).

cnf(c_90505,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(X1,sK162) != iProver_top
    | k7_relat_1(X0,sK162) != k7_relat_1(sK163,sK162)
    | k7_relat_1(X0,X1) = k7_relat_1(sK164,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_89812,c_1302])).

cnf(c_90506,plain,
    ( k7_relat_1(X0,X1) = k7_relat_1(sK164,X1)
    | k7_relat_1(X0,sK162) != k7_relat_1(sK163,sK162)
    | r1_tarski(X1,sK162) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_90505])).

cnf(c_90518,plain,
    ( k7_relat_1(sK163,X0) = k7_relat_1(sK164,X0)
    | r1_tarski(X0,sK162) != iProver_top
    | v1_relat_1(sK163) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_90506])).

cnf(c_1215,negated_conjecture,
    ( v1_relat_1(sK163) ),
    inference(cnf_transformation,[],[f3254])).

cnf(c_1301,plain,
    ( v1_relat_1(sK163) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_90549,plain,
    ( r1_tarski(X0,sK162) != iProver_top
    | k7_relat_1(sK163,X0) = k7_relat_1(sK164,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_90518,c_1301])).

cnf(c_90550,plain,
    ( k7_relat_1(sK163,X0) = k7_relat_1(sK164,X0)
    | r1_tarski(X0,sK162) != iProver_top ),
    inference(renaming,[status(thm)],[c_90549])).

cnf(c_90557,plain,
    ( k7_relat_1(sK164,sK162) = k7_relat_1(sK163,sK162) ),
    inference(superposition,[status(thm)],[c_36242,c_90550])).

cnf(c_35482,plain,
    ( v1_relat_1(sK164) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1214])).

cnf(c_1149,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f3191])).

cnf(c_35536,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_143296,plain,
    ( k2_relat_1(k7_relat_1(sK164,X0)) = k9_relat_1(sK164,X0) ),
    inference(superposition,[status(thm)],[c_35482,c_35536])).

cnf(c_144911,plain,
    ( k2_relat_1(k7_relat_1(sK163,sK162)) = k9_relat_1(sK164,sK162) ),
    inference(superposition,[status(thm)],[c_90557,c_143296])).

cnf(c_35481,plain,
    ( v1_relat_1(sK163) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_143297,plain,
    ( k2_relat_1(k7_relat_1(sK163,X0)) = k9_relat_1(sK163,X0) ),
    inference(superposition,[status(thm)],[c_35481,c_35536])).

cnf(c_145714,plain,
    ( k9_relat_1(sK164,sK162) = k9_relat_1(sK163,sK162) ),
    inference(demodulation,[status(thm)],[c_144911,c_143297])).

cnf(c_17695,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_65208,plain,
    ( k9_relat_1(sK163,sK162) = k9_relat_1(sK163,sK162) ),
    inference(instantiation,[status(thm)],[c_17695])).

cnf(c_17696,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_46391,plain,
    ( k9_relat_1(sK164,sK162) != X0
    | k9_relat_1(sK163,sK162) != X0
    | k9_relat_1(sK163,sK162) = k9_relat_1(sK164,sK162) ),
    inference(instantiation,[status(thm)],[c_17696])).

cnf(c_65207,plain,
    ( k9_relat_1(sK164,sK162) != k9_relat_1(sK163,sK162)
    | k9_relat_1(sK163,sK162) = k9_relat_1(sK164,sK162)
    | k9_relat_1(sK163,sK162) != k9_relat_1(sK163,sK162) ),
    inference(instantiation,[status(thm)],[c_46391])).

cnf(c_1212,negated_conjecture,
    ( k9_relat_1(sK163,sK162) != k9_relat_1(sK164,sK162) ),
    inference(cnf_transformation,[],[f3257])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_145714,c_65208,c_65207,c_1212])).

%------------------------------------------------------------------------------
