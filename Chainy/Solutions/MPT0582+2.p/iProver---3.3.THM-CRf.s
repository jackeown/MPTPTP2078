%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0582+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 19.58s
% Output     : CNFRefutation 19.58s
% Verified   : 
% Statistics : Number of formulae       :   49 (  77 expanded)
%              Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 308 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f773,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f774,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r1_tarski(X2,X1)
                & r1_tarski(k1_relat_1(X2),X0) )
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f773])).

fof(f1424,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f774])).

fof(f1425,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1424])).

fof(f1963,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(sK162,k7_relat_1(X1,X0))
        & r1_tarski(sK162,X1)
        & r1_tarski(k1_relat_1(sK162),X0)
        & v1_relat_1(sK162) ) ) ),
    introduced(choice_axiom,[])).

fof(f1962,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & r1_tarski(k1_relat_1(X2),X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK161,sK160))
          & r1_tarski(X2,sK161)
          & r1_tarski(k1_relat_1(X2),sK160)
          & v1_relat_1(X2) )
      & v1_relat_1(sK161) ) ),
    introduced(choice_axiom,[])).

fof(f1964,plain,
    ( ~ r1_tarski(sK162,k7_relat_1(sK161,sK160))
    & r1_tarski(sK162,sK161)
    & r1_tarski(k1_relat_1(sK162),sK160)
    & v1_relat_1(sK162)
    & v1_relat_1(sK161) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK160,sK161,sK162])],[f1425,f1963,f1962])).

fof(f3183,plain,(
    r1_tarski(k1_relat_1(sK162),sK160) ),
    inference(cnf_transformation,[],[f1964])).

fof(f839,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1504,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f839])).

fof(f1505,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1504])).

fof(f3270,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1505])).

fof(f3182,plain,(
    v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f1964])).

fof(f695,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1332,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f695])).

fof(f1333,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1332])).

fof(f3091,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1333])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1279,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2986,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1279])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1865,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2947,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1865])).

fof(f3185,plain,(
    ~ r1_tarski(sK162,k7_relat_1(sK161,sK160)) ),
    inference(cnf_transformation,[],[f1964])).

fof(f3184,plain,(
    r1_tarski(sK162,sK161) ),
    inference(cnf_transformation,[],[f1964])).

fof(f3181,plain,(
    v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f1964])).

cnf(c_1188,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK162),sK160) ),
    inference(cnf_transformation,[],[f3183])).

cnf(c_34982,plain,
    ( r1_tarski(k1_relat_1(sK162),sK160) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1188])).

cnf(c_1275,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f3270])).

cnf(c_34916,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_51055,plain,
    ( k7_relat_1(sK162,sK160) = sK162
    | v1_relat_1(sK162) != iProver_top ),
    inference(superposition,[status(thm)],[c_34982,c_34916])).

cnf(c_1189,negated_conjecture,
    ( v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3182])).

cnf(c_1279,plain,
    ( v1_relat_1(sK162) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1189])).

cnf(c_51314,plain,
    ( k7_relat_1(sK162,sK160) = sK162 ),
    inference(global_propositional_subsumption,[status(thm)],[c_51055,c_1279])).

cnf(c_1096,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3091])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2986])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2947])).

cnf(c_10198,plain,
    ( r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1096,c_991,c_951])).

cnf(c_10199,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_10198])).

cnf(c_34872,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10199])).

cnf(c_51319,plain,
    ( r1_tarski(sK162,X0) != iProver_top
    | r1_tarski(sK162,k7_relat_1(X0,sK160)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_51314,c_34872])).

cnf(c_1186,negated_conjecture,
    ( ~ r1_tarski(sK162,k7_relat_1(sK161,sK160)) ),
    inference(cnf_transformation,[],[f3185])).

cnf(c_34984,plain,
    ( r1_tarski(sK162,k7_relat_1(sK161,sK160)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1186])).

cnf(c_51345,plain,
    ( r1_tarski(sK162,sK161) != iProver_top
    | v1_relat_1(sK161) != iProver_top ),
    inference(superposition,[status(thm)],[c_51319,c_34984])).

cnf(c_1187,negated_conjecture,
    ( r1_tarski(sK162,sK161) ),
    inference(cnf_transformation,[],[f3184])).

cnf(c_1281,plain,
    ( r1_tarski(sK162,sK161) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_1190,negated_conjecture,
    ( v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3181])).

cnf(c_1278,plain,
    ( v1_relat_1(sK161) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51345,c_1281,c_1278])).

%------------------------------------------------------------------------------
