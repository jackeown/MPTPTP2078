%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0576+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 23.53s
% Output     : CNFRefutation 23.53s
% Verified   : 
% Statistics : Number of formulae       :   49 (  77 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  150 ( 322 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f764,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1404,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f764])).

fof(f1405,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1404])).

fof(f3148,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1405])).

fof(f765,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1406,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f765])).

fof(f1407,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1406])).

fof(f3149,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1272,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2965,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1272])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1849,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2926,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1849])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f890,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f891,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f890])).

fof(f2079,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f891])).

fof(f766,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f767,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f766])).

fof(f1408,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f767])).

fof(f1409,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1408])).

fof(f1942,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(sK162,X1))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK162)
        & v1_relat_1(sK162) ) ) ),
    introduced(choice_axiom,[])).

fof(f1941,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(X3,sK160))
          & r1_tarski(sK159,sK160)
          & r1_tarski(sK161,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK161) ) ),
    introduced(choice_axiom,[])).

fof(f1943,plain,
    ( ~ r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK162,sK160))
    & r1_tarski(sK159,sK160)
    & r1_tarski(sK161,sK162)
    & v1_relat_1(sK162)
    & v1_relat_1(sK161) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK159,sK160,sK161,sK162])],[f1409,f1942,f1941])).

fof(f3154,plain,(
    ~ r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK162,sK160)) ),
    inference(cnf_transformation,[],[f1943])).

fof(f3153,plain,(
    r1_tarski(sK159,sK160) ),
    inference(cnf_transformation,[],[f1943])).

fof(f3152,plain,(
    r1_tarski(sK161,sK162) ),
    inference(cnf_transformation,[],[f1943])).

fof(f3151,plain,(
    v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f1943])).

fof(f3150,plain,(
    v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f1943])).

cnf(c_1174,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f3148])).

cnf(c_57698,plain,
    ( r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK161,X0))
    | ~ r1_tarski(sK159,X0)
    | ~ v1_relat_1(sK161) ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_84595,plain,
    ( r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK161,sK160))
    | ~ r1_tarski(sK159,sK160)
    | ~ v1_relat_1(sK161) ),
    inference(instantiation,[status(thm)],[c_57698])).

cnf(c_1175,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3149])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2965])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2926])).

cnf(c_10058,plain,
    ( r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1175,c_991,c_951])).

cnf(c_10059,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_10058])).

cnf(c_84372,plain,
    ( r1_tarski(k10_relat_1(sK161,sK160),k10_relat_1(sK162,sK160))
    | ~ r1_tarski(sK161,sK162)
    | ~ v1_relat_1(sK162) ),
    inference(instantiation,[status(thm)],[c_10059])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f2079])).

cnf(c_44562,plain,
    ( ~ r1_tarski(X0,k10_relat_1(sK162,sK160))
    | ~ r1_tarski(k10_relat_1(sK161,sK159),X0)
    | r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK162,sK160)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_57697,plain,
    ( ~ r1_tarski(k10_relat_1(sK161,X0),k10_relat_1(sK162,sK160))
    | r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK162,sK160))
    | ~ r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK161,X0)) ),
    inference(instantiation,[status(thm)],[c_44562])).

cnf(c_84371,plain,
    ( ~ r1_tarski(k10_relat_1(sK161,sK160),k10_relat_1(sK162,sK160))
    | r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK162,sK160))
    | ~ r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK161,sK160)) ),
    inference(instantiation,[status(thm)],[c_57697])).

cnf(c_1176,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK161,sK159),k10_relat_1(sK162,sK160)) ),
    inference(cnf_transformation,[],[f3154])).

cnf(c_1177,negated_conjecture,
    ( r1_tarski(sK159,sK160) ),
    inference(cnf_transformation,[],[f3153])).

cnf(c_1178,negated_conjecture,
    ( r1_tarski(sK161,sK162) ),
    inference(cnf_transformation,[],[f3152])).

cnf(c_1179,negated_conjecture,
    ( v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3151])).

cnf(c_1180,negated_conjecture,
    ( v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3150])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_84595,c_84372,c_84371,c_1176,c_1177,c_1178,c_1179,c_1180])).

%------------------------------------------------------------------------------
