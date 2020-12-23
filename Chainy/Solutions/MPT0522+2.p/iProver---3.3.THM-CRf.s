%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0522+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:43 EST 2020

% Result     : Theorem 18.55s
% Output     : CNFRefutation 18.55s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 149 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f693,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1264,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f2903,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1264])).

fof(f728,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1308,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f728])).

fof(f1309,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1308])).

fof(f2945,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1309])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1207,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2807,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1207])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1713,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2768,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1713])).

fof(f698,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f699,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f698])).

fof(f1270,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f699])).

fof(f1784,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,sK153)),k5_relat_1(X1,sK153))
        & v1_relat_1(sK153) ) ) ),
    introduced(choice_axiom,[])).

fof(f1783,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK152,k8_relat_1(sK151,X2)),k5_relat_1(sK152,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1785,plain,
    ( ~ r1_tarski(k5_relat_1(sK152,k8_relat_1(sK151,sK153)),k5_relat_1(sK152,sK153))
    & v1_relat_1(sK153)
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152,sK153])],[f1270,f1784,f1783])).

fof(f2910,plain,(
    ~ r1_tarski(k5_relat_1(sK152,k8_relat_1(sK151,sK153)),k5_relat_1(sK152,sK153)) ),
    inference(cnf_transformation,[],[f1785])).

fof(f2909,plain,(
    v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f1785])).

fof(f2908,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1785])).

cnf(c_1087,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f2903])).

cnf(c_66467,plain,
    ( r1_tarski(k8_relat_1(sK151,sK153),sK153)
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_1129,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2945])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2807])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2768])).

cnf(c_5485,plain,
    ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1129,c_991,c_951])).

cnf(c_5486,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_5485])).

cnf(c_48955,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5486])).

cnf(c_1092,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK152,k8_relat_1(sK151,sK153)),k5_relat_1(sK152,sK153)) ),
    inference(cnf_transformation,[],[f2910])).

cnf(c_49029,plain,
    ( r1_tarski(k5_relat_1(sK152,k8_relat_1(sK151,sK153)),k5_relat_1(sK152,sK153)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_57585,plain,
    ( r1_tarski(k8_relat_1(sK151,sK153),sK153) != iProver_top
    | v1_relat_1(sK153) != iProver_top
    | v1_relat_1(sK152) != iProver_top ),
    inference(superposition,[status(thm)],[c_48955,c_49029])).

cnf(c_57586,plain,
    ( ~ r1_tarski(k8_relat_1(sK151,sK153),sK153)
    | ~ v1_relat_1(sK153)
    | ~ v1_relat_1(sK152) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_57585])).

cnf(c_1093,negated_conjecture,
    ( v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f2909])).

cnf(c_1094,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2908])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66467,c_57586,c_1093,c_1094])).

%------------------------------------------------------------------------------
