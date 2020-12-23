%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0606+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Theorem 19.38s
% Output     : CNFRefutation 19.38s
% Verified   : 
% Statistics : Number of formulae       :   40 (  68 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  133 ( 305 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1332,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f650])).

fof(f1997,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1332])).

fof(f3122,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1997])).

fof(f787,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1480,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f787])).

fof(f1481,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1480])).

fof(f3301,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1481])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1318,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f3084,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1318])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1953,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f3045,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1953])).

fof(f814,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( r1_tarski(X2,X1)
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f815,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( r1_tarski(X2,X1)
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f814])).

fof(f1518,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f815])).

fof(f1519,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1518])).

fof(f2063,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(sK166,k7_relat_1(X1,X0))
        & r1_tarski(sK166,X1)
        & v4_relat_1(sK166,X0)
        & v1_relat_1(sK166) ) ) ),
    introduced(choice_axiom,[])).

fof(f2062,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK165,sK164))
          & r1_tarski(X2,sK165)
          & v4_relat_1(X2,sK164)
          & v1_relat_1(X2) )
      & v1_relat_1(sK165) ) ),
    introduced(choice_axiom,[])).

fof(f2064,plain,
    ( ~ r1_tarski(sK166,k7_relat_1(sK165,sK164))
    & r1_tarski(sK166,sK165)
    & v4_relat_1(sK166,sK164)
    & v1_relat_1(sK166)
    & v1_relat_1(sK165) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK164,sK165,sK166])],[f1519,f2063,f2062])).

fof(f3337,plain,(
    ~ r1_tarski(sK166,k7_relat_1(sK165,sK164)) ),
    inference(cnf_transformation,[],[f2064])).

fof(f3336,plain,(
    r1_tarski(sK166,sK165) ),
    inference(cnf_transformation,[],[f2064])).

fof(f3335,plain,(
    v4_relat_1(sK166,sK164) ),
    inference(cnf_transformation,[],[f2064])).

fof(f3334,plain,(
    v1_relat_1(sK166) ),
    inference(cnf_transformation,[],[f2064])).

fof(f3333,plain,(
    v1_relat_1(sK165) ),
    inference(cnf_transformation,[],[f2064])).

cnf(c_1032,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3122])).

cnf(c_57447,plain,
    ( ~ v4_relat_1(sK166,sK164)
    | r1_tarski(k1_relat_1(sK166),sK164)
    | ~ v1_relat_1(sK166) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1210,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3301])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3084])).

cnf(c_953,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3045])).

cnf(c_6354,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_993,c_953])).

cnf(c_6355,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_6354])).

cnf(c_55641,plain,
    ( ~ r1_tarski(k1_relat_1(sK166),sK164)
    | r1_tarski(sK166,k7_relat_1(sK165,sK164))
    | ~ r1_tarski(sK166,sK165)
    | ~ v1_relat_1(sK165) ),
    inference(instantiation,[status(thm)],[c_6355])).

cnf(c_1242,negated_conjecture,
    ( ~ r1_tarski(sK166,k7_relat_1(sK165,sK164)) ),
    inference(cnf_transformation,[],[f3337])).

cnf(c_1243,negated_conjecture,
    ( r1_tarski(sK166,sK165) ),
    inference(cnf_transformation,[],[f3336])).

cnf(c_1244,negated_conjecture,
    ( v4_relat_1(sK166,sK164) ),
    inference(cnf_transformation,[],[f3335])).

cnf(c_1245,negated_conjecture,
    ( v1_relat_1(sK166) ),
    inference(cnf_transformation,[],[f3334])).

cnf(c_1246,negated_conjecture,
    ( v1_relat_1(sK165) ),
    inference(cnf_transformation,[],[f3333])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57447,c_55641,c_1242,c_1243,c_1244,c_1245,c_1246])).

%------------------------------------------------------------------------------
