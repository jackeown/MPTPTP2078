%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0494+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:42 EST 2020

% Result     : Theorem 15.39s
% Output     : CNFRefutation 15.39s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 142 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f732,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1278,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f732])).

fof(f2872,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1278])).

fof(f703,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f703])).

fof(f1247,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1246])).

fof(f2830,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1247])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1175,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2727,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1175])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1641,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2688,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1641])).

fof(f736,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f737,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f736])).

fof(f1283,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f737])).

fof(f1720,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),sK156),k5_relat_1(X1,sK156))
        & v1_relat_1(sK156) ) ) ),
    introduced(choice_axiom,[])).

fof(f1719,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK155,sK154),X2),k5_relat_1(sK155,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK155) ) ),
    introduced(choice_axiom,[])).

fof(f1721,plain,
    ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK155,sK154),sK156),k5_relat_1(sK155,sK156))
    & v1_relat_1(sK156)
    & v1_relat_1(sK155) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK154,sK155,sK156])],[f1283,f1720,f1719])).

fof(f2878,plain,(
    ~ r1_tarski(k5_relat_1(k7_relat_1(sK155,sK154),sK156),k5_relat_1(sK155,sK156)) ),
    inference(cnf_transformation,[],[f1721])).

fof(f2877,plain,(
    v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f1721])).

fof(f2876,plain,(
    v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1721])).

cnf(c_1136,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2872])).

cnf(c_50336,plain,
    ( r1_tarski(k7_relat_1(sK155,sK154),sK155)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_1094,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2830])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2727])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2688])).

cnf(c_5241,plain,
    ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1094,c_991,c_951])).

cnf(c_5242,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_5241])).

cnf(c_48968,plain,
    ( r1_tarski(k5_relat_1(k7_relat_1(sK155,sK154),sK156),k5_relat_1(sK155,sK156))
    | ~ r1_tarski(k7_relat_1(sK155,sK154),sK155)
    | ~ v1_relat_1(sK156)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_5242])).

cnf(c_1140,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK155,sK154),sK156),k5_relat_1(sK155,sK156)) ),
    inference(cnf_transformation,[],[f2878])).

cnf(c_1141,negated_conjecture,
    ( v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f2877])).

cnf(c_1142,negated_conjecture,
    ( v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f2876])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50336,c_48968,c_1140,c_1141,c_1142])).

%------------------------------------------------------------------------------
