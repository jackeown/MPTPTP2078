%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0495+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:42 EST 2020

% Result     : Theorem 15.14s
% Output     : CNFRefutation 15.14s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1279,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f732])).

fof(f2874,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1279])).

fof(f702,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f702])).

fof(f1246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1245])).

fof(f2831,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1246])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1176,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2729,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1176])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1643,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2690,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1643])).

fof(f737,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f738,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f737])).

fof(f1285,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f1722,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X1,k7_relat_1(sK156,X0)),k5_relat_1(X1,sK156))
        & v1_relat_1(sK156) ) ) ),
    introduced(choice_axiom,[])).

fof(f1721,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK155,k7_relat_1(X2,sK154)),k5_relat_1(sK155,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK155) ) ),
    introduced(choice_axiom,[])).

fof(f1723,plain,
    ( ~ r1_tarski(k5_relat_1(sK155,k7_relat_1(sK156,sK154)),k5_relat_1(sK155,sK156))
    & v1_relat_1(sK156)
    & v1_relat_1(sK155) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK154,sK155,sK156])],[f1285,f1722,f1721])).

fof(f2881,plain,(
    ~ r1_tarski(k5_relat_1(sK155,k7_relat_1(sK156,sK154)),k5_relat_1(sK155,sK156)) ),
    inference(cnf_transformation,[],[f1723])).

fof(f2880,plain,(
    v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f1723])).

fof(f2879,plain,(
    v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1723])).

cnf(c_1136,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2874])).

cnf(c_50372,plain,
    ( r1_tarski(k7_relat_1(sK156,sK154),sK156)
    | ~ v1_relat_1(sK156) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_1093,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2831])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2729])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2690])).

cnf(c_5253,plain,
    ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1093,c_991,c_951])).

cnf(c_5254,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_5253])).

cnf(c_49004,plain,
    ( r1_tarski(k5_relat_1(sK155,k7_relat_1(sK156,sK154)),k5_relat_1(sK155,sK156))
    | ~ r1_tarski(k7_relat_1(sK156,sK154),sK156)
    | ~ v1_relat_1(sK156)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_5254])).

cnf(c_1141,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK155,k7_relat_1(sK156,sK154)),k5_relat_1(sK155,sK156)) ),
    inference(cnf_transformation,[],[f2881])).

cnf(c_1142,negated_conjecture,
    ( v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f2880])).

cnf(c_1143,negated_conjecture,
    ( v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f2879])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50372,c_49004,c_1141,c_1142,c_1143])).

%------------------------------------------------------------------------------
