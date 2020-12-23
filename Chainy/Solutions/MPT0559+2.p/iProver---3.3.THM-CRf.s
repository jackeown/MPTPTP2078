%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0559+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 18.67s
% Output     : CNFRefutation 18.67s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 (  90 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f801,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1433,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f801])).

fof(f3139,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1433])).

fof(f739,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1357,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f739])).

fof(f1358,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1357])).

fof(f3058,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1358])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1250,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2908,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1250])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1804,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2869,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1804])).

fof(f744,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f745,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f744])).

fof(f1364,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f745])).

fof(f1885,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK157,sK155),sK156),k9_relat_1(sK157,sK156))
      & v1_relat_1(sK157) ) ),
    introduced(choice_axiom,[])).

fof(f1886,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK157,sK155),sK156),k9_relat_1(sK157,sK156))
    & v1_relat_1(sK157) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK155,sK156,sK157])],[f1364,f1885])).

fof(f3064,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK157,sK155),sK156),k9_relat_1(sK157,sK156)) ),
    inference(cnf_transformation,[],[f1886])).

fof(f3063,plain,(
    v1_relat_1(sK157) ),
    inference(cnf_transformation,[],[f1886])).

cnf(c_1222,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3139])).

cnf(c_69519,plain,
    ( r1_tarski(k7_relat_1(sK157,sK155),sK157)
    | ~ v1_relat_1(sK157) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_1141,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3058])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2908])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2869])).

cnf(c_5821,plain,
    ( r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_991,c_951])).

cnf(c_5822,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_5821])).

cnf(c_61147,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK157,sK155),sK156),k9_relat_1(sK157,sK156))
    | ~ r1_tarski(k7_relat_1(sK157,sK155),sK157)
    | ~ v1_relat_1(sK157) ),
    inference(instantiation,[status(thm)],[c_5822])).

cnf(c_1146,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK157,sK155),sK156),k9_relat_1(sK157,sK156)) ),
    inference(cnf_transformation,[],[f3064])).

cnf(c_1147,negated_conjecture,
    ( v1_relat_1(sK157) ),
    inference(cnf_transformation,[],[f3063])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_69519,c_61147,c_1146,c_1147])).

%------------------------------------------------------------------------------
