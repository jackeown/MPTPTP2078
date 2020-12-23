%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0556+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 23.66s
% Output     : CNFRefutation 23.66s
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
fof(f738,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1352,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f1353,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1352])).

fof(f3052,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1353])).

fof(f739,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1354,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f739])).

fof(f1355,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1354])).

fof(f3053,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1355])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1247,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2903,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1247])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1798,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2864,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1798])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f865,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f866,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f865])).

fof(f2017,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f866])).

fof(f740,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f741,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f740])).

fof(f1356,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f741])).

fof(f1357,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1356])).

fof(f1880,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(sK158,X1))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK158)
        & v1_relat_1(sK158) ) ) ),
    introduced(choice_axiom,[])).

fof(f1879,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(X3,sK156))
          & r1_tarski(sK155,sK156)
          & r1_tarski(sK157,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK157) ) ),
    introduced(choice_axiom,[])).

fof(f1881,plain,
    ( ~ r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK158,sK156))
    & r1_tarski(sK155,sK156)
    & r1_tarski(sK157,sK158)
    & v1_relat_1(sK158)
    & v1_relat_1(sK157) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK155,sK156,sK157,sK158])],[f1357,f1880,f1879])).

fof(f3058,plain,(
    ~ r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK158,sK156)) ),
    inference(cnf_transformation,[],[f1881])).

fof(f3057,plain,(
    r1_tarski(sK155,sK156) ),
    inference(cnf_transformation,[],[f1881])).

fof(f3056,plain,(
    r1_tarski(sK157,sK158) ),
    inference(cnf_transformation,[],[f1881])).

fof(f3055,plain,(
    v1_relat_1(sK158) ),
    inference(cnf_transformation,[],[f1881])).

fof(f3054,plain,(
    v1_relat_1(sK157) ),
    inference(cnf_transformation,[],[f1881])).

cnf(c_1140,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f3052])).

cnf(c_56036,plain,
    ( r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK157,X0))
    | ~ r1_tarski(sK155,X0)
    | ~ v1_relat_1(sK157) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_83427,plain,
    ( r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK157,sK156))
    | ~ r1_tarski(sK155,sK156)
    | ~ v1_relat_1(sK157) ),
    inference(instantiation,[status(thm)],[c_56036])).

cnf(c_1141,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3053])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2903])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2864])).

cnf(c_9760,plain,
    ( r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_991,c_951])).

cnf(c_9761,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_9760])).

cnf(c_83204,plain,
    ( r1_tarski(k9_relat_1(sK157,sK156),k9_relat_1(sK158,sK156))
    | ~ r1_tarski(sK157,sK158)
    | ~ v1_relat_1(sK158) ),
    inference(instantiation,[status(thm)],[c_9761])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f2017])).

cnf(c_43250,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK158,sK156))
    | ~ r1_tarski(k9_relat_1(sK157,sK155),X0)
    | r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK158,sK156)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_56035,plain,
    ( ~ r1_tarski(k9_relat_1(sK157,X0),k9_relat_1(sK158,sK156))
    | r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK158,sK156))
    | ~ r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK157,X0)) ),
    inference(instantiation,[status(thm)],[c_43250])).

cnf(c_83203,plain,
    ( ~ r1_tarski(k9_relat_1(sK157,sK156),k9_relat_1(sK158,sK156))
    | r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK158,sK156))
    | ~ r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK157,sK156)) ),
    inference(instantiation,[status(thm)],[c_56035])).

cnf(c_1142,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK157,sK155),k9_relat_1(sK158,sK156)) ),
    inference(cnf_transformation,[],[f3058])).

cnf(c_1143,negated_conjecture,
    ( r1_tarski(sK155,sK156) ),
    inference(cnf_transformation,[],[f3057])).

cnf(c_1144,negated_conjecture,
    ( r1_tarski(sK157,sK158) ),
    inference(cnf_transformation,[],[f3056])).

cnf(c_1145,negated_conjecture,
    ( v1_relat_1(sK158) ),
    inference(cnf_transformation,[],[f3055])).

cnf(c_1146,negated_conjecture,
    ( v1_relat_1(sK157) ),
    inference(cnf_transformation,[],[f3054])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83427,c_83204,c_83203,c_1142,c_1143,c_1144,c_1145,c_1146])).

%------------------------------------------------------------------------------
