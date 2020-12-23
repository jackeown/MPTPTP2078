%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0430+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 15.70s
% Output     : CNFRefutation 15.70s
% Verified   : 
% Statistics : Number of formulae       :   39 (  70 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 312 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f655,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1091,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f655])).

fof(f1092,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1091])).

fof(f1093,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1094,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1092,f1093])).

fof(f1452,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1094])).

fof(f551,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f995,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f551])).

fof(f1372,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f995])).

fof(f2312,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1372])).

fof(f631,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ( r1_tarski(X2,X1)
              & v3_setfam_1(X1,X0) )
           => v3_setfam_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f632,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ( r1_tarski(X2,X1)
                & v3_setfam_1(X1,X0) )
             => v3_setfam_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f631])).

fof(f1060,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f632])).

fof(f1061,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f1060])).

fof(f1440,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ v3_setfam_1(sK125,X0)
        & r1_tarski(sK125,X1)
        & v3_setfam_1(X1,X0)
        & m1_subset_1(sK125,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1439,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(X2,X0)
            & r1_tarski(X2,X1)
            & v3_setfam_1(X1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(X2,sK123)
          & r1_tarski(X2,sK124)
          & v3_setfam_1(sK124,sK123)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK123))) )
      & m1_subset_1(sK124,k1_zfmisc_1(k1_zfmisc_1(sK123))) ) ),
    introduced(choice_axiom,[])).

fof(f1441,plain,
    ( ~ v3_setfam_1(sK125,sK123)
    & r1_tarski(sK125,sK124)
    & v3_setfam_1(sK124,sK123)
    & m1_subset_1(sK125,k1_zfmisc_1(k1_zfmisc_1(sK123)))
    & m1_subset_1(sK124,k1_zfmisc_1(k1_zfmisc_1(sK123))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK123,sK124,sK125])],[f1061,f1440,f1439])).

fof(f2441,plain,(
    v3_setfam_1(sK124,sK123) ),
    inference(cnf_transformation,[],[f1441])).

fof(f2313,plain,(
    ! [X0,X1] :
      ( v3_setfam_1(X1,X0)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1372])).

fof(f2443,plain,(
    ~ v3_setfam_1(sK125,sK123) ),
    inference(cnf_transformation,[],[f1441])).

fof(f2442,plain,(
    r1_tarski(sK125,sK124) ),
    inference(cnf_transformation,[],[f1441])).

fof(f2440,plain,(
    m1_subset_1(sK125,k1_zfmisc_1(k1_zfmisc_1(sK123))) ),
    inference(cnf_transformation,[],[f1441])).

fof(f2439,plain,(
    m1_subset_1(sK124,k1_zfmisc_1(k1_zfmisc_1(sK123))) ),
    inference(cnf_transformation,[],[f1441])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f1452])).

cnf(c_43559,plain,
    ( ~ r1_tarski(X0,sK124)
    | ~ r2_hidden(sK123,X0)
    | r2_hidden(sK123,sK124) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_53339,plain,
    ( ~ r1_tarski(sK125,sK124)
    | r2_hidden(sK123,sK124)
    | ~ r2_hidden(sK123,sK125) ),
    inference(instantiation,[status(thm)],[c_43559])).

cnf(c_855,plain,
    ( ~ v3_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f2312])).

cnf(c_983,negated_conjecture,
    ( v3_setfam_1(sK124,sK123) ),
    inference(cnf_transformation,[],[f2441])).

cnf(c_9730,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0)
    | sK124 != X0
    | sK123 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_855,c_983])).

cnf(c_9731,plain,
    ( ~ m1_subset_1(sK124,k1_zfmisc_1(k1_zfmisc_1(sK123)))
    | ~ r2_hidden(sK123,sK124) ),
    inference(unflattening,[status(thm)],[c_9730])).

cnf(c_854,plain,
    ( v3_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f2313])).

cnf(c_981,negated_conjecture,
    ( ~ v3_setfam_1(sK125,sK123) ),
    inference(cnf_transformation,[],[f2443])).

cnf(c_9719,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X1,X0)
    | sK123 != X1
    | sK125 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_854,c_981])).

cnf(c_9720,plain,
    ( ~ m1_subset_1(sK125,k1_zfmisc_1(k1_zfmisc_1(sK123)))
    | r2_hidden(sK123,sK125) ),
    inference(unflattening,[status(thm)],[c_9719])).

cnf(c_982,negated_conjecture,
    ( r1_tarski(sK125,sK124) ),
    inference(cnf_transformation,[],[f2442])).

cnf(c_984,negated_conjecture,
    ( m1_subset_1(sK125,k1_zfmisc_1(k1_zfmisc_1(sK123))) ),
    inference(cnf_transformation,[],[f2440])).

cnf(c_985,negated_conjecture,
    ( m1_subset_1(sK124,k1_zfmisc_1(k1_zfmisc_1(sK123))) ),
    inference(cnf_transformation,[],[f2439])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53339,c_9731,c_9720,c_982,c_984,c_985])).

%------------------------------------------------------------------------------
