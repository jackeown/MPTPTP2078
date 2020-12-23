%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0342+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  166 ( 298 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f703,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f1588,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f703])).

fof(f451,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f702,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f451])).

fof(f910,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f702])).

fof(f1580,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f910])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f568,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f1116,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f568])).

fof(f462,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f463,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                   => r2_hidden(X3,X2) ) )
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f462])).

fof(f705,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f463])).

fof(f706,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f705])).

fof(f918,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(X1,sK68)
        & ! [X3] :
            ( r2_hidden(X3,sK68)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK68,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f917,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & ! [X3] :
                ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK67,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,sK67)
              | ~ m1_subset_1(X3,sK66) )
          & m1_subset_1(X2,k1_zfmisc_1(sK66)) )
      & m1_subset_1(sK67,k1_zfmisc_1(sK66)) ) ),
    introduced(choice_axiom,[])).

fof(f919,plain,
    ( ~ r1_tarski(sK67,sK68)
    & ! [X3] :
        ( r2_hidden(X3,sK68)
        | ~ r2_hidden(X3,sK67)
        | ~ m1_subset_1(X3,sK66) )
    & m1_subset_1(sK68,k1_zfmisc_1(sK66))
    & m1_subset_1(sK67,k1_zfmisc_1(sK66)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK66,sK67,sK68])],[f706,f918,f917])).

fof(f1596,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK68)
      | ~ r2_hidden(X3,sK67)
      | ~ m1_subset_1(X3,sK66) ) ),
    inference(cnf_transformation,[],[f919])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f479,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f717,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f479])).

fof(f718,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f717])).

fof(f719,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f720,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f718,f719])).

fof(f929,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f720])).

fof(f930,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f720])).

fof(f1597,plain,(
    ~ r1_tarski(sK67,sK68) ),
    inference(cnf_transformation,[],[f919])).

fof(f1594,plain,(
    m1_subset_1(sK67,k1_zfmisc_1(sK66)) ),
    inference(cnf_transformation,[],[f919])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f1588])).

cnf(c_23809,plain,
    ( ~ m1_subset_1(sK67,k1_zfmisc_1(X0))
    | r2_hidden(sK5(sK67,sK68),X0)
    | ~ r2_hidden(sK5(sK67,sK68),sK67) ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_35349,plain,
    ( ~ m1_subset_1(sK67,k1_zfmisc_1(sK66))
    | r2_hidden(sK5(sK67,sK68),sK66)
    | ~ r2_hidden(sK5(sK67,sK68),sK67) ),
    inference(instantiation,[status(thm)],[c_23809])).

cnf(c_649,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1580])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1116])).

cnf(c_4172,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_195])).

cnf(c_4173,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_4172])).

cnf(c_32397,plain,
    ( m1_subset_1(sK5(sK67,sK68),sK66)
    | ~ r2_hidden(sK5(sK67,sK68),sK66) ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_662,negated_conjecture,
    ( ~ m1_subset_1(X0,sK66)
    | r2_hidden(X0,sK68)
    | ~ r2_hidden(X0,sK67) ),
    inference(cnf_transformation,[],[f1596])).

cnf(c_23870,plain,
    ( ~ m1_subset_1(sK5(sK67,sK68),sK66)
    | r2_hidden(sK5(sK67,sK68),sK68)
    | ~ r2_hidden(sK5(sK67,sK68),sK67) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f929])).

cnf(c_19728,plain,
    ( r1_tarski(sK67,sK68)
    | r2_hidden(sK5(sK67,sK68),sK67) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f930])).

cnf(c_19720,plain,
    ( r1_tarski(sK67,sK68)
    | ~ r2_hidden(sK5(sK67,sK68),sK68) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_661,negated_conjecture,
    ( ~ r1_tarski(sK67,sK68) ),
    inference(cnf_transformation,[],[f1597])).

cnf(c_664,negated_conjecture,
    ( m1_subset_1(sK67,k1_zfmisc_1(sK66)) ),
    inference(cnf_transformation,[],[f1594])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35349,c_32397,c_23870,c_19728,c_19720,c_661,c_664])).

%------------------------------------------------------------------------------
