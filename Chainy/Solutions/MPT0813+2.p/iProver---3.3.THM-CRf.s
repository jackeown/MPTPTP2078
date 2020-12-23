%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0813+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:53 EST 2020

% Result     : Theorem 31.58s
% Output     : CNFRefutation 31.58s
% Verified   : 
% Statistics : Number of formulae       :   28 (  42 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 115 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2829,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f4280,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2829])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1280,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f1281,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1280])).

fof(f3432,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1281])).

fof(f4281,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2829])).

fof(f1212,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1213,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( r1_tarski(X0,X3)
         => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f1212])).

fof(f2449,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f1213])).

fof(f2450,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f2449])).

fof(f3311,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ~ m1_subset_1(sK320,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322)))
      & r1_tarski(sK320,sK323)
      & m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322))) ) ),
    introduced(choice_axiom,[])).

fof(f3312,plain,
    ( ~ m1_subset_1(sK320,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322)))
    & r1_tarski(sK320,sK323)
    & m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK320,sK321,sK322,sK323])],[f2450,f3311])).

fof(f5410,plain,(
    ~ m1_subset_1(sK320,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322))) ),
    inference(cnf_transformation,[],[f3312])).

fof(f5409,plain,(
    r1_tarski(sK320,sK323) ),
    inference(cnf_transformation,[],[f3312])).

fof(f5408,plain,(
    m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322))) ),
    inference(cnf_transformation,[],[f3312])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4280])).

cnf(c_116428,plain,
    ( ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322)))
    | r1_tarski(sK323,k2_zfmisc_1(sK321,sK322)) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f3432])).

cnf(c_99192,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK321,sK322))
    | ~ r1_tarski(sK320,X0)
    | r1_tarski(sK320,k2_zfmisc_1(sK321,sK322)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_112147,plain,
    ( ~ r1_tarski(sK323,k2_zfmisc_1(sK321,sK322))
    | r1_tarski(sK320,k2_zfmisc_1(sK321,sK322))
    | ~ r1_tarski(sK320,sK323) ),
    inference(instantiation,[status(thm)],[c_99192])).

cnf(c_953,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4281])).

cnf(c_99060,plain,
    ( m1_subset_1(sK320,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322)))
    | ~ r1_tarski(sK320,k2_zfmisc_1(sK321,sK322)) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_2080,negated_conjecture,
    ( ~ m1_subset_1(sK320,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322))) ),
    inference(cnf_transformation,[],[f5410])).

cnf(c_2081,negated_conjecture,
    ( r1_tarski(sK320,sK323) ),
    inference(cnf_transformation,[],[f5409])).

cnf(c_2082,negated_conjecture,
    ( m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322))) ),
    inference(cnf_transformation,[],[f5408])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_116428,c_112147,c_99060,c_2080,c_2081,c_2082])).

%------------------------------------------------------------------------------
