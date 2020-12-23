%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0829+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 43.38s
% Output     : CNFRefutation 43.38s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 181 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1215,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2482,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1215])).

fof(f5491,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2482])).

fof(f1236,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2506,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1236])).

fof(f2507,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2506])).

fof(f5519,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2507])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2896,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f4360,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2896])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2601,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2602,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2601])).

fof(f3461,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2602])).

fof(f5518,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2507])).

fof(f1238,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1239,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1238])).

fof(f2510,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1239])).

fof(f2511,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2510])).

fof(f3389,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK324,sK325,sK326) != sK325
        | ~ r1_tarski(sK325,k1_relset_1(sK324,sK325,sK326)) )
      & r1_tarski(k6_relat_1(sK325),sK326)
      & m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ) ),
    introduced(choice_axiom,[])).

fof(f3390,plain,
    ( ( k2_relset_1(sK324,sK325,sK326) != sK325
      | ~ r1_tarski(sK325,k1_relset_1(sK324,sK325,sK326)) )
    & r1_tarski(k6_relat_1(sK325),sK326)
    & m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK324,sK325,sK326])],[f2511,f3389])).

fof(f5524,plain,
    ( k2_relset_1(sK324,sK325,sK326) != sK325
    | ~ r1_tarski(sK325,k1_relset_1(sK324,sK325,sK326)) ),
    inference(cnf_transformation,[],[f3390])).

fof(f5523,plain,(
    r1_tarski(k6_relat_1(sK325),sK326) ),
    inference(cnf_transformation,[],[f3390])).

fof(f5522,plain,(
    m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    inference(cnf_transformation,[],[f3390])).

cnf(c_2083,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f5491])).

cnf(c_149390,plain,
    ( m1_subset_1(k2_relset_1(sK324,sK325,sK326),k1_zfmisc_1(sK325))
    | ~ m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_2110,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k2_relset_1(X1,X2,X0))
    | ~ r1_tarski(k6_relat_1(X3),X0) ),
    inference(cnf_transformation,[],[f5519])).

cnf(c_106625,plain,
    ( ~ m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325)))
    | ~ r1_tarski(k6_relat_1(sK325),sK326)
    | r1_tarski(sK325,k2_relset_1(sK324,sK325,sK326)) ),
    inference(instantiation,[status(thm)],[c_2110])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4360])).

cnf(c_103388,plain,
    ( ~ m1_subset_1(k2_relset_1(sK324,sK325,sK326),k1_zfmisc_1(sK325))
    | r1_tarski(k2_relset_1(sK324,sK325,sK326),sK325) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f3461])).

cnf(c_100795,plain,
    ( ~ r1_tarski(k2_relset_1(sK324,sK325,sK326),sK325)
    | ~ r1_tarski(sK325,k2_relset_1(sK324,sK325,sK326))
    | k2_relset_1(sK324,sK325,sK326) = sK325 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_2111,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k1_relset_1(X1,X2,X0))
    | ~ r1_tarski(k6_relat_1(X3),X0) ),
    inference(cnf_transformation,[],[f5518])).

cnf(c_100667,plain,
    ( ~ m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325)))
    | ~ r1_tarski(k6_relat_1(sK325),sK326)
    | r1_tarski(sK325,k1_relset_1(sK324,sK325,sK326)) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_2114,negated_conjecture,
    ( ~ r1_tarski(sK325,k1_relset_1(sK324,sK325,sK326))
    | k2_relset_1(sK324,sK325,sK326) != sK325 ),
    inference(cnf_transformation,[],[f5524])).

cnf(c_2115,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK325),sK326) ),
    inference(cnf_transformation,[],[f5523])).

cnf(c_2116,negated_conjecture,
    ( m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    inference(cnf_transformation,[],[f5522])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_149390,c_106625,c_103388,c_100795,c_100667,c_2114,c_2115,c_2116])).

%------------------------------------------------------------------------------
