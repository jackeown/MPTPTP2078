%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0828+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 43.04s
% Output     : CNFRefutation 43.04s
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
fof(f1214,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2480,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1214])).

fof(f5487,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2480])).

fof(f1236,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2505,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1236])).

fof(f2506,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2505])).

fof(f5515,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2506])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2893,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f4357,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2893])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2598,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2599,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2598])).

fof(f3458,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2599])).

fof(f5516,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2506])).

fof(f1237,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1238,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
            & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1237])).

fof(f2507,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f1238])).

fof(f2508,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f2507])).

fof(f3386,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
          | k1_relset_1(X1,X0,X2) != X1 )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( ~ r1_tarski(sK325,k2_relset_1(sK325,sK324,sK326))
        | k1_relset_1(sK325,sK324,sK326) != sK325 )
      & r1_tarski(k6_relat_1(sK325),sK326)
      & m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK325,sK324))) ) ),
    introduced(choice_axiom,[])).

fof(f3387,plain,
    ( ( ~ r1_tarski(sK325,k2_relset_1(sK325,sK324,sK326))
      | k1_relset_1(sK325,sK324,sK326) != sK325 )
    & r1_tarski(k6_relat_1(sK325),sK326)
    & m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK325,sK324))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK324,sK325,sK326])],[f2508,f3386])).

fof(f5519,plain,
    ( ~ r1_tarski(sK325,k2_relset_1(sK325,sK324,sK326))
    | k1_relset_1(sK325,sK324,sK326) != sK325 ),
    inference(cnf_transformation,[],[f3387])).

fof(f5518,plain,(
    r1_tarski(k6_relat_1(sK325),sK326) ),
    inference(cnf_transformation,[],[f3387])).

fof(f5517,plain,(
    m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK325,sK324))) ),
    inference(cnf_transformation,[],[f3387])).

cnf(c_2082,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f5487])).

cnf(c_149324,plain,
    ( m1_subset_1(k1_relset_1(sK325,sK324,sK326),k1_zfmisc_1(sK325))
    | ~ m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK325,sK324))) ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_2111,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k1_relset_1(X1,X2,X0))
    | ~ r1_tarski(k6_relat_1(X3),X0) ),
    inference(cnf_transformation,[],[f5515])).

cnf(c_106555,plain,
    ( ~ m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK325,sK324)))
    | ~ r1_tarski(k6_relat_1(sK325),sK326)
    | r1_tarski(sK325,k1_relset_1(sK325,sK324,sK326)) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4357])).

cnf(c_103318,plain,
    ( ~ m1_subset_1(k1_relset_1(sK325,sK324,sK326),k1_zfmisc_1(sK325))
    | r1_tarski(k1_relset_1(sK325,sK324,sK326),sK325) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f3458])).

cnf(c_100725,plain,
    ( ~ r1_tarski(k1_relset_1(sK325,sK324,sK326),sK325)
    | ~ r1_tarski(sK325,k1_relset_1(sK325,sK324,sK326))
    | k1_relset_1(sK325,sK324,sK326) = sK325 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_2110,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k2_relset_1(X1,X2,X0))
    | ~ r1_tarski(k6_relat_1(X3),X0) ),
    inference(cnf_transformation,[],[f5516])).

cnf(c_100597,plain,
    ( ~ m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK325,sK324)))
    | ~ r1_tarski(k6_relat_1(sK325),sK326)
    | r1_tarski(sK325,k2_relset_1(sK325,sK324,sK326)) ),
    inference(instantiation,[status(thm)],[c_2110])).

cnf(c_2112,negated_conjecture,
    ( ~ r1_tarski(sK325,k2_relset_1(sK325,sK324,sK326))
    | k1_relset_1(sK325,sK324,sK326) != sK325 ),
    inference(cnf_transformation,[],[f5519])).

cnf(c_2113,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK325),sK326) ),
    inference(cnf_transformation,[],[f5518])).

cnf(c_2114,negated_conjecture,
    ( m1_subset_1(sK326,k1_zfmisc_1(k2_zfmisc_1(sK325,sK324))) ),
    inference(cnf_transformation,[],[f5517])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_149324,c_106555,c_103318,c_100725,c_100597,c_2112,c_2113,c_2114])).

%------------------------------------------------------------------------------
