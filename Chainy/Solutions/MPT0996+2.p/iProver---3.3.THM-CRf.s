%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0996+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 39.45s
% Output     : CNFRefutation 39.45s
% Verified   : 
% Statistics : Number of formulae       :   21 (  27 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  83 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1221,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2783,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1221])).

fof(f6502,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2783])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3516,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f5360,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3516])).

fof(f1521,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1522,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(negated_conjecture,[],[f1521])).

fof(f3105,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1522])).

fof(f3106,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f3105])).

fof(f4387,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(sK538,sK539,sK541,sK540),sK539)
      & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
      & v1_funct_2(sK541,sK538,sK539)
      & v1_funct_1(sK541) ) ),
    introduced(choice_axiom,[])).

fof(f4388,plain,
    ( ~ r1_tarski(k7_relset_1(sK538,sK539,sK541,sK540),sK539)
    & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
    & v1_funct_2(sK541,sK538,sK539)
    & v1_funct_1(sK541) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK538,sK539,sK540,sK541])],[f3106,f4387])).

fof(f7261,plain,(
    ~ r1_tarski(k7_relset_1(sK538,sK539,sK541,sK540),sK539) ),
    inference(cnf_transformation,[],[f4388])).

fof(f7260,plain,(
    m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(cnf_transformation,[],[f4388])).

cnf(c_2096,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f6502])).

cnf(c_143515,plain,
    ( m1_subset_1(k7_relset_1(sK538,sK539,sK541,sK540),k1_zfmisc_1(sK539))
    | ~ m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(instantiation,[status(thm)],[c_2096])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5360])).

cnf(c_141770,plain,
    ( ~ m1_subset_1(k7_relset_1(sK538,sK539,sK541,sK540),k1_zfmisc_1(sK539))
    | r1_tarski(k7_relset_1(sK538,sK539,sK541,sK540),sK539) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_2843,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK538,sK539,sK541,sK540),sK539) ),
    inference(cnf_transformation,[],[f7261])).

cnf(c_2844,negated_conjecture,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(cnf_transformation,[],[f7260])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143515,c_141770,c_2843,c_2844])).

%------------------------------------------------------------------------------
