%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0999+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 42.40s
% Output     : CNFRefutation 42.40s
% Verified   : 
% Statistics : Number of formulae       :   21 (  27 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  69 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1222,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2787,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1222])).

fof(f6514,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2787])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3525,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f5371,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3525])).

fof(f1524,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1525,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(negated_conjecture,[],[f1524])).

fof(f3114,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1525])).

fof(f3115,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f3114])).

fof(f4398,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k8_relset_1(sK538,sK539,sK541,sK540),sK538)
      & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
      & v1_funct_1(sK541) ) ),
    introduced(choice_axiom,[])).

fof(f4399,plain,
    ( ~ r1_tarski(k8_relset_1(sK538,sK539,sK541,sK540),sK538)
    & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
    & v1_funct_1(sK541) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK538,sK539,sK540,sK541])],[f3115,f4398])).

fof(f7277,plain,(
    ~ r1_tarski(k8_relset_1(sK538,sK539,sK541,sK540),sK538) ),
    inference(cnf_transformation,[],[f4399])).

fof(f7276,plain,(
    m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(cnf_transformation,[],[f4399])).

cnf(c_2097,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f6514])).

cnf(c_143677,plain,
    ( m1_subset_1(k8_relset_1(sK538,sK539,sK541,sK540),k1_zfmisc_1(sK538))
    | ~ m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5371])).

cnf(c_141932,plain,
    ( ~ m1_subset_1(k8_relset_1(sK538,sK539,sK541,sK540),k1_zfmisc_1(sK538))
    | r1_tarski(k8_relset_1(sK538,sK539,sK541,sK540),sK538) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_2849,negated_conjecture,
    ( ~ r1_tarski(k8_relset_1(sK538,sK539,sK541,sK540),sK538) ),
    inference(cnf_transformation,[],[f7277])).

cnf(c_2850,negated_conjecture,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(cnf_transformation,[],[f7276])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143677,c_141932,c_2849,c_2850])).

%------------------------------------------------------------------------------
