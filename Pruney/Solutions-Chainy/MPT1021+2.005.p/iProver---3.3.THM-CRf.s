%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:18 EST 2020

% Result     : Theorem 35.08s
% Output     : CNFRefutation 35.08s
% Verified   : 
% Statistics : Number of formulae       :  316 (3069 expanded)
%              Number of clauses        :  207 ( 980 expanded)
%              Number of leaves         :   36 ( 601 expanded)
%              Depth                    :   29
%              Number of atoms          : 1080 (14481 expanded)
%              Number of equality atoms :  521 (1682 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK3(X0,X1),X0,X1)
        & v1_funct_1(sK3(X0,X1))
        & v5_relat_1(sK3(X0,X1),X1)
        & v4_relat_1(sK3(X0,X1),X0)
        & v1_relat_1(sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK3(X0,X1),X0,X1)
      & v1_funct_1(sK3(X0,X1))
      & v5_relat_1(sK3(X0,X1),X1)
      & v4_relat_1(sK3(X0,X1),X0)
      & v1_relat_1(sK3(X0,X1))
      & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f92])).

fof(f141,plain,(
    ! [X0,X1] : m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f93])).

fof(f23,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f125,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f149,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f160,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f125,f149])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f57])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f36,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f78,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f79,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f78])).

fof(f94,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4))
        | ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
      & v3_funct_2(sK5,sK4,sK4)
      & v1_funct_2(sK5,sK4,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,
    ( ( ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4))
      | ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    & v3_funct_2(sK5,sK4,sK4)
    & v1_funct_2(sK5,sK4,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f79,f94])).

fof(f158,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) ),
    inference(cnf_transformation,[],[f95])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f72])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f155,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f95])).

fof(f156,plain,(
    v1_funct_2(sK5,sK4,sK4) ),
    inference(cnf_transformation,[],[f95])).

fof(f157,plain,(
    v3_funct_2(sK5,sK4,sK4) ),
    inference(cnf_transformation,[],[f95])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f68])).

fof(f140,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f70])).

fof(f147,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f137,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f66])).

fof(f136,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f135,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f60])).

fof(f89,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK2(X0,X1,X2)) != k11_relat_1(X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK2(X0,X1,X2)) != k11_relat_1(X2,sK2(X0,X1,X2))
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f89])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f81,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f80])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f81,f82])).

fof(f96,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f159,plain,
    ( ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4))
    | ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) ),
    inference(cnf_transformation,[],[f95])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f86])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f87])).

fof(f161,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f105])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f62])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f74])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f64])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f35,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f76])).

fof(f153,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f154,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f113,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f117,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f139,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_50,plain,
    ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2486,plain,
    ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_29,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_2501,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2502,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10573,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2501,c_2502])).

cnf(c_104651,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_10573])).

cnf(c_104675,plain,
    ( r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_104651])).

cnf(c_1669,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_50488,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,k6_partfun1(X7))
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | k6_partfun1(X7) != X3 ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_53660,plain,
    ( ~ r2_relset_1(X0,X1,X2,k6_partfun1(X3))
    | r2_relset_1(X4,X5,X6,k6_partfun1(X7))
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | k6_partfun1(X7) != k6_partfun1(X3) ),
    inference(instantiation,[status(thm)],[c_50488])).

cnf(c_62736,plain,
    ( r2_relset_1(X0,X1,X2,k6_partfun1(X3))
    | ~ r2_relset_1(X4,X4,k6_partfun1(X4),k6_partfun1(X5))
    | X0 != X4
    | X1 != X4
    | X2 != k6_partfun1(X4)
    | k6_partfun1(X3) != k6_partfun1(X5) ),
    inference(instantiation,[status(thm)],[c_53660])).

cnf(c_84764,plain,
    ( r2_relset_1(X0,X1,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(X2))
    | ~ r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(X3))
    | X0 != sK4
    | X1 != sK4
    | k5_relat_1(sK5,k2_funct_1(sK5)) != k6_partfun1(sK4)
    | k6_partfun1(X2) != k6_partfun1(X3) ),
    inference(instantiation,[status(thm)],[c_62736])).

cnf(c_84765,plain,
    ( X0 != sK4
    | X1 != sK4
    | k5_relat_1(sK5,k2_funct_1(sK5)) != k6_partfun1(sK4)
    | k6_partfun1(X2) != k6_partfun1(X3)
    | r2_relset_1(X0,X1,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(X2)) = iProver_top
    | r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84764])).

cnf(c_84767,plain,
    ( k5_relat_1(sK5,k2_funct_1(sK5)) != k6_partfun1(sK4)
    | k6_partfun1(sK4) != k6_partfun1(sK4)
    | sK4 != sK4
    | r2_relset_1(sK4,sK4,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) = iProver_top
    | r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84765])).

cnf(c_59,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_2478,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_52,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_2484,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_6616,plain,
    ( k2_funct_2(sK4,sK5) = k2_funct_1(sK5)
    | v1_funct_2(sK5,sK4,sK4) != iProver_top
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2484])).

cnf(c_62,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_63,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( v1_funct_2(sK5,sK4,sK4) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_64,plain,
    ( v1_funct_2(sK5,sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_60,negated_conjecture,
    ( v3_funct_2(sK5,sK4,sK4) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_65,plain,
    ( v3_funct_2(sK5,sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_6865,plain,
    ( k2_funct_2(sK4,sK5) = k2_funct_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6616,c_63,c_64,c_65])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2493,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_11083,plain,
    ( v1_funct_2(sK5,sK4,sK4) != iProver_top
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6865,c_2493])).

cnf(c_66,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_11723,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11083,c_63,c_64,c_65,c_66])).

cnf(c_51,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_2485,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_11744,plain,
    ( k1_partfun1(X0,X1,sK4,sK4,X2,k2_funct_1(sK5)) = k5_relat_1(X2,k2_funct_1(sK5))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11723,c_2485])).

cnf(c_44,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_2490,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7990,plain,
    ( v1_funct_2(sK5,sK4,sK4) != iProver_top
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | v1_funct_1(k2_funct_2(sK4,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2490])).

cnf(c_7993,plain,
    ( v1_funct_2(sK5,sK4,sK4) != iProver_top
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7990,c_6865])).

cnf(c_20710,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK4,sK4,X2,k2_funct_1(sK5)) = k5_relat_1(X2,k2_funct_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11744,c_63,c_64,c_65,c_7993])).

cnf(c_20711,plain,
    ( k1_partfun1(X0,X1,sK4,sK4,X2,k2_funct_1(sK5)) = k5_relat_1(X2,k2_funct_1(sK5))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_20710])).

cnf(c_20723,plain,
    ( k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_1(sK5)) = k5_relat_1(sK5,k2_funct_1(sK5))
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_20711])).

cnf(c_20759,plain,
    ( k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_1(sK5)) = k5_relat_1(sK5,k2_funct_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20723,c_63])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_20763,plain,
    ( m1_subset_1(k5_relat_1(sK5,k2_funct_1(sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20759,c_2495])).

cnf(c_20827,plain,
    ( m1_subset_1(k5_relat_1(sK5,k2_funct_1(sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20763,c_63,c_64,c_65,c_66,c_7993,c_11083])).

cnf(c_20852,plain,
    ( k1_partfun1(X0,X1,sK4,sK4,X2,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(X2,k5_relat_1(sK5,k2_funct_1(sK5)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k5_relat_1(sK5,k2_funct_1(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20827,c_2485])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_20764,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(k5_relat_1(sK5,k2_funct_1(sK5))) = iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20759,c_2494])).

cnf(c_31197,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK4,sK4,X2,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(X2,k5_relat_1(sK5,k2_funct_1(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20852,c_63,c_64,c_65,c_66,c_7993,c_11083,c_20764])).

cnf(c_31198,plain,
    ( k1_partfun1(X0,X1,sK4,sK4,X2,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(X2,k5_relat_1(sK5,k2_funct_1(sK5)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_31197])).

cnf(c_31210,plain,
    ( k1_partfun1(sK4,sK4,sK4,sK4,sK5,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5)))
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_31198])).

cnf(c_31400,plain,
    ( k1_partfun1(sK4,sK4,sK4,sK4,sK5,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31210,c_63])).

cnf(c_31402,plain,
    ( m1_subset_1(k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5))),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(k5_relat_1(sK5,k2_funct_1(sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(k5_relat_1(sK5,k2_funct_1(sK5))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_31400,c_2495])).

cnf(c_31864,plain,
    ( m1_subset_1(k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5))),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31402,c_63,c_64,c_65,c_66,c_7993,c_11083,c_20763,c_20764])).

cnf(c_33,plain,
    ( r2_relset_1(X0,X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | r2_hidden(sK2(X0,X1,X2),X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_2497,plain,
    ( r2_relset_1(X0,X0,X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_13786,plain,
    ( r2_relset_1(sK4,sK4,sK5,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | r2_hidden(sK2(sK4,sK5,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2497])).

cnf(c_31893,plain,
    ( r2_relset_1(sK4,sK4,sK5,k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5)))) = iProver_top
    | r2_hidden(sK2(sK4,sK5,k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5)))),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_31864,c_13786])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2520,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_31982,plain,
    ( r2_relset_1(sK4,sK4,sK5,k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5)))) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_31893,c_2520])).

cnf(c_58,negated_conjecture,
    ( ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4))
    | ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_67,plain,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) != iProver_top
    | r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_148,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_150,plain,
    ( m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f161])).

cnf(c_206,plain,
    ( k2_zfmisc_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_219,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1657,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1698,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_2581,plain,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4))
    | ~ m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2582,plain,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) = iProver_top
    | m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2581])).

cnf(c_2601,plain,
    ( m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ v1_funct_1(k2_funct_2(sK4,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_2602,plain,
    ( m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(k2_funct_2(sK4,sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2601])).

cnf(c_2649,plain,
    ( ~ v1_funct_2(sK5,sK4,sK4)
    | ~ v3_funct_2(sK5,sK4,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | v1_funct_1(k2_funct_2(sK4,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_2650,plain,
    ( v1_funct_2(sK5,sK4,sK4) != iProver_top
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(k2_funct_2(sK4,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2649])).

cnf(c_2773,plain,
    ( ~ v1_funct_2(sK5,sK4,sK4)
    | ~ v3_funct_2(sK5,sK4,sK4)
    | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_2774,plain,
    ( v1_funct_2(sK5,sK4,sK4) != iProver_top
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2773])).

cnf(c_2806,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_2907,plain,
    ( ~ r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2908,plain,
    ( r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)),sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2907])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3402,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3403,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3402])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4157,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4158,plain,
    ( X0 = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4157])).

cnf(c_4160,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4158])).

cnf(c_1659,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3286,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_4162,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_zfmisc_1(X0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3286])).

cnf(c_4163,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) != k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4162])).

cnf(c_4165,plain,
    ( k2_zfmisc_1(sK4,k1_xboole_0) != k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(sK4,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4163])).

cnf(c_1663,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2981,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_3702,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | X1 != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_2981])).

cnf(c_5388,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_3702])).

cnf(c_5389,plain,
    ( X0 != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5388])).

cnf(c_5391,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5389])).

cnf(c_2623,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(sK4,sK4))
    | k2_zfmisc_1(sK4,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_6110,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | v1_xboole_0(k2_zfmisc_1(sK4,sK4))
    | k2_zfmisc_1(sK4,sK4) != k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2623])).

cnf(c_6151,plain,
    ( k2_zfmisc_1(sK4,sK4) != k2_zfmisc_1(X0,k1_xboole_0)
    | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6110])).

cnf(c_6153,plain,
    ( k2_zfmisc_1(sK4,sK4) != k2_zfmisc_1(sK4,k1_xboole_0)
    | v1_xboole_0(k2_zfmisc_1(sK4,sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6151])).

cnf(c_1661,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_10048,plain,
    ( k2_zfmisc_1(sK4,sK4) = k2_zfmisc_1(X0,k1_xboole_0)
    | sK4 != X0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_10049,plain,
    ( k2_zfmisc_1(sK4,sK4) = k2_zfmisc_1(sK4,k1_xboole_0)
    | sK4 != sK4
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10048])).

cnf(c_3731,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,X3)))
    | m1_subset_1(k1_partfun1(sK4,X3,X1,sK4,X2,X0),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_7347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | m1_subset_1(k1_partfun1(sK4,X1,X2,sK4,X0,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X2,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_2(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3731])).

cnf(c_10687,plain,
    ( m1_subset_1(k1_partfun1(sK4,X0,X1,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
    | ~ v1_funct_1(k2_funct_2(sK4,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_7347])).

cnf(c_10688,plain,
    ( m1_subset_1(k1_partfun1(sK4,X0,X1,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X1,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK4,sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10687])).

cnf(c_10690,plain,
    ( m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(k2_funct_2(sK4,sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10688])).

cnf(c_17258,plain,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4))
    | ~ m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_17259,plain,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) = iProver_top
    | m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17258])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2701,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(k2_zfmisc_1(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_34564,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)),sK4)
    | ~ v1_xboole_0(k2_zfmisc_1(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_2701])).

cnf(c_34565,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)),sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34564])).

cnf(c_34607,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31982,c_63,c_64,c_65,c_66,c_67,c_150,c_206,c_219,c_1698,c_2582,c_2602,c_2650,c_2774,c_2806,c_2908,c_3403,c_4160,c_4165,c_5391,c_6153,c_10049,c_10690,c_17259,c_34565])).

cnf(c_35,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_2496,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11279,plain,
    ( v3_funct_2(sK5,sK4,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2496])).

cnf(c_9596,plain,
    ( ~ v3_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | v2_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_9597,plain,
    ( v3_funct_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9596])).

cnf(c_9599,plain,
    ( v3_funct_2(sK5,sK4,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9597])).

cnf(c_11574,plain,
    ( v2_funct_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11279,c_63,c_65,c_66,c_9599])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2499,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6081,plain,
    ( k7_relset_1(sK4,sK4,sK5,sK4) = k2_relset_1(sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2478,c_2499])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2503,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5223,plain,
    ( k7_relset_1(sK4,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_2478,c_2503])).

cnf(c_6086,plain,
    ( k2_relset_1(sK4,sK4,sK5) = k9_relat_1(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_6081,c_5223])).

cnf(c_53,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f151])).

cnf(c_2483,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_6505,plain,
    ( k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
    | k9_relat_1(sK5,sK4) != sK4
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK4,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6086,c_2483])).

cnf(c_34,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_38,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_745,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_38])).

cnf(c_746,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_745])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_750,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_746,c_22])).

cnf(c_751,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_750])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_766,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_751,c_23])).

cnf(c_2472,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_3534,plain,
    ( k2_relat_1(sK5) = sK4
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2472])).

cnf(c_3748,plain,
    ( k2_relat_1(sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3534,c_63,c_65])).

cnf(c_56,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_2480,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_4305,plain,
    ( v1_funct_2(sK5,k1_relat_1(sK5),sK4) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3748,c_2480])).

cnf(c_2506,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4434,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2506])).

cnf(c_55,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_2481,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_5029,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3748,c_2481])).

cnf(c_5422,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5029,c_63,c_4434])).

cnf(c_6082,plain,
    ( k7_relset_1(k1_relat_1(sK5),sK4,sK5,k1_relat_1(sK5)) = k2_relset_1(k1_relat_1(sK5),sK4,sK5) ),
    inference(superposition,[status(thm)],[c_5422,c_2499])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2511,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4735,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4434,c_2511])).

cnf(c_4736,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_4735,c_3748])).

cnf(c_5429,plain,
    ( k7_relset_1(k1_relat_1(sK5),sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_5422,c_2503])).

cnf(c_6085,plain,
    ( k2_relset_1(k1_relat_1(sK5),sK4,sK5) = sK4 ),
    inference(demodulation,[status(thm)],[c_6082,c_4736,c_5429])).

cnf(c_6511,plain,
    ( k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6085,c_2483])).

cnf(c_6567,plain,
    ( sK4 = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
    | v2_funct_1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6505,c_63,c_4305,c_4434,c_5029,c_6511])).

cnf(c_6568,plain,
    ( k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
    | sK4 = k1_xboole_0
    | v2_funct_1(sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_6567])).

cnf(c_11581,plain,
    ( k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11574,c_6568])).

cnf(c_7262,plain,
    ( k1_partfun1(X0,X1,sK4,sK4,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2485])).

cnf(c_7742,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK4,sK4,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7262,c_63])).

cnf(c_7743,plain,
    ( k1_partfun1(X0,X1,sK4,sK4,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7742])).

cnf(c_11736,plain,
    ( k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_1(sK5),sK5) = k5_relat_1(k2_funct_1(sK5),sK5)
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11723,c_7743])).

cnf(c_11771,plain,
    ( k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_1(sK5),sK5) = k5_relat_1(k2_funct_1(sK5),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11736,c_63,c_64,c_65,c_7993])).

cnf(c_2479,plain,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) != iProver_top
    | r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_6867,plain,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_1(sK5),sK5),k6_partfun1(sK4)) != iProver_top
    | r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6865,c_2479])).

cnf(c_11773,plain,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) != iProver_top
    | r2_relset_1(sK4,sK4,k5_relat_1(k2_funct_1(sK5),sK5),k6_partfun1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11771,c_6867])).

cnf(c_20761,plain,
    ( r2_relset_1(sK4,sK4,k5_relat_1(k2_funct_1(sK5),sK5),k6_partfun1(sK4)) != iProver_top
    | r2_relset_1(sK4,sK4,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20759,c_11773])).

cnf(c_20779,plain,
    ( sK4 = k1_xboole_0
    | r2_relset_1(sK4,sK4,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) != iProver_top
    | r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11581,c_20761])).

cnf(c_11733,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = sK4
    | v3_funct_2(k2_funct_1(sK5),sK4,sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11723,c_2472])).

cnf(c_2475,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2508,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8249,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
    | v2_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2475,c_2508])).

cnf(c_8330,plain,
    ( v2_funct_1(sK5) != iProver_top
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8249,c_4434])).

cnf(c_8331,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
    | v2_funct_1(sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_8330])).

cnf(c_11579,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_11574,c_8331])).

cnf(c_11746,plain,
    ( k1_relat_1(sK5) = sK4
    | v3_funct_2(k2_funct_1(sK5),sK4,sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11733,c_11579])).

cnf(c_42,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_2492,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_10485,plain,
    ( v1_funct_2(sK5,sK4,sK4) != iProver_top
    | v3_funct_2(k2_funct_2(sK4,sK5),sK4,sK4) = iProver_top
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2492])).

cnf(c_10488,plain,
    ( v1_funct_2(sK5,sK4,sK4) != iProver_top
    | v3_funct_2(k2_funct_1(sK5),sK4,sK4) = iProver_top
    | v3_funct_2(sK5,sK4,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10485,c_6865])).

cnf(c_16985,plain,
    ( k1_relat_1(sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11746,c_63,c_64,c_65,c_7993,c_10488])).

cnf(c_17006,plain,
    ( k9_relat_1(sK5,sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_16985,c_4736])).

cnf(c_54,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f150])).

cnf(c_2482,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_6506,plain,
    ( k5_relat_1(sK5,k2_funct_1(sK5)) = k6_partfun1(sK4)
    | k9_relat_1(sK5,sK4) != sK4
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK4,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6086,c_2482])).

cnf(c_6572,plain,
    ( sK4 = k1_xboole_0
    | k9_relat_1(sK5,sK4) != sK4
    | k5_relat_1(sK5,k2_funct_1(sK5)) = k6_partfun1(sK4)
    | v2_funct_1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6506,c_63,c_64,c_66])).

cnf(c_6573,plain,
    ( k5_relat_1(sK5,k2_funct_1(sK5)) = k6_partfun1(sK4)
    | k9_relat_1(sK5,sK4) != sK4
    | sK4 = k1_xboole_0
    | v2_funct_1(sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_6572])).

cnf(c_3287,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3286])).

cnf(c_3289,plain,
    ( sK4 != k1_xboole_0
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3287])).

cnf(c_1670,plain,
    ( X0 != X1
    | k6_partfun1(X0) = k6_partfun1(X1) ),
    theory(equality)).

cnf(c_1689,plain,
    ( k6_partfun1(sK4) = k6_partfun1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_104675,c_84767,c_34607,c_20779,c_17006,c_9599,c_6573,c_3289,c_1698,c_1689,c_219,c_66,c_65,c_63])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:58:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.08/4.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.08/4.99  
% 35.08/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.08/4.99  
% 35.08/4.99  ------  iProver source info
% 35.08/4.99  
% 35.08/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.08/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.08/4.99  git: non_committed_changes: false
% 35.08/4.99  git: last_make_outside_of_git: false
% 35.08/4.99  
% 35.08/4.99  ------ 
% 35.08/4.99  
% 35.08/4.99  ------ Input Options
% 35.08/4.99  
% 35.08/4.99  --out_options                           all
% 35.08/4.99  --tptp_safe_out                         true
% 35.08/4.99  --problem_path                          ""
% 35.08/4.99  --include_path                          ""
% 35.08/4.99  --clausifier                            res/vclausify_rel
% 35.08/4.99  --clausifier_options                    ""
% 35.08/4.99  --stdin                                 false
% 35.08/4.99  --stats_out                             all
% 35.08/4.99  
% 35.08/4.99  ------ General Options
% 35.08/4.99  
% 35.08/4.99  --fof                                   false
% 35.08/4.99  --time_out_real                         305.
% 35.08/4.99  --time_out_virtual                      -1.
% 35.08/4.99  --symbol_type_check                     false
% 35.08/4.99  --clausify_out                          false
% 35.08/4.99  --sig_cnt_out                           false
% 35.08/4.99  --trig_cnt_out                          false
% 35.08/4.99  --trig_cnt_out_tolerance                1.
% 35.08/4.99  --trig_cnt_out_sk_spl                   false
% 35.08/4.99  --abstr_cl_out                          false
% 35.08/4.99  
% 35.08/4.99  ------ Global Options
% 35.08/4.99  
% 35.08/4.99  --schedule                              default
% 35.08/4.99  --add_important_lit                     false
% 35.08/4.99  --prop_solver_per_cl                    1000
% 35.08/4.99  --min_unsat_core                        false
% 35.08/4.99  --soft_assumptions                      false
% 35.08/4.99  --soft_lemma_size                       3
% 35.08/4.99  --prop_impl_unit_size                   0
% 35.08/4.99  --prop_impl_unit                        []
% 35.08/4.99  --share_sel_clauses                     true
% 35.08/4.99  --reset_solvers                         false
% 35.08/4.99  --bc_imp_inh                            [conj_cone]
% 35.08/4.99  --conj_cone_tolerance                   3.
% 35.08/4.99  --extra_neg_conj                        none
% 35.08/4.99  --large_theory_mode                     true
% 35.08/4.99  --prolific_symb_bound                   200
% 35.08/4.99  --lt_threshold                          2000
% 35.08/4.99  --clause_weak_htbl                      true
% 35.08/4.99  --gc_record_bc_elim                     false
% 35.08/4.99  
% 35.08/4.99  ------ Preprocessing Options
% 35.08/4.99  
% 35.08/4.99  --preprocessing_flag                    true
% 35.08/4.99  --time_out_prep_mult                    0.1
% 35.08/4.99  --splitting_mode                        input
% 35.08/4.99  --splitting_grd                         true
% 35.08/4.99  --splitting_cvd                         false
% 35.08/4.99  --splitting_cvd_svl                     false
% 35.08/4.99  --splitting_nvd                         32
% 35.08/4.99  --sub_typing                            true
% 35.08/4.99  --prep_gs_sim                           true
% 35.08/4.99  --prep_unflatten                        true
% 35.08/4.99  --prep_res_sim                          true
% 35.08/4.99  --prep_upred                            true
% 35.08/4.99  --prep_sem_filter                       exhaustive
% 35.08/4.99  --prep_sem_filter_out                   false
% 35.08/4.99  --pred_elim                             true
% 35.08/4.99  --res_sim_input                         true
% 35.08/4.99  --eq_ax_congr_red                       true
% 35.08/4.99  --pure_diseq_elim                       true
% 35.08/4.99  --brand_transform                       false
% 35.08/4.99  --non_eq_to_eq                          false
% 35.08/4.99  --prep_def_merge                        true
% 35.08/4.99  --prep_def_merge_prop_impl              false
% 35.08/4.99  --prep_def_merge_mbd                    true
% 35.08/4.99  --prep_def_merge_tr_red                 false
% 35.08/4.99  --prep_def_merge_tr_cl                  false
% 35.08/4.99  --smt_preprocessing                     true
% 35.08/4.99  --smt_ac_axioms                         fast
% 35.08/4.99  --preprocessed_out                      false
% 35.08/4.99  --preprocessed_stats                    false
% 35.08/4.99  
% 35.08/4.99  ------ Abstraction refinement Options
% 35.08/4.99  
% 35.08/4.99  --abstr_ref                             []
% 35.08/4.99  --abstr_ref_prep                        false
% 35.08/4.99  --abstr_ref_until_sat                   false
% 35.08/4.99  --abstr_ref_sig_restrict                funpre
% 35.08/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.08/4.99  --abstr_ref_under                       []
% 35.08/4.99  
% 35.08/4.99  ------ SAT Options
% 35.08/4.99  
% 35.08/4.99  --sat_mode                              false
% 35.08/4.99  --sat_fm_restart_options                ""
% 35.08/4.99  --sat_gr_def                            false
% 35.08/4.99  --sat_epr_types                         true
% 35.08/4.99  --sat_non_cyclic_types                  false
% 35.08/4.99  --sat_finite_models                     false
% 35.08/4.99  --sat_fm_lemmas                         false
% 35.08/4.99  --sat_fm_prep                           false
% 35.08/4.99  --sat_fm_uc_incr                        true
% 35.08/4.99  --sat_out_model                         small
% 35.08/4.99  --sat_out_clauses                       false
% 35.08/4.99  
% 35.08/4.99  ------ QBF Options
% 35.08/4.99  
% 35.08/4.99  --qbf_mode                              false
% 35.08/4.99  --qbf_elim_univ                         false
% 35.08/4.99  --qbf_dom_inst                          none
% 35.08/4.99  --qbf_dom_pre_inst                      false
% 35.08/4.99  --qbf_sk_in                             false
% 35.08/4.99  --qbf_pred_elim                         true
% 35.08/4.99  --qbf_split                             512
% 35.08/4.99  
% 35.08/4.99  ------ BMC1 Options
% 35.08/4.99  
% 35.08/4.99  --bmc1_incremental                      false
% 35.08/4.99  --bmc1_axioms                           reachable_all
% 35.08/4.99  --bmc1_min_bound                        0
% 35.08/4.99  --bmc1_max_bound                        -1
% 35.08/4.99  --bmc1_max_bound_default                -1
% 35.08/4.99  --bmc1_symbol_reachability              true
% 35.08/4.99  --bmc1_property_lemmas                  false
% 35.08/4.99  --bmc1_k_induction                      false
% 35.08/4.99  --bmc1_non_equiv_states                 false
% 35.08/4.99  --bmc1_deadlock                         false
% 35.08/4.99  --bmc1_ucm                              false
% 35.08/4.99  --bmc1_add_unsat_core                   none
% 35.08/4.99  --bmc1_unsat_core_children              false
% 35.08/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.08/4.99  --bmc1_out_stat                         full
% 35.08/4.99  --bmc1_ground_init                      false
% 35.08/4.99  --bmc1_pre_inst_next_state              false
% 35.08/4.99  --bmc1_pre_inst_state                   false
% 35.08/4.99  --bmc1_pre_inst_reach_state             false
% 35.08/4.99  --bmc1_out_unsat_core                   false
% 35.08/4.99  --bmc1_aig_witness_out                  false
% 35.08/4.99  --bmc1_verbose                          false
% 35.08/4.99  --bmc1_dump_clauses_tptp                false
% 35.08/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.08/4.99  --bmc1_dump_file                        -
% 35.08/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.08/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.08/4.99  --bmc1_ucm_extend_mode                  1
% 35.08/4.99  --bmc1_ucm_init_mode                    2
% 35.08/4.99  --bmc1_ucm_cone_mode                    none
% 35.08/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.08/4.99  --bmc1_ucm_relax_model                  4
% 35.08/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.08/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.08/4.99  --bmc1_ucm_layered_model                none
% 35.08/4.99  --bmc1_ucm_max_lemma_size               10
% 35.08/4.99  
% 35.08/4.99  ------ AIG Options
% 35.08/4.99  
% 35.08/4.99  --aig_mode                              false
% 35.08/4.99  
% 35.08/4.99  ------ Instantiation Options
% 35.08/4.99  
% 35.08/4.99  --instantiation_flag                    true
% 35.08/4.99  --inst_sos_flag                         true
% 35.08/4.99  --inst_sos_phase                        true
% 35.08/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.08/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.08/4.99  --inst_lit_sel_side                     num_symb
% 35.08/4.99  --inst_solver_per_active                1400
% 35.08/4.99  --inst_solver_calls_frac                1.
% 35.08/4.99  --inst_passive_queue_type               priority_queues
% 35.08/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.08/4.99  --inst_passive_queues_freq              [25;2]
% 35.08/4.99  --inst_dismatching                      true
% 35.08/4.99  --inst_eager_unprocessed_to_passive     true
% 35.08/4.99  --inst_prop_sim_given                   true
% 35.08/4.99  --inst_prop_sim_new                     false
% 35.08/4.99  --inst_subs_new                         false
% 35.08/4.99  --inst_eq_res_simp                      false
% 35.08/4.99  --inst_subs_given                       false
% 35.08/4.99  --inst_orphan_elimination               true
% 35.08/4.99  --inst_learning_loop_flag               true
% 35.08/4.99  --inst_learning_start                   3000
% 35.08/4.99  --inst_learning_factor                  2
% 35.08/4.99  --inst_start_prop_sim_after_learn       3
% 35.08/4.99  --inst_sel_renew                        solver
% 35.08/4.99  --inst_lit_activity_flag                true
% 35.08/4.99  --inst_restr_to_given                   false
% 35.08/4.99  --inst_activity_threshold               500
% 35.08/4.99  --inst_out_proof                        true
% 35.08/4.99  
% 35.08/4.99  ------ Resolution Options
% 35.08/4.99  
% 35.08/4.99  --resolution_flag                       true
% 35.08/4.99  --res_lit_sel                           adaptive
% 35.08/4.99  --res_lit_sel_side                      none
% 35.08/4.99  --res_ordering                          kbo
% 35.08/4.99  --res_to_prop_solver                    active
% 35.08/4.99  --res_prop_simpl_new                    false
% 35.08/4.99  --res_prop_simpl_given                  true
% 35.08/4.99  --res_passive_queue_type                priority_queues
% 35.08/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.08/4.99  --res_passive_queues_freq               [15;5]
% 35.08/4.99  --res_forward_subs                      full
% 35.08/4.99  --res_backward_subs                     full
% 35.08/4.99  --res_forward_subs_resolution           true
% 35.08/4.99  --res_backward_subs_resolution          true
% 35.08/4.99  --res_orphan_elimination                true
% 35.08/4.99  --res_time_limit                        2.
% 35.08/4.99  --res_out_proof                         true
% 35.08/4.99  
% 35.08/4.99  ------ Superposition Options
% 35.08/4.99  
% 35.08/4.99  --superposition_flag                    true
% 35.08/4.99  --sup_passive_queue_type                priority_queues
% 35.08/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.08/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.08/4.99  --demod_completeness_check              fast
% 35.08/4.99  --demod_use_ground                      true
% 35.08/4.99  --sup_to_prop_solver                    passive
% 35.08/4.99  --sup_prop_simpl_new                    true
% 35.08/4.99  --sup_prop_simpl_given                  true
% 35.08/4.99  --sup_fun_splitting                     true
% 35.08/4.99  --sup_smt_interval                      50000
% 35.08/4.99  
% 35.08/4.99  ------ Superposition Simplification Setup
% 35.08/4.99  
% 35.08/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.08/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.08/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.08/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.08/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.08/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.08/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.08/4.99  --sup_immed_triv                        [TrivRules]
% 35.08/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.08/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.08/4.99  --sup_immed_bw_main                     []
% 35.08/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.08/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.08/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.08/4.99  --sup_input_bw                          []
% 35.08/4.99  
% 35.08/4.99  ------ Combination Options
% 35.08/4.99  
% 35.08/4.99  --comb_res_mult                         3
% 35.08/4.99  --comb_sup_mult                         2
% 35.08/4.99  --comb_inst_mult                        10
% 35.08/4.99  
% 35.08/4.99  ------ Debug Options
% 35.08/4.99  
% 35.08/4.99  --dbg_backtrace                         false
% 35.08/4.99  --dbg_dump_prop_clauses                 false
% 35.08/4.99  --dbg_dump_prop_clauses_file            -
% 35.08/4.99  --dbg_out_stat                          false
% 35.08/4.99  ------ Parsing...
% 35.08/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.08/4.99  
% 35.08/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 35.08/4.99  
% 35.08/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.08/4.99  
% 35.08/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.08/4.99  ------ Proving...
% 35.08/4.99  ------ Problem Properties 
% 35.08/4.99  
% 35.08/4.99  
% 35.08/4.99  clauses                                 53
% 35.08/4.99  conjectures                             5
% 35.08/4.99  EPR                                     6
% 35.08/4.99  Horn                                    47
% 35.08/4.99  unary                                   15
% 35.08/4.99  binary                                  11
% 35.08/4.99  lits                                    148
% 35.08/4.99  lits eq                                 27
% 35.08/4.99  fd_pure                                 0
% 35.08/4.99  fd_pseudo                               0
% 35.08/4.99  fd_cond                                 6
% 35.08/4.99  fd_pseudo_cond                          2
% 35.08/4.99  AC symbols                              0
% 35.08/4.99  
% 35.08/4.99  ------ Schedule dynamic 5 is on 
% 35.08/4.99  
% 35.08/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.08/4.99  
% 35.08/4.99  
% 35.08/4.99  ------ 
% 35.08/4.99  Current options:
% 35.08/4.99  ------ 
% 35.08/4.99  
% 35.08/4.99  ------ Input Options
% 35.08/4.99  
% 35.08/4.99  --out_options                           all
% 35.08/4.99  --tptp_safe_out                         true
% 35.08/4.99  --problem_path                          ""
% 35.08/4.99  --include_path                          ""
% 35.08/4.99  --clausifier                            res/vclausify_rel
% 35.08/4.99  --clausifier_options                    ""
% 35.08/4.99  --stdin                                 false
% 35.08/4.99  --stats_out                             all
% 35.08/4.99  
% 35.08/4.99  ------ General Options
% 35.08/4.99  
% 35.08/4.99  --fof                                   false
% 35.08/4.99  --time_out_real                         305.
% 35.08/4.99  --time_out_virtual                      -1.
% 35.08/4.99  --symbol_type_check                     false
% 35.08/4.99  --clausify_out                          false
% 35.08/4.99  --sig_cnt_out                           false
% 35.08/4.99  --trig_cnt_out                          false
% 35.08/4.99  --trig_cnt_out_tolerance                1.
% 35.08/4.99  --trig_cnt_out_sk_spl                   false
% 35.08/4.99  --abstr_cl_out                          false
% 35.08/4.99  
% 35.08/4.99  ------ Global Options
% 35.08/4.99  
% 35.08/4.99  --schedule                              default
% 35.08/4.99  --add_important_lit                     false
% 35.08/4.99  --prop_solver_per_cl                    1000
% 35.08/4.99  --min_unsat_core                        false
% 35.08/4.99  --soft_assumptions                      false
% 35.08/4.99  --soft_lemma_size                       3
% 35.08/4.99  --prop_impl_unit_size                   0
% 35.08/4.99  --prop_impl_unit                        []
% 35.08/4.99  --share_sel_clauses                     true
% 35.08/4.99  --reset_solvers                         false
% 35.08/4.99  --bc_imp_inh                            [conj_cone]
% 35.08/4.99  --conj_cone_tolerance                   3.
% 35.08/4.99  --extra_neg_conj                        none
% 35.08/4.99  --large_theory_mode                     true
% 35.08/4.99  --prolific_symb_bound                   200
% 35.08/4.99  --lt_threshold                          2000
% 35.08/4.99  --clause_weak_htbl                      true
% 35.08/4.99  --gc_record_bc_elim                     false
% 35.08/4.99  
% 35.08/4.99  ------ Preprocessing Options
% 35.08/4.99  
% 35.08/4.99  --preprocessing_flag                    true
% 35.08/4.99  --time_out_prep_mult                    0.1
% 35.08/4.99  --splitting_mode                        input
% 35.08/4.99  --splitting_grd                         true
% 35.08/4.99  --splitting_cvd                         false
% 35.08/4.99  --splitting_cvd_svl                     false
% 35.08/4.99  --splitting_nvd                         32
% 35.08/4.99  --sub_typing                            true
% 35.08/4.99  --prep_gs_sim                           true
% 35.08/4.99  --prep_unflatten                        true
% 35.08/4.99  --prep_res_sim                          true
% 35.08/4.99  --prep_upred                            true
% 35.08/4.99  --prep_sem_filter                       exhaustive
% 35.08/4.99  --prep_sem_filter_out                   false
% 35.08/4.99  --pred_elim                             true
% 35.08/4.99  --res_sim_input                         true
% 35.08/4.99  --eq_ax_congr_red                       true
% 35.08/4.99  --pure_diseq_elim                       true
% 35.08/4.99  --brand_transform                       false
% 35.08/4.99  --non_eq_to_eq                          false
% 35.08/4.99  --prep_def_merge                        true
% 35.08/4.99  --prep_def_merge_prop_impl              false
% 35.08/4.99  --prep_def_merge_mbd                    true
% 35.08/4.99  --prep_def_merge_tr_red                 false
% 35.08/4.99  --prep_def_merge_tr_cl                  false
% 35.08/4.99  --smt_preprocessing                     true
% 35.08/4.99  --smt_ac_axioms                         fast
% 35.08/4.99  --preprocessed_out                      false
% 35.08/4.99  --preprocessed_stats                    false
% 35.08/4.99  
% 35.08/4.99  ------ Abstraction refinement Options
% 35.08/4.99  
% 35.08/4.99  --abstr_ref                             []
% 35.08/4.99  --abstr_ref_prep                        false
% 35.08/4.99  --abstr_ref_until_sat                   false
% 35.08/4.99  --abstr_ref_sig_restrict                funpre
% 35.08/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.08/4.99  --abstr_ref_under                       []
% 35.08/4.99  
% 35.08/4.99  ------ SAT Options
% 35.08/4.99  
% 35.08/4.99  --sat_mode                              false
% 35.08/4.99  --sat_fm_restart_options                ""
% 35.08/4.99  --sat_gr_def                            false
% 35.08/4.99  --sat_epr_types                         true
% 35.08/4.99  --sat_non_cyclic_types                  false
% 35.08/4.99  --sat_finite_models                     false
% 35.08/4.99  --sat_fm_lemmas                         false
% 35.08/4.99  --sat_fm_prep                           false
% 35.08/4.99  --sat_fm_uc_incr                        true
% 35.08/4.99  --sat_out_model                         small
% 35.08/4.99  --sat_out_clauses                       false
% 35.08/4.99  
% 35.08/4.99  ------ QBF Options
% 35.08/4.99  
% 35.08/4.99  --qbf_mode                              false
% 35.08/4.99  --qbf_elim_univ                         false
% 35.08/4.99  --qbf_dom_inst                          none
% 35.08/4.99  --qbf_dom_pre_inst                      false
% 35.08/4.99  --qbf_sk_in                             false
% 35.08/4.99  --qbf_pred_elim                         true
% 35.08/4.99  --qbf_split                             512
% 35.08/4.99  
% 35.08/4.99  ------ BMC1 Options
% 35.08/4.99  
% 35.08/4.99  --bmc1_incremental                      false
% 35.08/4.99  --bmc1_axioms                           reachable_all
% 35.08/4.99  --bmc1_min_bound                        0
% 35.08/4.99  --bmc1_max_bound                        -1
% 35.08/4.99  --bmc1_max_bound_default                -1
% 35.08/4.99  --bmc1_symbol_reachability              true
% 35.08/4.99  --bmc1_property_lemmas                  false
% 35.08/4.99  --bmc1_k_induction                      false
% 35.08/4.99  --bmc1_non_equiv_states                 false
% 35.08/4.99  --bmc1_deadlock                         false
% 35.08/4.99  --bmc1_ucm                              false
% 35.08/4.99  --bmc1_add_unsat_core                   none
% 35.08/4.99  --bmc1_unsat_core_children              false
% 35.08/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.08/4.99  --bmc1_out_stat                         full
% 35.08/4.99  --bmc1_ground_init                      false
% 35.08/4.99  --bmc1_pre_inst_next_state              false
% 35.08/4.99  --bmc1_pre_inst_state                   false
% 35.08/4.99  --bmc1_pre_inst_reach_state             false
% 35.08/4.99  --bmc1_out_unsat_core                   false
% 35.08/4.99  --bmc1_aig_witness_out                  false
% 35.08/4.99  --bmc1_verbose                          false
% 35.08/4.99  --bmc1_dump_clauses_tptp                false
% 35.08/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.08/4.99  --bmc1_dump_file                        -
% 35.08/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.08/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.08/4.99  --bmc1_ucm_extend_mode                  1
% 35.08/4.99  --bmc1_ucm_init_mode                    2
% 35.08/4.99  --bmc1_ucm_cone_mode                    none
% 35.08/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.08/4.99  --bmc1_ucm_relax_model                  4
% 35.08/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.08/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.08/4.99  --bmc1_ucm_layered_model                none
% 35.08/4.99  --bmc1_ucm_max_lemma_size               10
% 35.08/4.99  
% 35.08/4.99  ------ AIG Options
% 35.08/4.99  
% 35.08/4.99  --aig_mode                              false
% 35.08/4.99  
% 35.08/4.99  ------ Instantiation Options
% 35.08/4.99  
% 35.08/4.99  --instantiation_flag                    true
% 35.08/4.99  --inst_sos_flag                         true
% 35.08/4.99  --inst_sos_phase                        true
% 35.08/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.08/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.08/4.99  --inst_lit_sel_side                     none
% 35.08/4.99  --inst_solver_per_active                1400
% 35.08/4.99  --inst_solver_calls_frac                1.
% 35.08/4.99  --inst_passive_queue_type               priority_queues
% 35.08/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.08/4.99  --inst_passive_queues_freq              [25;2]
% 35.08/4.99  --inst_dismatching                      true
% 35.08/4.99  --inst_eager_unprocessed_to_passive     true
% 35.08/4.99  --inst_prop_sim_given                   true
% 35.08/4.99  --inst_prop_sim_new                     false
% 35.08/4.99  --inst_subs_new                         false
% 35.08/4.99  --inst_eq_res_simp                      false
% 35.08/4.99  --inst_subs_given                       false
% 35.08/4.99  --inst_orphan_elimination               true
% 35.08/4.99  --inst_learning_loop_flag               true
% 35.08/4.99  --inst_learning_start                   3000
% 35.08/4.99  --inst_learning_factor                  2
% 35.08/4.99  --inst_start_prop_sim_after_learn       3
% 35.08/4.99  --inst_sel_renew                        solver
% 35.08/4.99  --inst_lit_activity_flag                true
% 35.08/4.99  --inst_restr_to_given                   false
% 35.08/4.99  --inst_activity_threshold               500
% 35.08/4.99  --inst_out_proof                        true
% 35.08/4.99  
% 35.08/4.99  ------ Resolution Options
% 35.08/4.99  
% 35.08/4.99  --resolution_flag                       false
% 35.08/4.99  --res_lit_sel                           adaptive
% 35.08/4.99  --res_lit_sel_side                      none
% 35.08/4.99  --res_ordering                          kbo
% 35.08/4.99  --res_to_prop_solver                    active
% 35.08/4.99  --res_prop_simpl_new                    false
% 35.08/4.99  --res_prop_simpl_given                  true
% 35.08/4.99  --res_passive_queue_type                priority_queues
% 35.08/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.08/4.99  --res_passive_queues_freq               [15;5]
% 35.08/4.99  --res_forward_subs                      full
% 35.08/4.99  --res_backward_subs                     full
% 35.08/4.99  --res_forward_subs_resolution           true
% 35.08/4.99  --res_backward_subs_resolution          true
% 35.08/4.99  --res_orphan_elimination                true
% 35.08/4.99  --res_time_limit                        2.
% 35.08/4.99  --res_out_proof                         true
% 35.08/4.99  
% 35.08/4.99  ------ Superposition Options
% 35.08/4.99  
% 35.08/4.99  --superposition_flag                    true
% 35.08/4.99  --sup_passive_queue_type                priority_queues
% 35.08/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.08/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.08/4.99  --demod_completeness_check              fast
% 35.08/4.99  --demod_use_ground                      true
% 35.08/4.99  --sup_to_prop_solver                    passive
% 35.08/4.99  --sup_prop_simpl_new                    true
% 35.08/4.99  --sup_prop_simpl_given                  true
% 35.08/4.99  --sup_fun_splitting                     true
% 35.08/4.99  --sup_smt_interval                      50000
% 35.08/4.99  
% 35.08/4.99  ------ Superposition Simplification Setup
% 35.08/4.99  
% 35.08/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.08/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.08/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.08/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.08/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.08/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.08/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.08/4.99  --sup_immed_triv                        [TrivRules]
% 35.08/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.08/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.08/4.99  --sup_immed_bw_main                     []
% 35.08/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.08/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.08/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.08/4.99  --sup_input_bw                          []
% 35.08/4.99  
% 35.08/4.99  ------ Combination Options
% 35.08/4.99  
% 35.08/4.99  --comb_res_mult                         3
% 35.08/4.99  --comb_sup_mult                         2
% 35.08/4.99  --comb_inst_mult                        10
% 35.08/4.99  
% 35.08/4.99  ------ Debug Options
% 35.08/4.99  
% 35.08/4.99  --dbg_backtrace                         false
% 35.08/4.99  --dbg_dump_prop_clauses                 false
% 35.08/4.99  --dbg_dump_prop_clauses_file            -
% 35.08/4.99  --dbg_out_stat                          false
% 35.08/4.99  
% 35.08/4.99  
% 35.08/4.99  
% 35.08/4.99  
% 35.08/4.99  ------ Proving...
% 35.08/4.99  
% 35.08/4.99  
% 35.08/4.99  % SZS status Theorem for theBenchmark.p
% 35.08/4.99  
% 35.08/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.08/4.99  
% 35.08/4.99  fof(f30,axiom,(
% 35.08/4.99    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f92,plain,(
% 35.08/4.99    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v5_relat_1(sK3(X0,X1),X1) & v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 35.08/4.99    introduced(choice_axiom,[])).
% 35.08/4.99  
% 35.08/4.99  fof(f93,plain,(
% 35.08/4.99    ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v5_relat_1(sK3(X0,X1),X1) & v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f92])).
% 35.08/4.99  
% 35.08/4.99  fof(f141,plain,(
% 35.08/4.99    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f93])).
% 35.08/4.99  
% 35.08/4.99  fof(f23,axiom,(
% 35.08/4.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f125,plain,(
% 35.08/4.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f23])).
% 35.08/4.99  
% 35.08/4.99  fof(f33,axiom,(
% 35.08/4.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f149,plain,(
% 35.08/4.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f33])).
% 35.08/4.99  
% 35.08/4.99  fof(f160,plain,(
% 35.08/4.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.08/4.99    inference(definition_unfolding,[],[f125,f149])).
% 35.08/4.99  
% 35.08/4.99  fof(f22,axiom,(
% 35.08/4.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f57,plain,(
% 35.08/4.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 35.08/4.99    inference(ennf_transformation,[],[f22])).
% 35.08/4.99  
% 35.08/4.99  fof(f58,plain,(
% 35.08/4.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    inference(flattening,[],[f57])).
% 35.08/4.99  
% 35.08/4.99  fof(f124,plain,(
% 35.08/4.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f58])).
% 35.08/4.99  
% 35.08/4.99  fof(f36,conjecture,(
% 35.08/4.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f37,negated_conjecture,(
% 35.08/4.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 35.08/4.99    inference(negated_conjecture,[],[f36])).
% 35.08/4.99  
% 35.08/4.99  fof(f78,plain,(
% 35.08/4.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 35.08/4.99    inference(ennf_transformation,[],[f37])).
% 35.08/4.99  
% 35.08/4.99  fof(f79,plain,(
% 35.08/4.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 35.08/4.99    inference(flattening,[],[f78])).
% 35.08/4.99  
% 35.08/4.99  fof(f94,plain,(
% 35.08/4.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) | ~r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) & v3_funct_2(sK5,sK4,sK4) & v1_funct_2(sK5,sK4,sK4) & v1_funct_1(sK5))),
% 35.08/4.99    introduced(choice_axiom,[])).
% 35.08/4.99  
% 35.08/4.99  fof(f95,plain,(
% 35.08/4.99    (~r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) | ~r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) & v3_funct_2(sK5,sK4,sK4) & v1_funct_2(sK5,sK4,sK4) & v1_funct_1(sK5)),
% 35.08/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f79,f94])).
% 35.08/4.99  
% 35.08/4.99  fof(f158,plain,(
% 35.08/4.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))),
% 35.08/4.99    inference(cnf_transformation,[],[f95])).
% 35.08/4.99  
% 35.08/4.99  fof(f32,axiom,(
% 35.08/4.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f72,plain,(
% 35.08/4.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 35.08/4.99    inference(ennf_transformation,[],[f32])).
% 35.08/4.99  
% 35.08/4.99  fof(f73,plain,(
% 35.08/4.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 35.08/4.99    inference(flattening,[],[f72])).
% 35.08/4.99  
% 35.08/4.99  fof(f148,plain,(
% 35.08/4.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f73])).
% 35.08/4.99  
% 35.08/4.99  fof(f155,plain,(
% 35.08/4.99    v1_funct_1(sK5)),
% 35.08/4.99    inference(cnf_transformation,[],[f95])).
% 35.08/4.99  
% 35.08/4.99  fof(f156,plain,(
% 35.08/4.99    v1_funct_2(sK5,sK4,sK4)),
% 35.08/4.99    inference(cnf_transformation,[],[f95])).
% 35.08/4.99  
% 35.08/4.99  fof(f157,plain,(
% 35.08/4.99    v3_funct_2(sK5,sK4,sK4)),
% 35.08/4.99    inference(cnf_transformation,[],[f95])).
% 35.08/4.99  
% 35.08/4.99  fof(f29,axiom,(
% 35.08/4.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f68,plain,(
% 35.08/4.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 35.08/4.99    inference(ennf_transformation,[],[f29])).
% 35.08/4.99  
% 35.08/4.99  fof(f69,plain,(
% 35.08/4.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 35.08/4.99    inference(flattening,[],[f68])).
% 35.08/4.99  
% 35.08/4.99  fof(f140,plain,(
% 35.08/4.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f69])).
% 35.08/4.99  
% 35.08/4.99  fof(f31,axiom,(
% 35.08/4.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f70,plain,(
% 35.08/4.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.08/4.99    inference(ennf_transformation,[],[f31])).
% 35.08/4.99  
% 35.08/4.99  fof(f71,plain,(
% 35.08/4.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.08/4.99    inference(flattening,[],[f70])).
% 35.08/4.99  
% 35.08/4.99  fof(f147,plain,(
% 35.08/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f71])).
% 35.08/4.99  
% 35.08/4.99  fof(f137,plain,(
% 35.08/4.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f69])).
% 35.08/4.99  
% 35.08/4.99  fof(f28,axiom,(
% 35.08/4.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f66,plain,(
% 35.08/4.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.08/4.99    inference(ennf_transformation,[],[f28])).
% 35.08/4.99  
% 35.08/4.99  fof(f67,plain,(
% 35.08/4.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.08/4.99    inference(flattening,[],[f66])).
% 35.08/4.99  
% 35.08/4.99  fof(f136,plain,(
% 35.08/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f67])).
% 35.08/4.99  
% 35.08/4.99  fof(f135,plain,(
% 35.08/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f67])).
% 35.08/4.99  
% 35.08/4.99  fof(f25,axiom,(
% 35.08/4.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f60,plain,(
% 35.08/4.99    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 35.08/4.99    inference(ennf_transformation,[],[f25])).
% 35.08/4.99  
% 35.08/4.99  fof(f61,plain,(
% 35.08/4.99    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 35.08/4.99    inference(flattening,[],[f60])).
% 35.08/4.99  
% 35.08/4.99  fof(f89,plain,(
% 35.08/4.99    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK2(X0,X1,X2)) != k11_relat_1(X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X0)))),
% 35.08/4.99    introduced(choice_axiom,[])).
% 35.08/4.99  
% 35.08/4.99  fof(f90,plain,(
% 35.08/4.99    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK2(X0,X1,X2)) != k11_relat_1(X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 35.08/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f89])).
% 35.08/4.99  
% 35.08/4.99  fof(f128,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (r2_relset_1(X0,X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f90])).
% 35.08/4.99  
% 35.08/4.99  fof(f1,axiom,(
% 35.08/4.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f80,plain,(
% 35.08/4.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 35.08/4.99    inference(nnf_transformation,[],[f1])).
% 35.08/4.99  
% 35.08/4.99  fof(f81,plain,(
% 35.08/4.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 35.08/4.99    inference(rectify,[],[f80])).
% 35.08/4.99  
% 35.08/4.99  fof(f82,plain,(
% 35.08/4.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 35.08/4.99    introduced(choice_axiom,[])).
% 35.08/4.99  
% 35.08/4.99  fof(f83,plain,(
% 35.08/4.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 35.08/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f81,f82])).
% 35.08/4.99  
% 35.08/4.99  fof(f96,plain,(
% 35.08/4.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f83])).
% 35.08/4.99  
% 35.08/4.99  fof(f159,plain,(
% 35.08/4.99    ~r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) | ~r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4))),
% 35.08/4.99    inference(cnf_transformation,[],[f95])).
% 35.08/4.99  
% 35.08/4.99  fof(f7,axiom,(
% 35.08/4.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f86,plain,(
% 35.08/4.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 35.08/4.99    inference(nnf_transformation,[],[f7])).
% 35.08/4.99  
% 35.08/4.99  fof(f87,plain,(
% 35.08/4.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 35.08/4.99    inference(flattening,[],[f86])).
% 35.08/4.99  
% 35.08/4.99  fof(f105,plain,(
% 35.08/4.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 35.08/4.99    inference(cnf_transformation,[],[f87])).
% 35.08/4.99  
% 35.08/4.99  fof(f161,plain,(
% 35.08/4.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 35.08/4.99    inference(equality_resolution,[],[f105])).
% 35.08/4.99  
% 35.08/4.99  fof(f2,axiom,(
% 35.08/4.99    v1_xboole_0(k1_xboole_0)),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f98,plain,(
% 35.08/4.99    v1_xboole_0(k1_xboole_0)),
% 35.08/4.99    inference(cnf_transformation,[],[f2])).
% 35.08/4.99  
% 35.08/4.99  fof(f8,axiom,(
% 35.08/4.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f106,plain,(
% 35.08/4.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f8])).
% 35.08/4.99  
% 35.08/4.99  fof(f6,axiom,(
% 35.08/4.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f41,plain,(
% 35.08/4.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 35.08/4.99    inference(ennf_transformation,[],[f6])).
% 35.08/4.99  
% 35.08/4.99  fof(f102,plain,(
% 35.08/4.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f41])).
% 35.08/4.99  
% 35.08/4.99  fof(f10,axiom,(
% 35.08/4.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f44,plain,(
% 35.08/4.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 35.08/4.99    inference(ennf_transformation,[],[f10])).
% 35.08/4.99  
% 35.08/4.99  fof(f108,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f44])).
% 35.08/4.99  
% 35.08/4.99  fof(f26,axiom,(
% 35.08/4.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f62,plain,(
% 35.08/4.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    inference(ennf_transformation,[],[f26])).
% 35.08/4.99  
% 35.08/4.99  fof(f63,plain,(
% 35.08/4.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    inference(flattening,[],[f62])).
% 35.08/4.99  
% 35.08/4.99  fof(f131,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f63])).
% 35.08/4.99  
% 35.08/4.99  fof(f24,axiom,(
% 35.08/4.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f59,plain,(
% 35.08/4.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    inference(ennf_transformation,[],[f24])).
% 35.08/4.99  
% 35.08/4.99  fof(f126,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f59])).
% 35.08/4.99  
% 35.08/4.99  fof(f21,axiom,(
% 35.08/4.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f56,plain,(
% 35.08/4.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    inference(ennf_transformation,[],[f21])).
% 35.08/4.99  
% 35.08/4.99  fof(f123,plain,(
% 35.08/4.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f56])).
% 35.08/4.99  
% 35.08/4.99  fof(f34,axiom,(
% 35.08/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f74,plain,(
% 35.08/4.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 35.08/4.99    inference(ennf_transformation,[],[f34])).
% 35.08/4.99  
% 35.08/4.99  fof(f75,plain,(
% 35.08/4.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.08/4.99    inference(flattening,[],[f74])).
% 35.08/4.99  
% 35.08/4.99  fof(f151,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f75])).
% 35.08/4.99  
% 35.08/4.99  fof(f132,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f63])).
% 35.08/4.99  
% 35.08/4.99  fof(f27,axiom,(
% 35.08/4.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f64,plain,(
% 35.08/4.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 35.08/4.99    inference(ennf_transformation,[],[f27])).
% 35.08/4.99  
% 35.08/4.99  fof(f65,plain,(
% 35.08/4.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 35.08/4.99    inference(flattening,[],[f64])).
% 35.08/4.99  
% 35.08/4.99  fof(f91,plain,(
% 35.08/4.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 35.08/4.99    inference(nnf_transformation,[],[f65])).
% 35.08/4.99  
% 35.08/4.99  fof(f133,plain,(
% 35.08/4.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f91])).
% 35.08/4.99  
% 35.08/4.99  fof(f17,axiom,(
% 35.08/4.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f52,plain,(
% 35.08/4.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    inference(ennf_transformation,[],[f17])).
% 35.08/4.99  
% 35.08/4.99  fof(f118,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f52])).
% 35.08/4.99  
% 35.08/4.99  fof(f18,axiom,(
% 35.08/4.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f53,plain,(
% 35.08/4.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.08/4.99    inference(ennf_transformation,[],[f18])).
% 35.08/4.99  
% 35.08/4.99  fof(f120,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.08/4.99    inference(cnf_transformation,[],[f53])).
% 35.08/4.99  
% 35.08/4.99  fof(f35,axiom,(
% 35.08/4.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f76,plain,(
% 35.08/4.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.08/4.99    inference(ennf_transformation,[],[f35])).
% 35.08/4.99  
% 35.08/4.99  fof(f77,plain,(
% 35.08/4.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.08/4.99    inference(flattening,[],[f76])).
% 35.08/4.99  
% 35.08/4.99  fof(f153,plain,(
% 35.08/4.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f77])).
% 35.08/4.99  
% 35.08/4.99  fof(f154,plain,(
% 35.08/4.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f77])).
% 35.08/4.99  
% 35.08/4.99  fof(f14,axiom,(
% 35.08/4.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f47,plain,(
% 35.08/4.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 35.08/4.99    inference(ennf_transformation,[],[f14])).
% 35.08/4.99  
% 35.08/4.99  fof(f113,plain,(
% 35.08/4.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f47])).
% 35.08/4.99  
% 35.08/4.99  fof(f16,axiom,(
% 35.08/4.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 35.08/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.08/4.99  
% 35.08/4.99  fof(f50,plain,(
% 35.08/4.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.08/4.99    inference(ennf_transformation,[],[f16])).
% 35.08/4.99  
% 35.08/4.99  fof(f51,plain,(
% 35.08/4.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.08/4.99    inference(flattening,[],[f50])).
% 35.08/4.99  
% 35.08/4.99  fof(f117,plain,(
% 35.08/4.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f51])).
% 35.08/4.99  
% 35.08/4.99  fof(f139,plain,(
% 35.08/4.99    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f69])).
% 35.08/4.99  
% 35.08/4.99  fof(f150,plain,(
% 35.08/4.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.08/4.99    inference(cnf_transformation,[],[f75])).
% 35.08/4.99  
% 35.08/4.99  cnf(c_50,plain,
% 35.08/4.99      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 35.08/4.99      inference(cnf_transformation,[],[f141]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2486,plain,
% 35.08/4.99      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_29,plain,
% 35.08/4.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 35.08/4.99      inference(cnf_transformation,[],[f160]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2501,plain,
% 35.08/4.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_28,plain,
% 35.08/4.99      ( r2_relset_1(X0,X1,X2,X2)
% 35.08/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.08/4.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 35.08/4.99      inference(cnf_transformation,[],[f124]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2502,plain,
% 35.08/4.99      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_10573,plain,
% 35.08/4.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 35.08/4.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_2501,c_2502]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_104651,plain,
% 35.08/4.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_2486,c_10573]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_104675,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(sK4)) = iProver_top ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_104651]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_1669,plain,
% 35.08/4.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 35.08/4.99      | r2_relset_1(X4,X5,X6,X7)
% 35.08/4.99      | X4 != X0
% 35.08/4.99      | X5 != X1
% 35.08/4.99      | X6 != X2
% 35.08/4.99      | X7 != X3 ),
% 35.08/4.99      theory(equality) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_50488,plain,
% 35.08/4.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 35.08/4.99      | r2_relset_1(X4,X5,X6,k6_partfun1(X7))
% 35.08/4.99      | X4 != X0
% 35.08/4.99      | X5 != X1
% 35.08/4.99      | X6 != X2
% 35.08/4.99      | k6_partfun1(X7) != X3 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_1669]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_53660,plain,
% 35.08/4.99      ( ~ r2_relset_1(X0,X1,X2,k6_partfun1(X3))
% 35.08/4.99      | r2_relset_1(X4,X5,X6,k6_partfun1(X7))
% 35.08/4.99      | X4 != X0
% 35.08/4.99      | X5 != X1
% 35.08/4.99      | X6 != X2
% 35.08/4.99      | k6_partfun1(X7) != k6_partfun1(X3) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_50488]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_62736,plain,
% 35.08/4.99      ( r2_relset_1(X0,X1,X2,k6_partfun1(X3))
% 35.08/4.99      | ~ r2_relset_1(X4,X4,k6_partfun1(X4),k6_partfun1(X5))
% 35.08/4.99      | X0 != X4
% 35.08/4.99      | X1 != X4
% 35.08/4.99      | X2 != k6_partfun1(X4)
% 35.08/4.99      | k6_partfun1(X3) != k6_partfun1(X5) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_53660]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_84764,plain,
% 35.08/4.99      ( r2_relset_1(X0,X1,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(X2))
% 35.08/4.99      | ~ r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(X3))
% 35.08/4.99      | X0 != sK4
% 35.08/4.99      | X1 != sK4
% 35.08/4.99      | k5_relat_1(sK5,k2_funct_1(sK5)) != k6_partfun1(sK4)
% 35.08/4.99      | k6_partfun1(X2) != k6_partfun1(X3) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_62736]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_84765,plain,
% 35.08/4.99      ( X0 != sK4
% 35.08/4.99      | X1 != sK4
% 35.08/4.99      | k5_relat_1(sK5,k2_funct_1(sK5)) != k6_partfun1(sK4)
% 35.08/4.99      | k6_partfun1(X2) != k6_partfun1(X3)
% 35.08/4.99      | r2_relset_1(X0,X1,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(X2)) = iProver_top
% 35.08/4.99      | r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(X3)) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_84764]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_84767,plain,
% 35.08/4.99      ( k5_relat_1(sK5,k2_funct_1(sK5)) != k6_partfun1(sK4)
% 35.08/4.99      | k6_partfun1(sK4) != k6_partfun1(sK4)
% 35.08/4.99      | sK4 != sK4
% 35.08/4.99      | r2_relset_1(sK4,sK4,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) = iProver_top
% 35.08/4.99      | r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(sK4)) != iProver_top ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_84765]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_59,negated_conjecture,
% 35.08/4.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) ),
% 35.08/4.99      inference(cnf_transformation,[],[f158]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2478,plain,
% 35.08/4.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_52,plain,
% 35.08/4.99      ( ~ v1_funct_2(X0,X1,X1)
% 35.08/4.99      | ~ v3_funct_2(X0,X1,X1)
% 35.08/4.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 35.08/4.99      | ~ v1_funct_1(X0)
% 35.08/4.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 35.08/4.99      inference(cnf_transformation,[],[f148]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2484,plain,
% 35.08/4.99      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 35.08/4.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 35.08/4.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 35.08/4.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 35.08/4.99      | v1_funct_1(X1) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_6616,plain,
% 35.08/4.99      ( k2_funct_2(sK4,sK5) = k2_funct_1(sK5)
% 35.08/4.99      | v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_2478,c_2484]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_62,negated_conjecture,
% 35.08/4.99      ( v1_funct_1(sK5) ),
% 35.08/4.99      inference(cnf_transformation,[],[f155]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_63,plain,
% 35.08/4.99      ( v1_funct_1(sK5) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_61,negated_conjecture,
% 35.08/4.99      ( v1_funct_2(sK5,sK4,sK4) ),
% 35.08/4.99      inference(cnf_transformation,[],[f156]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_64,plain,
% 35.08/4.99      ( v1_funct_2(sK5,sK4,sK4) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_60,negated_conjecture,
% 35.08/4.99      ( v3_funct_2(sK5,sK4,sK4) ),
% 35.08/4.99      inference(cnf_transformation,[],[f157]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_65,plain,
% 35.08/4.99      ( v3_funct_2(sK5,sK4,sK4) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_6865,plain,
% 35.08/4.99      ( k2_funct_2(sK4,sK5) = k2_funct_1(sK5) ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_6616,c_63,c_64,c_65]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_41,plain,
% 35.08/4.99      ( ~ v1_funct_2(X0,X1,X1)
% 35.08/4.99      | ~ v3_funct_2(X0,X1,X1)
% 35.08/4.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 35.08/4.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 35.08/4.99      | ~ v1_funct_1(X0) ),
% 35.08/4.99      inference(cnf_transformation,[],[f140]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2493,plain,
% 35.08/4.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 35.08/4.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 35.08/4.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 35.08/4.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 35.08/4.99      | v1_funct_1(X0) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_11083,plain,
% 35.08/4.99      ( v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_6865,c_2493]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_66,plain,
% 35.08/4.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_11723,plain,
% 35.08/4.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_11083,c_63,c_64,c_65,c_66]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_51,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/4.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.08/4.99      | ~ v1_funct_1(X0)
% 35.08/4.99      | ~ v1_funct_1(X3)
% 35.08/4.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 35.08/4.99      inference(cnf_transformation,[],[f147]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2485,plain,
% 35.08/4.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 35.08/4.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 35.08/4.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | v1_funct_1(X5) != iProver_top
% 35.08/4.99      | v1_funct_1(X4) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_11744,plain,
% 35.08/4.99      ( k1_partfun1(X0,X1,sK4,sK4,X2,k2_funct_1(sK5)) = k5_relat_1(X2,k2_funct_1(sK5))
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | v1_funct_1(X2) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_11723,c_2485]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_44,plain,
% 35.08/4.99      ( ~ v1_funct_2(X0,X1,X1)
% 35.08/4.99      | ~ v3_funct_2(X0,X1,X1)
% 35.08/4.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 35.08/4.99      | ~ v1_funct_1(X0)
% 35.08/4.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 35.08/4.99      inference(cnf_transformation,[],[f137]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2490,plain,
% 35.08/4.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 35.08/4.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 35.08/4.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 35.08/4.99      | v1_funct_1(X0) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_7990,plain,
% 35.08/4.99      ( v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_2(sK4,sK5)) = iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_2478,c_2490]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_7993,plain,
% 35.08/4.99      ( v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_1(sK5)) = iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(light_normalisation,[status(thm)],[c_7990,c_6865]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_20710,plain,
% 35.08/4.99      ( v1_funct_1(X2) != iProver_top
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | k1_partfun1(X0,X1,sK4,sK4,X2,k2_funct_1(sK5)) = k5_relat_1(X2,k2_funct_1(sK5)) ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_11744,c_63,c_64,c_65,c_7993]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_20711,plain,
% 35.08/4.99      ( k1_partfun1(X0,X1,sK4,sK4,X2,k2_funct_1(sK5)) = k5_relat_1(X2,k2_funct_1(sK5))
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | v1_funct_1(X2) != iProver_top ),
% 35.08/4.99      inference(renaming,[status(thm)],[c_20710]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_20723,plain,
% 35.08/4.99      ( k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_1(sK5)) = k5_relat_1(sK5,k2_funct_1(sK5))
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_2478,c_20711]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_20759,plain,
% 35.08/4.99      ( k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_1(sK5)) = k5_relat_1(sK5,k2_funct_1(sK5)) ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_20723,c_63]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_39,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/4.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.08/4.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 35.08/4.99      | ~ v1_funct_1(X0)
% 35.08/4.99      | ~ v1_funct_1(X3) ),
% 35.08/4.99      inference(cnf_transformation,[],[f136]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2495,plain,
% 35.08/4.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.08/4.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 35.08/4.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 35.08/4.99      | v1_funct_1(X0) != iProver_top
% 35.08/4.99      | v1_funct_1(X3) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_20763,plain,
% 35.08/4.99      ( m1_subset_1(k5_relat_1(sK5,k2_funct_1(sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_20759,c_2495]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_20827,plain,
% 35.08/4.99      ( m1_subset_1(k5_relat_1(sK5,k2_funct_1(sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_20763,c_63,c_64,c_65,c_66,c_7993,c_11083]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_20852,plain,
% 35.08/4.99      ( k1_partfun1(X0,X1,sK4,sK4,X2,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(X2,k5_relat_1(sK5,k2_funct_1(sK5)))
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | v1_funct_1(X2) != iProver_top
% 35.08/4.99      | v1_funct_1(k5_relat_1(sK5,k2_funct_1(sK5))) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_20827,c_2485]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_40,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/4.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.08/4.99      | ~ v1_funct_1(X0)
% 35.08/4.99      | ~ v1_funct_1(X3)
% 35.08/4.99      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
% 35.08/4.99      inference(cnf_transformation,[],[f135]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2494,plain,
% 35.08/4.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.08/4.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 35.08/4.99      | v1_funct_1(X0) != iProver_top
% 35.08/4.99      | v1_funct_1(X3) != iProver_top
% 35.08/4.99      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_20764,plain,
% 35.08/4.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | v1_funct_1(k5_relat_1(sK5,k2_funct_1(sK5))) = iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_20759,c_2494]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_31197,plain,
% 35.08/4.99      ( v1_funct_1(X2) != iProver_top
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | k1_partfun1(X0,X1,sK4,sK4,X2,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(X2,k5_relat_1(sK5,k2_funct_1(sK5))) ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_20852,c_63,c_64,c_65,c_66,c_7993,c_11083,c_20764]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_31198,plain,
% 35.08/4.99      ( k1_partfun1(X0,X1,sK4,sK4,X2,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(X2,k5_relat_1(sK5,k2_funct_1(sK5)))
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | v1_funct_1(X2) != iProver_top ),
% 35.08/4.99      inference(renaming,[status(thm)],[c_31197]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_31210,plain,
% 35.08/4.99      ( k1_partfun1(sK4,sK4,sK4,sK4,sK5,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5)))
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_2478,c_31198]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_31400,plain,
% 35.08/4.99      ( k1_partfun1(sK4,sK4,sK4,sK4,sK5,k5_relat_1(sK5,k2_funct_1(sK5))) = k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5))) ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_31210,c_63]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_31402,plain,
% 35.08/4.99      ( m1_subset_1(k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5))),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(k5_relat_1(sK5,k2_funct_1(sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | v1_funct_1(k5_relat_1(sK5,k2_funct_1(sK5))) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_31400,c_2495]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_31864,plain,
% 35.08/4.99      ( m1_subset_1(k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5))),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_31402,c_63,c_64,c_65,c_66,c_7993,c_11083,c_20763,
% 35.08/4.99                 c_20764]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_33,plain,
% 35.08/4.99      ( r2_relset_1(X0,X0,X1,X2)
% 35.08/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 35.08/4.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 35.08/4.99      | r2_hidden(sK2(X0,X1,X2),X0) ),
% 35.08/4.99      inference(cnf_transformation,[],[f128]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2497,plain,
% 35.08/4.99      ( r2_relset_1(X0,X0,X1,X2) = iProver_top
% 35.08/4.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 35.08/4.99      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_13786,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,sK5,X0) = iProver_top
% 35.08/4.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | r2_hidden(sK2(sK4,sK5,X0),sK4) = iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_2478,c_2497]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_31893,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,sK5,k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5)))) = iProver_top
% 35.08/4.99      | r2_hidden(sK2(sK4,sK5,k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5)))),sK4) = iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_31864,c_13786]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_1,plain,
% 35.08/4.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 35.08/4.99      inference(cnf_transformation,[],[f96]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2520,plain,
% 35.08/4.99      ( r2_hidden(X0,X1) != iProver_top
% 35.08/4.99      | v1_xboole_0(X1) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_31982,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,sK5,k5_relat_1(sK5,k5_relat_1(sK5,k2_funct_1(sK5)))) = iProver_top
% 35.08/4.99      | v1_xboole_0(sK4) != iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_31893,c_2520]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_58,negated_conjecture,
% 35.08/4.99      ( ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4))
% 35.08/4.99      | ~ r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) ),
% 35.08/4.99      inference(cnf_transformation,[],[f159]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_67,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) != iProver_top
% 35.08/4.99      | r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_148,plain,
% 35.08/4.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_150,plain,
% 35.08/4.99      ( m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_148]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_7,plain,
% 35.08/4.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.08/4.99      inference(cnf_transformation,[],[f161]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_206,plain,
% 35.08/4.99      ( k2_zfmisc_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_7]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2,plain,
% 35.08/4.99      ( v1_xboole_0(k1_xboole_0) ),
% 35.08/4.99      inference(cnf_transformation,[],[f98]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_219,plain,
% 35.08/4.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_1657,plain,( X0 = X0 ),theory(equality) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_1698,plain,
% 35.08/4.99      ( sK4 = sK4 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_1657]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2581,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4))
% 35.08/4.99      | ~ m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)),sK4) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_33]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2582,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) = iProver_top
% 35.08/4.99      | m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)),sK4) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_2581]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2601,plain,
% 35.08/4.99      ( m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ v1_funct_1(k2_funct_2(sK4,sK5))
% 35.08/4.99      | ~ v1_funct_1(sK5) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_39]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2602,plain,
% 35.08/4.99      ( m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_2(sK4,sK5)) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_2601]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2649,plain,
% 35.08/4.99      ( ~ v1_funct_2(sK5,sK4,sK4)
% 35.08/4.99      | ~ v3_funct_2(sK5,sK4,sK4)
% 35.08/4.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | v1_funct_1(k2_funct_2(sK4,sK5))
% 35.08/4.99      | ~ v1_funct_1(sK5) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_44]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2650,plain,
% 35.08/4.99      ( v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_2(sK4,sK5)) = iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_2649]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2773,plain,
% 35.08/4.99      ( ~ v1_funct_2(sK5,sK4,sK4)
% 35.08/4.99      | ~ v3_funct_2(sK5,sK4,sK4)
% 35.08/4.99      | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ v1_funct_1(sK5) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_41]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2774,plain,
% 35.08/4.99      ( v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_2773]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2806,plain,
% 35.08/4.99      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_1657]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2907,plain,
% 35.08/4.99      ( ~ r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)),sK4)
% 35.08/4.99      | ~ v1_xboole_0(sK4) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_1]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2908,plain,
% 35.08/4.99      ( r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)),sK4) != iProver_top
% 35.08/4.99      | v1_xboole_0(sK4) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_2907]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_10,plain,
% 35.08/4.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 35.08/4.99      inference(cnf_transformation,[],[f106]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_3402,plain,
% 35.08/4.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_10]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_3403,plain,
% 35.08/4.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_3402]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_6,plain,
% 35.08/4.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 35.08/4.99      inference(cnf_transformation,[],[f102]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_4157,plain,
% 35.08/4.99      ( ~ v1_xboole_0(X0)
% 35.08/4.99      | ~ v1_xboole_0(k1_xboole_0)
% 35.08/4.99      | X0 = k1_xboole_0 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_6]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_4158,plain,
% 35.08/4.99      ( X0 = k1_xboole_0
% 35.08/4.99      | v1_xboole_0(X0) != iProver_top
% 35.08/4.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_4157]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_4160,plain,
% 35.08/4.99      ( sK4 = k1_xboole_0
% 35.08/4.99      | v1_xboole_0(sK4) != iProver_top
% 35.08/4.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_4158]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_1659,plain,
% 35.08/4.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 35.08/4.99      theory(equality) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_3286,plain,
% 35.08/4.99      ( v1_xboole_0(X0)
% 35.08/4.99      | ~ v1_xboole_0(k1_xboole_0)
% 35.08/4.99      | X0 != k1_xboole_0 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_1659]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_4162,plain,
% 35.08/4.99      ( v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
% 35.08/4.99      | ~ v1_xboole_0(k1_xboole_0)
% 35.08/4.99      | k2_zfmisc_1(X0,k1_xboole_0) != k1_xboole_0 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_3286]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_4163,plain,
% 35.08/4.99      ( k2_zfmisc_1(X0,k1_xboole_0) != k1_xboole_0
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top
% 35.08/4.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_4162]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_4165,plain,
% 35.08/4.99      ( k2_zfmisc_1(sK4,k1_xboole_0) != k1_xboole_0
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(sK4,k1_xboole_0)) = iProver_top
% 35.08/4.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_4163]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_1663,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.08/4.99      theory(equality) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2981,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,X1)
% 35.08/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | X2 != X0
% 35.08/4.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != X1 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_1663]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_3702,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | X1 != X0
% 35.08/4.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_2981]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_5388,plain,
% 35.08/4.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | X0 != k1_xboole_0
% 35.08/4.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_3702]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_5389,plain,
% 35.08/4.99      ( X0 != k1_xboole_0
% 35.08/4.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))
% 35.08/4.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_5388]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_5391,plain,
% 35.08/4.99      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))
% 35.08/4.99      | sK4 != k1_xboole_0
% 35.08/4.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_5389]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2623,plain,
% 35.08/4.99      ( ~ v1_xboole_0(X0)
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(sK4,sK4))
% 35.08/4.99      | k2_zfmisc_1(sK4,sK4) != X0 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_1659]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_6110,plain,
% 35.08/4.99      ( ~ v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(sK4,sK4))
% 35.08/4.99      | k2_zfmisc_1(sK4,sK4) != k2_zfmisc_1(X0,k1_xboole_0) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_2623]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_6151,plain,
% 35.08/4.99      ( k2_zfmisc_1(sK4,sK4) != k2_zfmisc_1(X0,k1_xboole_0)
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(sK4,sK4)) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_6110]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_6153,plain,
% 35.08/4.99      ( k2_zfmisc_1(sK4,sK4) != k2_zfmisc_1(sK4,k1_xboole_0)
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(sK4,sK4)) = iProver_top
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(sK4,k1_xboole_0)) != iProver_top ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_6151]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_1661,plain,
% 35.08/4.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 35.08/4.99      theory(equality) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_10048,plain,
% 35.08/4.99      ( k2_zfmisc_1(sK4,sK4) = k2_zfmisc_1(X0,k1_xboole_0)
% 35.08/4.99      | sK4 != X0
% 35.08/4.99      | sK4 != k1_xboole_0 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_1661]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_10049,plain,
% 35.08/4.99      ( k2_zfmisc_1(sK4,sK4) = k2_zfmisc_1(sK4,k1_xboole_0)
% 35.08/4.99      | sK4 != sK4
% 35.08/4.99      | sK4 != k1_xboole_0 ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_10048]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_3731,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
% 35.08/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,X3)))
% 35.08/4.99      | m1_subset_1(k1_partfun1(sK4,X3,X1,sK4,X2,X0),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ v1_funct_1(X0)
% 35.08/4.99      | ~ v1_funct_1(X2) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_39]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_7347,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 35.08/4.99      | m1_subset_1(k1_partfun1(sK4,X1,X2,sK4,X0,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X2,sK4)))
% 35.08/4.99      | ~ v1_funct_1(X0)
% 35.08/4.99      | ~ v1_funct_1(k2_funct_2(sK4,sK5)) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_3731]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_10687,plain,
% 35.08/4.99      ( m1_subset_1(k1_partfun1(sK4,X0,X1,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
% 35.08/4.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
% 35.08/4.99      | ~ v1_funct_1(k2_funct_2(sK4,sK5))
% 35.08/4.99      | ~ v1_funct_1(sK5) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_7347]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_10688,plain,
% 35.08/4.99      ( m1_subset_1(k1_partfun1(sK4,X0,X1,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X1,sK4))) != iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_2(sK4,sK5)) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_10687]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_10690,plain,
% 35.08/4.99      ( m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 35.08/4.99      | m1_subset_1(k2_funct_2(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | v1_funct_1(k2_funct_2(sK4,sK5)) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_10688]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_17258,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4))
% 35.08/4.99      | ~ m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)),sK4) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_33]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_17259,plain,
% 35.08/4.99      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) = iProver_top
% 35.08/4.99      | m1_subset_1(k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)),sK4) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_17258]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_12,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.08/4.99      | ~ r2_hidden(X2,X0)
% 35.08/4.99      | ~ v1_xboole_0(X1) ),
% 35.08/4.99      inference(cnf_transformation,[],[f108]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2701,plain,
% 35.08/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ r2_hidden(X1,X0)
% 35.08/4.99      | ~ v1_xboole_0(k2_zfmisc_1(sK4,sK4)) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_12]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_34564,plain,
% 35.08/4.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 35.08/4.99      | ~ r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)),sK4)
% 35.08/4.99      | ~ v1_xboole_0(k2_zfmisc_1(sK4,sK4)) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_2701]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_34565,plain,
% 35.08/4.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/4.99      | r2_hidden(sK2(sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)),sK4) != iProver_top
% 35.08/4.99      | v1_xboole_0(k2_zfmisc_1(sK4,sK4)) != iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_34564]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_34607,plain,
% 35.08/4.99      ( v1_xboole_0(sK4) != iProver_top ),
% 35.08/4.99      inference(global_propositional_subsumption,
% 35.08/4.99                [status(thm)],
% 35.08/4.99                [c_31982,c_63,c_64,c_65,c_66,c_67,c_150,c_206,c_219,
% 35.08/4.99                 c_1698,c_2582,c_2602,c_2650,c_2774,c_2806,c_2908,c_3403,
% 35.08/4.99                 c_4160,c_4165,c_5391,c_6153,c_10049,c_10690,c_17259,
% 35.08/4.99                 c_34565]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_35,plain,
% 35.08/4.99      ( ~ v3_funct_2(X0,X1,X2)
% 35.08/4.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/4.99      | ~ v1_funct_1(X0)
% 35.08/4.99      | v2_funct_1(X0) ),
% 35.08/4.99      inference(cnf_transformation,[],[f131]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_2496,plain,
% 35.08/4.99      ( v3_funct_2(X0,X1,X2) != iProver_top
% 35.08/4.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.08/4.99      | v1_funct_1(X0) != iProver_top
% 35.08/4.99      | v2_funct_1(X0) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_11279,plain,
% 35.08/4.99      ( v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top
% 35.08/4.99      | v2_funct_1(sK5) = iProver_top ),
% 35.08/4.99      inference(superposition,[status(thm)],[c_2478,c_2496]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_9596,plain,
% 35.08/4.99      ( ~ v3_funct_2(sK5,X0,X1)
% 35.08/4.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.08/4.99      | ~ v1_funct_1(sK5)
% 35.08/4.99      | v2_funct_1(sK5) ),
% 35.08/4.99      inference(instantiation,[status(thm)],[c_35]) ).
% 35.08/4.99  
% 35.08/4.99  cnf(c_9597,plain,
% 35.08/4.99      ( v3_funct_2(sK5,X0,X1) != iProver_top
% 35.08/4.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/4.99      | v1_funct_1(sK5) != iProver_top
% 35.08/4.99      | v2_funct_1(sK5) = iProver_top ),
% 35.08/4.99      inference(predicate_to_equality,[status(thm)],[c_9596]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_9599,plain,
% 35.08/5.00      ( v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/5.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top
% 35.08/5.00      | v2_funct_1(sK5) = iProver_top ),
% 35.08/5.00      inference(instantiation,[status(thm)],[c_9597]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_11574,plain,
% 35.08/5.00      ( v2_funct_1(sK5) = iProver_top ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_11279,c_63,c_65,c_66,c_9599]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_31,plain,
% 35.08/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 35.08/5.00      inference(cnf_transformation,[],[f126]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2499,plain,
% 35.08/5.00      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 35.08/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6081,plain,
% 35.08/5.00      ( k7_relset_1(sK4,sK4,sK5,sK4) = k2_relset_1(sK4,sK4,sK5) ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_2478,c_2499]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_27,plain,
% 35.08/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 35.08/5.00      inference(cnf_transformation,[],[f123]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2503,plain,
% 35.08/5.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 35.08/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_5223,plain,
% 35.08/5.00      ( k7_relset_1(sK4,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_2478,c_2503]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6086,plain,
% 35.08/5.00      ( k2_relset_1(sK4,sK4,sK5) = k9_relat_1(sK5,sK4) ),
% 35.08/5.00      inference(demodulation,[status(thm)],[c_6081,c_5223]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_53,plain,
% 35.08/5.00      ( ~ v1_funct_2(X0,X1,X2)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | ~ v1_funct_1(X0)
% 35.08/5.00      | ~ v2_funct_1(X0)
% 35.08/5.00      | k2_relset_1(X1,X2,X0) != X2
% 35.08/5.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 35.08/5.00      | k1_xboole_0 = X2 ),
% 35.08/5.00      inference(cnf_transformation,[],[f151]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2483,plain,
% 35.08/5.00      ( k2_relset_1(X0,X1,X2) != X1
% 35.08/5.00      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 35.08/5.00      | k1_xboole_0 = X1
% 35.08/5.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.08/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/5.00      | v1_funct_1(X2) != iProver_top
% 35.08/5.00      | v2_funct_1(X2) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6505,plain,
% 35.08/5.00      ( k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
% 35.08/5.00      | k9_relat_1(sK5,sK4) != sK4
% 35.08/5.00      | sK4 = k1_xboole_0
% 35.08/5.00      | v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/5.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_6086,c_2483]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_34,plain,
% 35.08/5.00      ( ~ v3_funct_2(X0,X1,X2)
% 35.08/5.00      | v2_funct_2(X0,X2)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | ~ v1_funct_1(X0) ),
% 35.08/5.00      inference(cnf_transformation,[],[f132]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_38,plain,
% 35.08/5.00      ( ~ v2_funct_2(X0,X1)
% 35.08/5.00      | ~ v5_relat_1(X0,X1)
% 35.08/5.00      | ~ v1_relat_1(X0)
% 35.08/5.00      | k2_relat_1(X0) = X1 ),
% 35.08/5.00      inference(cnf_transformation,[],[f133]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_745,plain,
% 35.08/5.00      ( ~ v3_funct_2(X0,X1,X2)
% 35.08/5.00      | ~ v5_relat_1(X3,X4)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | ~ v1_funct_1(X0)
% 35.08/5.00      | ~ v1_relat_1(X3)
% 35.08/5.00      | X3 != X0
% 35.08/5.00      | X4 != X2
% 35.08/5.00      | k2_relat_1(X3) = X4 ),
% 35.08/5.00      inference(resolution_lifted,[status(thm)],[c_34,c_38]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_746,plain,
% 35.08/5.00      ( ~ v3_funct_2(X0,X1,X2)
% 35.08/5.00      | ~ v5_relat_1(X0,X2)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | ~ v1_funct_1(X0)
% 35.08/5.00      | ~ v1_relat_1(X0)
% 35.08/5.00      | k2_relat_1(X0) = X2 ),
% 35.08/5.00      inference(unflattening,[status(thm)],[c_745]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_22,plain,
% 35.08/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | v1_relat_1(X0) ),
% 35.08/5.00      inference(cnf_transformation,[],[f118]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_750,plain,
% 35.08/5.00      ( ~ v1_funct_1(X0)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | ~ v5_relat_1(X0,X2)
% 35.08/5.00      | ~ v3_funct_2(X0,X1,X2)
% 35.08/5.00      | k2_relat_1(X0) = X2 ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_746,c_22]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_751,plain,
% 35.08/5.00      ( ~ v3_funct_2(X0,X1,X2)
% 35.08/5.00      | ~ v5_relat_1(X0,X2)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | ~ v1_funct_1(X0)
% 35.08/5.00      | k2_relat_1(X0) = X2 ),
% 35.08/5.00      inference(renaming,[status(thm)],[c_750]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_23,plain,
% 35.08/5.00      ( v5_relat_1(X0,X1)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 35.08/5.00      inference(cnf_transformation,[],[f120]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_766,plain,
% 35.08/5.00      ( ~ v3_funct_2(X0,X1,X2)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | ~ v1_funct_1(X0)
% 35.08/5.00      | k2_relat_1(X0) = X2 ),
% 35.08/5.00      inference(forward_subsumption_resolution,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_751,c_23]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2472,plain,
% 35.08/5.00      ( k2_relat_1(X0) = X1
% 35.08/5.00      | v3_funct_2(X0,X2,X1) != iProver_top
% 35.08/5.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 35.08/5.00      | v1_funct_1(X0) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_3534,plain,
% 35.08/5.00      ( k2_relat_1(sK5) = sK4
% 35.08/5.00      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_2478,c_2472]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_3748,plain,
% 35.08/5.00      ( k2_relat_1(sK5) = sK4 ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_3534,c_63,c_65]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_56,plain,
% 35.08/5.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 35.08/5.00      | ~ v1_funct_1(X0)
% 35.08/5.00      | ~ v1_relat_1(X0) ),
% 35.08/5.00      inference(cnf_transformation,[],[f153]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2480,plain,
% 35.08/5.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 35.08/5.00      | v1_funct_1(X0) != iProver_top
% 35.08/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_4305,plain,
% 35.08/5.00      ( v1_funct_2(sK5,k1_relat_1(sK5),sK4) = iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top
% 35.08/5.00      | v1_relat_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_3748,c_2480]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2506,plain,
% 35.08/5.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.08/5.00      | v1_relat_1(X0) = iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_4434,plain,
% 35.08/5.00      ( v1_relat_1(sK5) = iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_2478,c_2506]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_55,plain,
% 35.08/5.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 35.08/5.00      | ~ v1_funct_1(X0)
% 35.08/5.00      | ~ v1_relat_1(X0) ),
% 35.08/5.00      inference(cnf_transformation,[],[f154]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2481,plain,
% 35.08/5.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 35.08/5.00      | v1_funct_1(X0) != iProver_top
% 35.08/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_5029,plain,
% 35.08/5.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top
% 35.08/5.00      | v1_relat_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_3748,c_2481]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_5422,plain,
% 35.08/5.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_5029,c_63,c_4434]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6082,plain,
% 35.08/5.00      ( k7_relset_1(k1_relat_1(sK5),sK4,sK5,k1_relat_1(sK5)) = k2_relset_1(k1_relat_1(sK5),sK4,sK5) ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_5422,c_2499]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_17,plain,
% 35.08/5.00      ( ~ v1_relat_1(X0)
% 35.08/5.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 35.08/5.00      inference(cnf_transformation,[],[f113]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2511,plain,
% 35.08/5.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 35.08/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_4735,plain,
% 35.08/5.00      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_4434,c_2511]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_4736,plain,
% 35.08/5.00      ( k9_relat_1(sK5,k1_relat_1(sK5)) = sK4 ),
% 35.08/5.00      inference(light_normalisation,[status(thm)],[c_4735,c_3748]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_5429,plain,
% 35.08/5.00      ( k7_relset_1(k1_relat_1(sK5),sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_5422,c_2503]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6085,plain,
% 35.08/5.00      ( k2_relset_1(k1_relat_1(sK5),sK4,sK5) = sK4 ),
% 35.08/5.00      inference(demodulation,[status(thm)],[c_6082,c_4736,c_5429]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6511,plain,
% 35.08/5.00      ( k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
% 35.08/5.00      | sK4 = k1_xboole_0
% 35.08/5.00      | v1_funct_2(sK5,k1_relat_1(sK5),sK4) != iProver_top
% 35.08/5.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) != iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_6085,c_2483]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6567,plain,
% 35.08/5.00      ( sK4 = k1_xboole_0
% 35.08/5.00      | k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_6505,c_63,c_4305,c_4434,c_5029,c_6511]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6568,plain,
% 35.08/5.00      ( k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
% 35.08/5.00      | sK4 = k1_xboole_0
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(renaming,[status(thm)],[c_6567]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_11581,plain,
% 35.08/5.00      ( k5_relat_1(k2_funct_1(sK5),sK5) = k6_partfun1(sK4)
% 35.08/5.00      | sK4 = k1_xboole_0 ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_11574,c_6568]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_7262,plain,
% 35.08/5.00      ( k1_partfun1(X0,X1,sK4,sK4,X2,sK5) = k5_relat_1(X2,sK5)
% 35.08/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/5.00      | v1_funct_1(X2) != iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_2478,c_2485]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_7742,plain,
% 35.08/5.00      ( v1_funct_1(X2) != iProver_top
% 35.08/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/5.00      | k1_partfun1(X0,X1,sK4,sK4,X2,sK5) = k5_relat_1(X2,sK5) ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_7262,c_63]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_7743,plain,
% 35.08/5.00      ( k1_partfun1(X0,X1,sK4,sK4,X2,sK5) = k5_relat_1(X2,sK5)
% 35.08/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/5.00      | v1_funct_1(X2) != iProver_top ),
% 35.08/5.00      inference(renaming,[status(thm)],[c_7742]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_11736,plain,
% 35.08/5.00      ( k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_1(sK5),sK5) = k5_relat_1(k2_funct_1(sK5),sK5)
% 35.08/5.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_11723,c_7743]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_11771,plain,
% 35.08/5.00      ( k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_1(sK5),sK5) = k5_relat_1(k2_funct_1(sK5),sK5) ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_11736,c_63,c_64,c_65,c_7993]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2479,plain,
% 35.08/5.00      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_2(sK4,sK5),sK5),k6_partfun1(sK4)) != iProver_top
% 35.08/5.00      | r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_2(sK4,sK5)),k6_partfun1(sK4)) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6867,plain,
% 35.08/5.00      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,k2_funct_1(sK5),sK5),k6_partfun1(sK4)) != iProver_top
% 35.08/5.00      | r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) != iProver_top ),
% 35.08/5.00      inference(demodulation,[status(thm)],[c_6865,c_2479]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_11773,plain,
% 35.08/5.00      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK4,sK4,sK4,sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) != iProver_top
% 35.08/5.00      | r2_relset_1(sK4,sK4,k5_relat_1(k2_funct_1(sK5),sK5),k6_partfun1(sK4)) != iProver_top ),
% 35.08/5.00      inference(demodulation,[status(thm)],[c_11771,c_6867]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_20761,plain,
% 35.08/5.00      ( r2_relset_1(sK4,sK4,k5_relat_1(k2_funct_1(sK5),sK5),k6_partfun1(sK4)) != iProver_top
% 35.08/5.00      | r2_relset_1(sK4,sK4,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) != iProver_top ),
% 35.08/5.00      inference(demodulation,[status(thm)],[c_20759,c_11773]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_20779,plain,
% 35.08/5.00      ( sK4 = k1_xboole_0
% 35.08/5.00      | r2_relset_1(sK4,sK4,k5_relat_1(sK5,k2_funct_1(sK5)),k6_partfun1(sK4)) != iProver_top
% 35.08/5.00      | r2_relset_1(sK4,sK4,k6_partfun1(sK4),k6_partfun1(sK4)) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_11581,c_20761]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_11733,plain,
% 35.08/5.00      ( k2_relat_1(k2_funct_1(sK5)) = sK4
% 35.08/5.00      | v3_funct_2(k2_funct_1(sK5),sK4,sK4) != iProver_top
% 35.08/5.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_11723,c_2472]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2475,plain,
% 35.08/5.00      ( v1_funct_1(sK5) = iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_20,plain,
% 35.08/5.00      ( ~ v1_funct_1(X0)
% 35.08/5.00      | ~ v2_funct_1(X0)
% 35.08/5.00      | ~ v1_relat_1(X0)
% 35.08/5.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 35.08/5.00      inference(cnf_transformation,[],[f117]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2508,plain,
% 35.08/5.00      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 35.08/5.00      | v1_funct_1(X0) != iProver_top
% 35.08/5.00      | v2_funct_1(X0) != iProver_top
% 35.08/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_8249,plain,
% 35.08/5.00      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top
% 35.08/5.00      | v1_relat_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_2475,c_2508]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_8330,plain,
% 35.08/5.00      ( v2_funct_1(sK5) != iProver_top
% 35.08/5.00      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_8249,c_4434]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_8331,plain,
% 35.08/5.00      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(renaming,[status(thm)],[c_8330]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_11579,plain,
% 35.08/5.00      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_11574,c_8331]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_11746,plain,
% 35.08/5.00      ( k1_relat_1(sK5) = sK4
% 35.08/5.00      | v3_funct_2(k2_funct_1(sK5),sK4,sK4) != iProver_top
% 35.08/5.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 35.08/5.00      inference(demodulation,[status(thm)],[c_11733,c_11579]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_42,plain,
% 35.08/5.00      ( ~ v1_funct_2(X0,X1,X1)
% 35.08/5.00      | ~ v3_funct_2(X0,X1,X1)
% 35.08/5.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 35.08/5.00      | ~ v1_funct_1(X0) ),
% 35.08/5.00      inference(cnf_transformation,[],[f139]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2492,plain,
% 35.08/5.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 35.08/5.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 35.08/5.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 35.08/5.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 35.08/5.00      | v1_funct_1(X0) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_10485,plain,
% 35.08/5.00      ( v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/5.00      | v3_funct_2(k2_funct_2(sK4,sK5),sK4,sK4) = iProver_top
% 35.08/5.00      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_2478,c_2492]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_10488,plain,
% 35.08/5.00      ( v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/5.00      | v3_funct_2(k2_funct_1(sK5),sK4,sK4) = iProver_top
% 35.08/5.00      | v3_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(light_normalisation,[status(thm)],[c_10485,c_6865]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_16985,plain,
% 35.08/5.00      ( k1_relat_1(sK5) = sK4 ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_11746,c_63,c_64,c_65,c_7993,c_10488]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_17006,plain,
% 35.08/5.00      ( k9_relat_1(sK5,sK4) = sK4 ),
% 35.08/5.00      inference(demodulation,[status(thm)],[c_16985,c_4736]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_54,plain,
% 35.08/5.00      ( ~ v1_funct_2(X0,X1,X2)
% 35.08/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.08/5.00      | ~ v1_funct_1(X0)
% 35.08/5.00      | ~ v2_funct_1(X0)
% 35.08/5.00      | k2_relset_1(X1,X2,X0) != X2
% 35.08/5.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 35.08/5.00      | k1_xboole_0 = X2 ),
% 35.08/5.00      inference(cnf_transformation,[],[f150]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_2482,plain,
% 35.08/5.00      ( k2_relset_1(X0,X1,X2) != X1
% 35.08/5.00      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 35.08/5.00      | k1_xboole_0 = X1
% 35.08/5.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.08/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.08/5.00      | v1_funct_1(X2) != iProver_top
% 35.08/5.00      | v2_funct_1(X2) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6506,plain,
% 35.08/5.00      ( k5_relat_1(sK5,k2_funct_1(sK5)) = k6_partfun1(sK4)
% 35.08/5.00      | k9_relat_1(sK5,sK4) != sK4
% 35.08/5.00      | sK4 = k1_xboole_0
% 35.08/5.00      | v1_funct_2(sK5,sK4,sK4) != iProver_top
% 35.08/5.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top
% 35.08/5.00      | v1_funct_1(sK5) != iProver_top
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(superposition,[status(thm)],[c_6086,c_2482]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6572,plain,
% 35.08/5.00      ( sK4 = k1_xboole_0
% 35.08/5.00      | k9_relat_1(sK5,sK4) != sK4
% 35.08/5.00      | k5_relat_1(sK5,k2_funct_1(sK5)) = k6_partfun1(sK4)
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(global_propositional_subsumption,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_6506,c_63,c_64,c_66]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_6573,plain,
% 35.08/5.00      ( k5_relat_1(sK5,k2_funct_1(sK5)) = k6_partfun1(sK4)
% 35.08/5.00      | k9_relat_1(sK5,sK4) != sK4
% 35.08/5.00      | sK4 = k1_xboole_0
% 35.08/5.00      | v2_funct_1(sK5) != iProver_top ),
% 35.08/5.00      inference(renaming,[status(thm)],[c_6572]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_3287,plain,
% 35.08/5.00      ( X0 != k1_xboole_0
% 35.08/5.00      | v1_xboole_0(X0) = iProver_top
% 35.08/5.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.08/5.00      inference(predicate_to_equality,[status(thm)],[c_3286]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_3289,plain,
% 35.08/5.00      ( sK4 != k1_xboole_0
% 35.08/5.00      | v1_xboole_0(sK4) = iProver_top
% 35.08/5.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.08/5.00      inference(instantiation,[status(thm)],[c_3287]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_1670,plain,
% 35.08/5.00      ( X0 != X1 | k6_partfun1(X0) = k6_partfun1(X1) ),
% 35.08/5.00      theory(equality) ).
% 35.08/5.00  
% 35.08/5.00  cnf(c_1689,plain,
% 35.08/5.00      ( k6_partfun1(sK4) = k6_partfun1(sK4) | sK4 != sK4 ),
% 35.08/5.00      inference(instantiation,[status(thm)],[c_1670]) ).
% 35.08/5.00  
% 35.08/5.00  cnf(contradiction,plain,
% 35.08/5.00      ( $false ),
% 35.08/5.00      inference(minisat,
% 35.08/5.00                [status(thm)],
% 35.08/5.00                [c_104675,c_84767,c_34607,c_20779,c_17006,c_9599,c_6573,
% 35.08/5.00                 c_3289,c_1698,c_1689,c_219,c_66,c_65,c_63]) ).
% 35.08/5.00  
% 35.08/5.00  
% 35.08/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.08/5.00  
% 35.08/5.00  ------                               Statistics
% 35.08/5.00  
% 35.08/5.00  ------ General
% 35.08/5.00  
% 35.08/5.00  abstr_ref_over_cycles:                  0
% 35.08/5.00  abstr_ref_under_cycles:                 0
% 35.08/5.00  gc_basic_clause_elim:                   0
% 35.08/5.00  forced_gc_time:                         0
% 35.08/5.00  parsing_time:                           0.009
% 35.08/5.00  unif_index_cands_time:                  0.
% 35.08/5.00  unif_index_add_time:                    0.
% 35.08/5.00  orderings_time:                         0.
% 35.08/5.00  out_proof_time:                         0.038
% 35.08/5.00  total_time:                             4.212
% 35.08/5.00  num_of_symbols:                         67
% 35.08/5.00  num_of_terms:                           135852
% 35.08/5.00  
% 35.08/5.00  ------ Preprocessing
% 35.08/5.00  
% 35.08/5.00  num_of_splits:                          0
% 35.08/5.00  num_of_split_atoms:                     0
% 35.08/5.00  num_of_reused_defs:                     0
% 35.08/5.00  num_eq_ax_congr_red:                    80
% 35.08/5.00  num_of_sem_filtered_clauses:            1
% 35.08/5.00  num_of_subtypes:                        0
% 35.08/5.00  monotx_restored_types:                  0
% 35.08/5.00  sat_num_of_epr_types:                   0
% 35.08/5.00  sat_num_of_non_cyclic_types:            0
% 35.08/5.00  sat_guarded_non_collapsed_types:        0
% 35.08/5.00  num_pure_diseq_elim:                    0
% 35.08/5.00  simp_replaced_by:                       0
% 35.08/5.00  res_preprocessed:                       263
% 35.08/5.00  prep_upred:                             0
% 35.08/5.00  prep_unflattend:                        48
% 35.08/5.00  smt_new_axioms:                         0
% 35.08/5.00  pred_elim_cands:                        9
% 35.08/5.00  pred_elim:                              5
% 35.08/5.00  pred_elim_cl:                           8
% 35.08/5.00  pred_elim_cycles:                       9
% 35.08/5.00  merged_defs:                            0
% 35.08/5.00  merged_defs_ncl:                        0
% 35.08/5.00  bin_hyper_res:                          0
% 35.08/5.00  prep_cycles:                            4
% 35.08/5.00  pred_elim_time:                         0.009
% 35.08/5.00  splitting_time:                         0.
% 35.08/5.00  sem_filter_time:                        0.
% 35.08/5.00  monotx_time:                            0.
% 35.08/5.00  subtype_inf_time:                       0.
% 35.08/5.00  
% 35.08/5.00  ------ Problem properties
% 35.08/5.00  
% 35.08/5.00  clauses:                                53
% 35.08/5.00  conjectures:                            5
% 35.08/5.00  epr:                                    6
% 35.08/5.00  horn:                                   47
% 35.08/5.00  ground:                                 6
% 35.08/5.00  unary:                                  15
% 35.08/5.00  binary:                                 11
% 35.08/5.00  lits:                                   148
% 35.08/5.00  lits_eq:                                27
% 35.08/5.00  fd_pure:                                0
% 35.08/5.00  fd_pseudo:                              0
% 35.08/5.00  fd_cond:                                6
% 35.08/5.00  fd_pseudo_cond:                         2
% 35.08/5.00  ac_symbols:                             0
% 35.08/5.00  
% 35.08/5.00  ------ Propositional Solver
% 35.08/5.00  
% 35.08/5.00  prop_solver_calls:                      52
% 35.08/5.00  prop_fast_solver_calls:                 5969
% 35.08/5.00  smt_solver_calls:                       0
% 35.08/5.00  smt_fast_solver_calls:                  0
% 35.08/5.00  prop_num_of_clauses:                    51573
% 35.08/5.00  prop_preprocess_simplified:             87604
% 35.08/5.00  prop_fo_subsumed:                       644
% 35.08/5.00  prop_solver_time:                       0.
% 35.08/5.00  smt_solver_time:                        0.
% 35.08/5.00  smt_fast_solver_time:                   0.
% 35.08/5.00  prop_fast_solver_time:                  0.
% 35.08/5.00  prop_unsat_core_time:                   0.007
% 35.08/5.00  
% 35.08/5.00  ------ QBF
% 35.08/5.00  
% 35.08/5.00  qbf_q_res:                              0
% 35.08/5.00  qbf_num_tautologies:                    0
% 35.08/5.00  qbf_prep_cycles:                        0
% 35.08/5.00  
% 35.08/5.00  ------ BMC1
% 35.08/5.00  
% 35.08/5.00  bmc1_current_bound:                     -1
% 35.08/5.00  bmc1_last_solved_bound:                 -1
% 35.08/5.00  bmc1_unsat_core_size:                   -1
% 35.08/5.00  bmc1_unsat_core_parents_size:           -1
% 35.08/5.00  bmc1_merge_next_fun:                    0
% 35.08/5.00  bmc1_unsat_core_clauses_time:           0.
% 35.08/5.00  
% 35.08/5.00  ------ Instantiation
% 35.08/5.00  
% 35.08/5.00  inst_num_of_clauses:                    6182
% 35.08/5.00  inst_num_in_passive:                    1641
% 35.08/5.00  inst_num_in_active:                     4753
% 35.08/5.00  inst_num_in_unprocessed:                1846
% 35.08/5.00  inst_num_of_loops:                      5829
% 35.08/5.00  inst_num_of_learning_restarts:          1
% 35.08/5.00  inst_num_moves_active_passive:          1070
% 35.08/5.00  inst_lit_activity:                      0
% 35.08/5.00  inst_lit_activity_moves:                1
% 35.08/5.00  inst_num_tautologies:                   0
% 35.08/5.00  inst_num_prop_implied:                  0
% 35.08/5.00  inst_num_existing_simplified:           0
% 35.08/5.00  inst_num_eq_res_simplified:             0
% 35.08/5.00  inst_num_child_elim:                    0
% 35.08/5.00  inst_num_of_dismatching_blockings:      9725
% 35.08/5.00  inst_num_of_non_proper_insts:           14355
% 35.08/5.00  inst_num_of_duplicates:                 0
% 35.08/5.00  inst_inst_num_from_inst_to_res:         0
% 35.08/5.00  inst_dismatching_checking_time:         0.
% 35.08/5.00  
% 35.08/5.00  ------ Resolution
% 35.08/5.00  
% 35.08/5.00  res_num_of_clauses:                     74
% 35.08/5.00  res_num_in_passive:                     74
% 35.08/5.00  res_num_in_active:                      0
% 35.08/5.00  res_num_of_loops:                       267
% 35.08/5.00  res_forward_subset_subsumed:            586
% 35.08/5.00  res_backward_subset_subsumed:           8
% 35.08/5.00  res_forward_subsumed:                   0
% 35.08/5.00  res_backward_subsumed:                  0
% 35.08/5.00  res_forward_subsumption_resolution:     3
% 35.08/5.00  res_backward_subsumption_resolution:    0
% 35.08/5.00  res_clause_to_clause_subsumption:       37801
% 35.08/5.00  res_orphan_elimination:                 0
% 35.08/5.00  res_tautology_del:                      906
% 35.08/5.00  res_num_eq_res_simplified:              0
% 35.08/5.00  res_num_sel_changes:                    0
% 35.08/5.00  res_moves_from_active_to_pass:          0
% 35.08/5.00  
% 35.08/5.00  ------ Superposition
% 35.08/5.00  
% 35.08/5.00  sup_time_total:                         0.
% 35.08/5.00  sup_time_generating:                    0.
% 35.08/5.00  sup_time_sim_full:                      0.
% 35.08/5.00  sup_time_sim_immed:                     0.
% 35.08/5.00  
% 35.08/5.00  sup_num_of_clauses:                     5515
% 35.08/5.00  sup_num_in_active:                      978
% 35.08/5.00  sup_num_in_passive:                     4537
% 35.08/5.00  sup_num_of_loops:                       1165
% 35.08/5.00  sup_fw_superposition:                   4490
% 35.08/5.00  sup_bw_superposition:                   2589
% 35.08/5.00  sup_immediate_simplified:               3061
% 35.08/5.00  sup_given_eliminated:                   28
% 35.08/5.00  comparisons_done:                       0
% 35.08/5.00  comparisons_avoided:                    12
% 35.08/5.00  
% 35.08/5.00  ------ Simplifications
% 35.08/5.00  
% 35.08/5.00  
% 35.08/5.00  sim_fw_subset_subsumed:                 199
% 35.08/5.00  sim_bw_subset_subsumed:                 329
% 35.08/5.00  sim_fw_subsumed:                        224
% 35.08/5.00  sim_bw_subsumed:                        78
% 35.08/5.00  sim_fw_subsumption_res:                 0
% 35.08/5.00  sim_bw_subsumption_res:                 0
% 35.08/5.00  sim_tautology_del:                      6
% 35.08/5.00  sim_eq_tautology_del:                   285
% 35.08/5.00  sim_eq_res_simp:                        1
% 35.08/5.00  sim_fw_demodulated:                     2198
% 35.08/5.00  sim_bw_demodulated:                     457
% 35.08/5.00  sim_light_normalised:                   519
% 35.08/5.00  sim_joinable_taut:                      0
% 35.08/5.00  sim_joinable_simp:                      0
% 35.08/5.00  sim_ac_normalised:                      0
% 35.08/5.00  sim_smt_subsumption:                    0
% 35.08/5.00  
%------------------------------------------------------------------------------
