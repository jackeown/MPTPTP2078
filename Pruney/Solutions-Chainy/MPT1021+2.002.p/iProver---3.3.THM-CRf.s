%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:17 EST 2020

% Result     : Theorem 6.70s
% Output     : CNFRefutation 6.70s
% Verified   : 
% Statistics : Number of formulae       :  281 (4721 expanded)
%              Number of clauses        :  170 (1448 expanded)
%              Number of leaves         :   30 ( 919 expanded)
%              Depth                    :   27
%              Number of atoms          :  836 (21679 expanded)
%              Number of equality atoms :  374 (2445 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f48])).

fof(f104,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f105,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f104])).

fof(f123,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
        | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v3_funct_2(sK4,sK3,sK3)
      & v1_funct_2(sK4,sK3,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f124,plain,
    ( ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
      | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v3_funct_2(sK4,sK3,sK3)
    & v1_funct_2(sK4,sK3,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f105,f123])).

fof(f205,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f124])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f75])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f156,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f90])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f94])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f95])).

fof(f190,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f202,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f124])).

fof(f204,plain,(
    v3_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f124])).

fof(f34,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f47,axiom,(
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

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f102])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f203,plain,(
    v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f124])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f79])).

fof(f164,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f46,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f199,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f46])).

fof(f212,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f164,f199])).

fof(f45,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f100])).

fof(f198,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f42,axiom,(
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

fof(f96,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f96])).

fof(f195,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f44,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f99,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f98])).

fof(f197,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f192,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f165,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f211,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f165,f199])).

fof(f206,plain,
    ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
    | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) ),
    inference(cnf_transformation,[],[f124])).

fof(f43,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f43])).

fof(f196,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f35,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f86])).

fof(f120,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f87])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f217,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f175])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f77])).

fof(f159,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f131,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f151,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f132,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f142,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f36,axiom,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f176,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f214,plain,(
    ! [X0] : r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(definition_unfolding,[],[f176,f199])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f138,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f57])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f147,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f116])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f117])).

fof(f216,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f135])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_77,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f205])).

cnf(c_4051,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_53,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f177])).

cnf(c_4071,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_12678,plain,
    ( k7_relset_1(sK3,sK3,sK4,sK3) = k2_relset_1(sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_4051,c_4071])).

cnf(c_47,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_32,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f157])).

cnf(c_1007,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_47,c_32])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f170])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_47,c_45,c_32])).

cnf(c_4044,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_6522,plain,
    ( k7_relat_1(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_4051,c_4044])).

cnf(c_4077,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_6198,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_4077])).

cnf(c_31,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_4087,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6730,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_6198,c_4087])).

cnf(c_7358,plain,
    ( k9_relat_1(sK4,sK3) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_6522,c_6730])).

cnf(c_56,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f183])).

cnf(c_66,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f190])).

cnf(c_1057,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_56,c_66])).

cnf(c_1058,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_1057])).

cnf(c_1062,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1058,c_45])).

cnf(c_1063,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_1062])).

cnf(c_46,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_1078,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1063,c_46])).

cnf(c_4043,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_5899,plain,
    ( k2_relat_1(sK4) = sK3
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_4043])).

cnf(c_80,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f202])).

cnf(c_78,negated_conjecture,
    ( v3_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f204])).

cnf(c_4733,plain,
    ( ~ v3_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_relat_1(sK4) = X1 ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_4990,plain,
    ( ~ v3_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_relat_1(sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_4733])).

cnf(c_6321,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5899,c_80,c_78,c_77,c_4990])).

cnf(c_7365,plain,
    ( k9_relat_1(sK4,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_7358,c_6321])).

cnf(c_48,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f173])).

cnf(c_4076,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_12095,plain,
    ( k7_relset_1(sK3,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_4051,c_4076])).

cnf(c_12685,plain,
    ( k2_relset_1(sK3,sK3,sK4) = sK3 ),
    inference(demodulation,[status(thm)],[c_12678,c_7365,c_12095])).

cnf(c_75,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f200])).

cnf(c_4053,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_12733,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK3,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12685,c_4053])).

cnf(c_79,negated_conjecture,
    ( v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f203])).

cnf(c_57,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f182])).

cnf(c_4707,plain,
    ( ~ v3_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_4987,plain,
    ( ~ v3_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4707])).

cnf(c_12759,plain,
    ( ~ v1_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12733])).

cnf(c_14200,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12733,c_80,c_79,c_78,c_77,c_4987,c_12759])).

cnf(c_4068,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_14939,plain,
    ( v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_4068])).

cnf(c_81,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_83,plain,
    ( v3_funct_2(sK4,sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_84,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_4988,plain,
    ( v3_funct_2(sK4,sK3,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4987])).

cnf(c_15261,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14939,c_81,c_83,c_84,c_4988])).

cnf(c_40,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f212])).

cnf(c_4081,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_15267,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_15261,c_4081])).

cnf(c_4646,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_5256,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_15370,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15267,c_80,c_78,c_77,c_4646,c_4987,c_5256])).

cnf(c_15373,plain,
    ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14200,c_15370])).

cnf(c_73,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f198])).

cnf(c_4055,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_10648,plain,
    ( k2_funct_2(sK3,sK4) = k2_funct_1(sK4)
    | v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_4055])).

cnf(c_4801,plain,
    ( ~ v1_funct_2(sK4,X0,X0)
    | ~ v3_funct_2(sK4,X0,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK4)
    | k2_funct_2(X0,sK4) = k2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_5086,plain,
    ( ~ v1_funct_2(sK4,sK3,sK3)
    | ~ v3_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_funct_2(sK3,sK4) = k2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4801])).

cnf(c_11139,plain,
    ( k2_funct_2(sK3,sK4) = k2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10648,c_80,c_79,c_78,c_77,c_5086])).

cnf(c_67,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f195])).

cnf(c_4061,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_14464,plain,
    ( v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11139,c_4061])).

cnf(c_82,plain,
    ( v1_funct_2(sK4,sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_15464,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14464,c_81,c_82,c_83,c_84])).

cnf(c_72,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f197])).

cnf(c_4056,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_15487,plain,
    ( k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15464,c_4056])).

cnf(c_70,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f192])).

cnf(c_4058,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_12515,plain,
    ( v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(k2_funct_2(sK3,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_4058])).

cnf(c_12531,plain,
    ( v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12515,c_11139])).

cnf(c_19704,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15487,c_81,c_82,c_83,c_12531])).

cnf(c_19705,plain,
    ( k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_19704])).

cnf(c_19716,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k5_relat_1(sK4,k2_funct_1(sK4))
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_19705])).

cnf(c_19731,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19716,c_15370])).

cnf(c_19771,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19731,c_81])).

cnf(c_11917,plain,
    ( k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_4056])).

cnf(c_12185,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11917,c_81])).

cnf(c_12186,plain,
    ( k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_12185])).

cnf(c_14475,plain,
    ( k1_partfun1(X0,X0,sK3,sK3,k2_funct_2(X0,X1),sK4) = k5_relat_1(k2_funct_2(X0,X1),sK4)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4061,c_12186])).

cnf(c_15597,plain,
    ( k1_partfun1(X0,X0,sK3,sK3,k2_funct_2(X0,X1),sK4) = k5_relat_1(k2_funct_2(X0,X1),sK4)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14475,c_4058])).

cnf(c_15604,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4) = k5_relat_1(k2_funct_2(sK3,sK4),sK4)
    | v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_15597])).

cnf(c_39,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f211])).

cnf(c_4082,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_15266,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(k2_relat_1(sK4))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_15261,c_4082])).

cnf(c_15277,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15266,c_6321])).

cnf(c_4647,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4646])).

cnf(c_15366,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15277,c_81,c_84,c_4647])).

cnf(c_15629,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
    | v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15604,c_11139,c_15366])).

cnf(c_15480,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k5_relat_1(k2_funct_1(sK4),sK4)
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15464,c_12186])).

cnf(c_15534,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15480,c_15366])).

cnf(c_15907,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15629,c_81,c_82,c_83,c_12531,c_15534])).

cnf(c_76,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
    | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) ),
    inference(cnf_transformation,[],[f206])).

cnf(c_4052,plain,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) != iProver_top
    | r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_11142,plain,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4),k6_partfun1(sK3)) != iProver_top
    | r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11139,c_4052])).

cnf(c_15910,plain,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top
    | r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15907,c_11142])).

cnf(c_19774,plain,
    ( r2_relset_1(sK3,sK3,k6_partfun1(k1_relat_1(sK4)),k6_partfun1(sK3)) != iProver_top
    | r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19771,c_15910])).

cnf(c_71,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f196])).

cnf(c_4057,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_49,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f217])).

cnf(c_4075,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_10946,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4057,c_4075])).

cnf(c_20046,plain,
    ( r2_relset_1(sK3,sK3,k6_partfun1(k1_relat_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19774,c_10946])).

cnf(c_20278,plain,
    ( sK3 = k1_xboole_0
    | r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15373,c_20046])).

cnf(c_22731,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20278,c_10946])).

cnf(c_22748,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK4)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22731,c_20046])).

cnf(c_33,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f159])).

cnf(c_4086,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8216,plain,
    ( sK4 = k1_xboole_0
    | sK3 != k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6321,c_4086])).

cnf(c_8230,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8216])).

cnf(c_8665,plain,
    ( sK3 != k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8216,c_77,c_4646,c_8230])).

cnf(c_8666,plain,
    ( sK4 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8665])).

cnf(c_22811,plain,
    ( sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22731,c_8666])).

cnf(c_22836,plain,
    ( sK4 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_22811])).

cnf(c_23126,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22748,c_22836])).

cnf(c_6,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_4104,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_4092,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_4103,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4953,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4092,c_4103])).

cnf(c_5301,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4104,c_4953])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_4097,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5111,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4097,c_4103])).

cnf(c_5690,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4104,c_5111])).

cnf(c_51,plain,
    ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(cnf_transformation,[],[f214])).

cnf(c_4073,plain,
    ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_5722,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5690,c_4073])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_994,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_995,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_4045,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_995])).

cnf(c_6353,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5722,c_4045])).

cnf(c_6418,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6353,c_4103])).

cnf(c_23128,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23126,c_5301,c_6418])).

cnf(c_2554,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5184,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_2554])).

cnf(c_5185,plain,
    ( X0 != X1
    | k2_zfmisc_1(X2,X3) != X4
    | r1_tarski(X1,X4) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5184])).

cnf(c_5187,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5185])).

cnf(c_5124,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5111])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_4640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4640])).

cnf(c_4643,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4641])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f216])).

cnf(c_263,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_265,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_264,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_260,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_262,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_261,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_257,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_259,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_258,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_252,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_162,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_164,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23128,c_5187,c_5124,c_4643,c_265,c_264,c_262,c_261,c_259,c_258,c_252,c_164])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:26:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.70/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/1.47  
% 6.70/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.70/1.47  
% 6.70/1.47  ------  iProver source info
% 6.70/1.47  
% 6.70/1.47  git: date: 2020-06-30 10:37:57 +0100
% 6.70/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.70/1.47  git: non_committed_changes: false
% 6.70/1.47  git: last_make_outside_of_git: false
% 6.70/1.47  
% 6.70/1.47  ------ 
% 6.70/1.47  
% 6.70/1.47  ------ Input Options
% 6.70/1.47  
% 6.70/1.47  --out_options                           all
% 6.70/1.47  --tptp_safe_out                         true
% 6.70/1.47  --problem_path                          ""
% 6.70/1.47  --include_path                          ""
% 6.70/1.47  --clausifier                            res/vclausify_rel
% 6.70/1.47  --clausifier_options                    --mode clausify
% 6.70/1.47  --stdin                                 false
% 6.70/1.47  --stats_out                             all
% 6.70/1.47  
% 6.70/1.47  ------ General Options
% 6.70/1.47  
% 6.70/1.47  --fof                                   false
% 6.70/1.47  --time_out_real                         305.
% 6.70/1.47  --time_out_virtual                      -1.
% 6.70/1.47  --symbol_type_check                     false
% 6.70/1.47  --clausify_out                          false
% 6.70/1.47  --sig_cnt_out                           false
% 6.70/1.47  --trig_cnt_out                          false
% 6.70/1.47  --trig_cnt_out_tolerance                1.
% 6.70/1.47  --trig_cnt_out_sk_spl                   false
% 6.70/1.47  --abstr_cl_out                          false
% 6.70/1.47  
% 6.70/1.47  ------ Global Options
% 6.70/1.47  
% 6.70/1.47  --schedule                              default
% 6.70/1.47  --add_important_lit                     false
% 6.70/1.47  --prop_solver_per_cl                    1000
% 6.70/1.47  --min_unsat_core                        false
% 6.70/1.47  --soft_assumptions                      false
% 6.70/1.47  --soft_lemma_size                       3
% 6.70/1.47  --prop_impl_unit_size                   0
% 6.70/1.47  --prop_impl_unit                        []
% 6.70/1.47  --share_sel_clauses                     true
% 6.70/1.47  --reset_solvers                         false
% 6.70/1.47  --bc_imp_inh                            [conj_cone]
% 6.70/1.47  --conj_cone_tolerance                   3.
% 6.70/1.47  --extra_neg_conj                        none
% 6.70/1.47  --large_theory_mode                     true
% 6.70/1.47  --prolific_symb_bound                   200
% 6.70/1.47  --lt_threshold                          2000
% 6.70/1.47  --clause_weak_htbl                      true
% 6.70/1.47  --gc_record_bc_elim                     false
% 6.70/1.47  
% 6.70/1.47  ------ Preprocessing Options
% 6.70/1.47  
% 6.70/1.47  --preprocessing_flag                    true
% 6.70/1.47  --time_out_prep_mult                    0.1
% 6.70/1.47  --splitting_mode                        input
% 6.70/1.47  --splitting_grd                         true
% 6.70/1.47  --splitting_cvd                         false
% 6.70/1.47  --splitting_cvd_svl                     false
% 6.70/1.47  --splitting_nvd                         32
% 6.70/1.47  --sub_typing                            true
% 6.70/1.47  --prep_gs_sim                           true
% 6.70/1.47  --prep_unflatten                        true
% 6.70/1.47  --prep_res_sim                          true
% 6.70/1.47  --prep_upred                            true
% 6.70/1.47  --prep_sem_filter                       exhaustive
% 6.70/1.47  --prep_sem_filter_out                   false
% 6.70/1.47  --pred_elim                             true
% 6.70/1.47  --res_sim_input                         true
% 6.70/1.47  --eq_ax_congr_red                       true
% 6.70/1.47  --pure_diseq_elim                       true
% 6.70/1.47  --brand_transform                       false
% 6.70/1.47  --non_eq_to_eq                          false
% 6.70/1.47  --prep_def_merge                        true
% 6.70/1.47  --prep_def_merge_prop_impl              false
% 6.70/1.48  --prep_def_merge_mbd                    true
% 6.70/1.48  --prep_def_merge_tr_red                 false
% 6.70/1.48  --prep_def_merge_tr_cl                  false
% 6.70/1.48  --smt_preprocessing                     true
% 6.70/1.48  --smt_ac_axioms                         fast
% 6.70/1.48  --preprocessed_out                      false
% 6.70/1.48  --preprocessed_stats                    false
% 6.70/1.48  
% 6.70/1.48  ------ Abstraction refinement Options
% 6.70/1.48  
% 6.70/1.48  --abstr_ref                             []
% 6.70/1.48  --abstr_ref_prep                        false
% 6.70/1.48  --abstr_ref_until_sat                   false
% 6.70/1.48  --abstr_ref_sig_restrict                funpre
% 6.70/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.70/1.48  --abstr_ref_under                       []
% 6.70/1.48  
% 6.70/1.48  ------ SAT Options
% 6.70/1.48  
% 6.70/1.48  --sat_mode                              false
% 6.70/1.48  --sat_fm_restart_options                ""
% 6.70/1.48  --sat_gr_def                            false
% 6.70/1.48  --sat_epr_types                         true
% 6.70/1.48  --sat_non_cyclic_types                  false
% 6.70/1.48  --sat_finite_models                     false
% 6.70/1.48  --sat_fm_lemmas                         false
% 6.70/1.48  --sat_fm_prep                           false
% 6.70/1.48  --sat_fm_uc_incr                        true
% 6.70/1.48  --sat_out_model                         small
% 6.70/1.48  --sat_out_clauses                       false
% 6.70/1.48  
% 6.70/1.48  ------ QBF Options
% 6.70/1.48  
% 6.70/1.48  --qbf_mode                              false
% 6.70/1.48  --qbf_elim_univ                         false
% 6.70/1.48  --qbf_dom_inst                          none
% 6.70/1.48  --qbf_dom_pre_inst                      false
% 6.70/1.48  --qbf_sk_in                             false
% 6.70/1.48  --qbf_pred_elim                         true
% 6.70/1.48  --qbf_split                             512
% 6.70/1.48  
% 6.70/1.48  ------ BMC1 Options
% 6.70/1.48  
% 6.70/1.48  --bmc1_incremental                      false
% 6.70/1.48  --bmc1_axioms                           reachable_all
% 6.70/1.48  --bmc1_min_bound                        0
% 6.70/1.48  --bmc1_max_bound                        -1
% 6.70/1.48  --bmc1_max_bound_default                -1
% 6.70/1.48  --bmc1_symbol_reachability              true
% 6.70/1.48  --bmc1_property_lemmas                  false
% 6.70/1.48  --bmc1_k_induction                      false
% 6.70/1.48  --bmc1_non_equiv_states                 false
% 6.70/1.48  --bmc1_deadlock                         false
% 6.70/1.48  --bmc1_ucm                              false
% 6.70/1.48  --bmc1_add_unsat_core                   none
% 6.70/1.48  --bmc1_unsat_core_children              false
% 6.70/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.70/1.48  --bmc1_out_stat                         full
% 6.70/1.48  --bmc1_ground_init                      false
% 6.70/1.48  --bmc1_pre_inst_next_state              false
% 6.70/1.48  --bmc1_pre_inst_state                   false
% 6.70/1.48  --bmc1_pre_inst_reach_state             false
% 6.70/1.48  --bmc1_out_unsat_core                   false
% 6.70/1.48  --bmc1_aig_witness_out                  false
% 6.70/1.48  --bmc1_verbose                          false
% 6.70/1.48  --bmc1_dump_clauses_tptp                false
% 6.70/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.70/1.48  --bmc1_dump_file                        -
% 6.70/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.70/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.70/1.48  --bmc1_ucm_extend_mode                  1
% 6.70/1.48  --bmc1_ucm_init_mode                    2
% 6.70/1.48  --bmc1_ucm_cone_mode                    none
% 6.70/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.70/1.48  --bmc1_ucm_relax_model                  4
% 6.70/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.70/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.70/1.48  --bmc1_ucm_layered_model                none
% 6.70/1.48  --bmc1_ucm_max_lemma_size               10
% 6.70/1.48  
% 6.70/1.48  ------ AIG Options
% 6.70/1.48  
% 6.70/1.48  --aig_mode                              false
% 6.70/1.48  
% 6.70/1.48  ------ Instantiation Options
% 6.70/1.48  
% 6.70/1.48  --instantiation_flag                    true
% 6.70/1.48  --inst_sos_flag                         false
% 6.70/1.48  --inst_sos_phase                        true
% 6.70/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.70/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.70/1.48  --inst_lit_sel_side                     num_symb
% 6.70/1.48  --inst_solver_per_active                1400
% 6.70/1.48  --inst_solver_calls_frac                1.
% 6.70/1.48  --inst_passive_queue_type               priority_queues
% 6.70/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.70/1.48  --inst_passive_queues_freq              [25;2]
% 6.70/1.48  --inst_dismatching                      true
% 6.70/1.48  --inst_eager_unprocessed_to_passive     true
% 6.70/1.48  --inst_prop_sim_given                   true
% 6.70/1.48  --inst_prop_sim_new                     false
% 6.70/1.48  --inst_subs_new                         false
% 6.70/1.48  --inst_eq_res_simp                      false
% 6.70/1.48  --inst_subs_given                       false
% 6.70/1.48  --inst_orphan_elimination               true
% 6.70/1.48  --inst_learning_loop_flag               true
% 6.70/1.48  --inst_learning_start                   3000
% 6.70/1.48  --inst_learning_factor                  2
% 6.70/1.48  --inst_start_prop_sim_after_learn       3
% 6.70/1.48  --inst_sel_renew                        solver
% 6.70/1.48  --inst_lit_activity_flag                true
% 6.70/1.48  --inst_restr_to_given                   false
% 6.70/1.48  --inst_activity_threshold               500
% 6.70/1.48  --inst_out_proof                        true
% 6.70/1.48  
% 6.70/1.48  ------ Resolution Options
% 6.70/1.48  
% 6.70/1.48  --resolution_flag                       true
% 6.70/1.48  --res_lit_sel                           adaptive
% 6.70/1.48  --res_lit_sel_side                      none
% 6.70/1.48  --res_ordering                          kbo
% 6.70/1.48  --res_to_prop_solver                    active
% 6.70/1.48  --res_prop_simpl_new                    false
% 6.70/1.48  --res_prop_simpl_given                  true
% 6.70/1.48  --res_passive_queue_type                priority_queues
% 6.70/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.70/1.48  --res_passive_queues_freq               [15;5]
% 6.70/1.48  --res_forward_subs                      full
% 6.70/1.48  --res_backward_subs                     full
% 6.70/1.48  --res_forward_subs_resolution           true
% 6.70/1.48  --res_backward_subs_resolution          true
% 6.70/1.48  --res_orphan_elimination                true
% 6.70/1.48  --res_time_limit                        2.
% 6.70/1.48  --res_out_proof                         true
% 6.70/1.48  
% 6.70/1.48  ------ Superposition Options
% 6.70/1.48  
% 6.70/1.48  --superposition_flag                    true
% 6.70/1.48  --sup_passive_queue_type                priority_queues
% 6.70/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.70/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.70/1.48  --demod_completeness_check              fast
% 6.70/1.48  --demod_use_ground                      true
% 6.70/1.48  --sup_to_prop_solver                    passive
% 6.70/1.48  --sup_prop_simpl_new                    true
% 6.70/1.48  --sup_prop_simpl_given                  true
% 6.70/1.48  --sup_fun_splitting                     false
% 6.70/1.48  --sup_smt_interval                      50000
% 6.70/1.48  
% 6.70/1.48  ------ Superposition Simplification Setup
% 6.70/1.48  
% 6.70/1.48  --sup_indices_passive                   []
% 6.70/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.70/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.70/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.70/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.70/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.70/1.48  --sup_full_bw                           [BwDemod]
% 6.70/1.48  --sup_immed_triv                        [TrivRules]
% 6.70/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.70/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.70/1.48  --sup_immed_bw_main                     []
% 6.70/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.70/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.70/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.70/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.70/1.48  
% 6.70/1.48  ------ Combination Options
% 6.70/1.48  
% 6.70/1.48  --comb_res_mult                         3
% 6.70/1.48  --comb_sup_mult                         2
% 6.70/1.48  --comb_inst_mult                        10
% 6.70/1.48  
% 6.70/1.48  ------ Debug Options
% 6.70/1.48  
% 6.70/1.48  --dbg_backtrace                         false
% 6.70/1.48  --dbg_dump_prop_clauses                 false
% 6.70/1.48  --dbg_dump_prop_clauses_file            -
% 6.70/1.48  --dbg_out_stat                          false
% 6.70/1.48  ------ Parsing...
% 6.70/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.70/1.48  
% 6.70/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 6.70/1.48  
% 6.70/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.70/1.48  
% 6.70/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.70/1.48  ------ Proving...
% 6.70/1.48  ------ Problem Properties 
% 6.70/1.48  
% 6.70/1.48  
% 6.70/1.48  clauses                                 72
% 6.70/1.48  conjectures                             5
% 6.70/1.48  EPR                                     14
% 6.70/1.48  Horn                                    63
% 6.70/1.48  unary                                   13
% 6.70/1.48  binary                                  29
% 6.70/1.48  lits                                    189
% 6.70/1.48  lits eq                                 41
% 6.70/1.48  fd_pure                                 0
% 6.70/1.48  fd_pseudo                               0
% 6.70/1.48  fd_cond                                 8
% 6.70/1.48  fd_pseudo_cond                          5
% 6.70/1.48  AC symbols                              0
% 6.70/1.48  
% 6.70/1.48  ------ Schedule dynamic 5 is on 
% 6.70/1.48  
% 6.70/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.70/1.48  
% 6.70/1.48  
% 6.70/1.48  ------ 
% 6.70/1.48  Current options:
% 6.70/1.48  ------ 
% 6.70/1.48  
% 6.70/1.48  ------ Input Options
% 6.70/1.48  
% 6.70/1.48  --out_options                           all
% 6.70/1.48  --tptp_safe_out                         true
% 6.70/1.48  --problem_path                          ""
% 6.70/1.48  --include_path                          ""
% 6.70/1.48  --clausifier                            res/vclausify_rel
% 6.70/1.48  --clausifier_options                    --mode clausify
% 6.70/1.48  --stdin                                 false
% 6.70/1.48  --stats_out                             all
% 6.70/1.48  
% 6.70/1.48  ------ General Options
% 6.70/1.48  
% 6.70/1.48  --fof                                   false
% 6.70/1.48  --time_out_real                         305.
% 6.70/1.48  --time_out_virtual                      -1.
% 6.70/1.48  --symbol_type_check                     false
% 6.70/1.48  --clausify_out                          false
% 6.70/1.48  --sig_cnt_out                           false
% 6.70/1.48  --trig_cnt_out                          false
% 6.70/1.48  --trig_cnt_out_tolerance                1.
% 6.70/1.48  --trig_cnt_out_sk_spl                   false
% 6.70/1.48  --abstr_cl_out                          false
% 6.70/1.48  
% 6.70/1.48  ------ Global Options
% 6.70/1.48  
% 6.70/1.48  --schedule                              default
% 6.70/1.48  --add_important_lit                     false
% 6.70/1.48  --prop_solver_per_cl                    1000
% 6.70/1.48  --min_unsat_core                        false
% 6.70/1.48  --soft_assumptions                      false
% 6.70/1.48  --soft_lemma_size                       3
% 6.70/1.48  --prop_impl_unit_size                   0
% 6.70/1.48  --prop_impl_unit                        []
% 6.70/1.48  --share_sel_clauses                     true
% 6.70/1.48  --reset_solvers                         false
% 6.70/1.48  --bc_imp_inh                            [conj_cone]
% 6.70/1.48  --conj_cone_tolerance                   3.
% 6.70/1.48  --extra_neg_conj                        none
% 6.70/1.48  --large_theory_mode                     true
% 6.70/1.48  --prolific_symb_bound                   200
% 6.70/1.48  --lt_threshold                          2000
% 6.70/1.48  --clause_weak_htbl                      true
% 6.70/1.48  --gc_record_bc_elim                     false
% 6.70/1.48  
% 6.70/1.48  ------ Preprocessing Options
% 6.70/1.48  
% 6.70/1.48  --preprocessing_flag                    true
% 6.70/1.48  --time_out_prep_mult                    0.1
% 6.70/1.48  --splitting_mode                        input
% 6.70/1.48  --splitting_grd                         true
% 6.70/1.48  --splitting_cvd                         false
% 6.70/1.48  --splitting_cvd_svl                     false
% 6.70/1.48  --splitting_nvd                         32
% 6.70/1.48  --sub_typing                            true
% 6.70/1.48  --prep_gs_sim                           true
% 6.70/1.48  --prep_unflatten                        true
% 6.70/1.48  --prep_res_sim                          true
% 6.70/1.48  --prep_upred                            true
% 6.70/1.48  --prep_sem_filter                       exhaustive
% 6.70/1.48  --prep_sem_filter_out                   false
% 6.70/1.48  --pred_elim                             true
% 6.70/1.48  --res_sim_input                         true
% 6.70/1.48  --eq_ax_congr_red                       true
% 6.70/1.48  --pure_diseq_elim                       true
% 6.70/1.48  --brand_transform                       false
% 6.70/1.48  --non_eq_to_eq                          false
% 6.70/1.48  --prep_def_merge                        true
% 6.70/1.48  --prep_def_merge_prop_impl              false
% 6.70/1.48  --prep_def_merge_mbd                    true
% 6.70/1.48  --prep_def_merge_tr_red                 false
% 6.70/1.48  --prep_def_merge_tr_cl                  false
% 6.70/1.48  --smt_preprocessing                     true
% 6.70/1.48  --smt_ac_axioms                         fast
% 6.70/1.48  --preprocessed_out                      false
% 6.70/1.48  --preprocessed_stats                    false
% 6.70/1.48  
% 6.70/1.48  ------ Abstraction refinement Options
% 6.70/1.48  
% 6.70/1.48  --abstr_ref                             []
% 6.70/1.48  --abstr_ref_prep                        false
% 6.70/1.48  --abstr_ref_until_sat                   false
% 6.70/1.48  --abstr_ref_sig_restrict                funpre
% 6.70/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.70/1.48  --abstr_ref_under                       []
% 6.70/1.48  
% 6.70/1.48  ------ SAT Options
% 6.70/1.48  
% 6.70/1.48  --sat_mode                              false
% 6.70/1.48  --sat_fm_restart_options                ""
% 6.70/1.48  --sat_gr_def                            false
% 6.70/1.48  --sat_epr_types                         true
% 6.70/1.48  --sat_non_cyclic_types                  false
% 6.70/1.48  --sat_finite_models                     false
% 6.70/1.48  --sat_fm_lemmas                         false
% 6.70/1.48  --sat_fm_prep                           false
% 6.70/1.48  --sat_fm_uc_incr                        true
% 6.70/1.48  --sat_out_model                         small
% 6.70/1.48  --sat_out_clauses                       false
% 6.70/1.48  
% 6.70/1.48  ------ QBF Options
% 6.70/1.48  
% 6.70/1.48  --qbf_mode                              false
% 6.70/1.48  --qbf_elim_univ                         false
% 6.70/1.48  --qbf_dom_inst                          none
% 6.70/1.48  --qbf_dom_pre_inst                      false
% 6.70/1.48  --qbf_sk_in                             false
% 6.70/1.48  --qbf_pred_elim                         true
% 6.70/1.48  --qbf_split                             512
% 6.70/1.48  
% 6.70/1.48  ------ BMC1 Options
% 6.70/1.48  
% 6.70/1.48  --bmc1_incremental                      false
% 6.70/1.48  --bmc1_axioms                           reachable_all
% 6.70/1.48  --bmc1_min_bound                        0
% 6.70/1.48  --bmc1_max_bound                        -1
% 6.70/1.48  --bmc1_max_bound_default                -1
% 6.70/1.48  --bmc1_symbol_reachability              true
% 6.70/1.48  --bmc1_property_lemmas                  false
% 6.70/1.48  --bmc1_k_induction                      false
% 6.70/1.48  --bmc1_non_equiv_states                 false
% 6.70/1.48  --bmc1_deadlock                         false
% 6.70/1.48  --bmc1_ucm                              false
% 6.70/1.48  --bmc1_add_unsat_core                   none
% 6.70/1.48  --bmc1_unsat_core_children              false
% 6.70/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.70/1.48  --bmc1_out_stat                         full
% 6.70/1.48  --bmc1_ground_init                      false
% 6.70/1.48  --bmc1_pre_inst_next_state              false
% 6.70/1.48  --bmc1_pre_inst_state                   false
% 6.70/1.48  --bmc1_pre_inst_reach_state             false
% 6.70/1.48  --bmc1_out_unsat_core                   false
% 6.70/1.48  --bmc1_aig_witness_out                  false
% 6.70/1.48  --bmc1_verbose                          false
% 6.70/1.48  --bmc1_dump_clauses_tptp                false
% 6.70/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.70/1.48  --bmc1_dump_file                        -
% 6.70/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.70/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.70/1.48  --bmc1_ucm_extend_mode                  1
% 6.70/1.48  --bmc1_ucm_init_mode                    2
% 6.70/1.48  --bmc1_ucm_cone_mode                    none
% 6.70/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.70/1.48  --bmc1_ucm_relax_model                  4
% 6.70/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.70/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.70/1.48  --bmc1_ucm_layered_model                none
% 6.70/1.48  --bmc1_ucm_max_lemma_size               10
% 6.70/1.48  
% 6.70/1.48  ------ AIG Options
% 6.70/1.48  
% 6.70/1.48  --aig_mode                              false
% 6.70/1.48  
% 6.70/1.48  ------ Instantiation Options
% 6.70/1.48  
% 6.70/1.48  --instantiation_flag                    true
% 6.70/1.48  --inst_sos_flag                         false
% 6.70/1.48  --inst_sos_phase                        true
% 6.70/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.70/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.70/1.48  --inst_lit_sel_side                     none
% 6.70/1.48  --inst_solver_per_active                1400
% 6.70/1.48  --inst_solver_calls_frac                1.
% 6.70/1.48  --inst_passive_queue_type               priority_queues
% 6.70/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.70/1.48  --inst_passive_queues_freq              [25;2]
% 6.70/1.48  --inst_dismatching                      true
% 6.70/1.48  --inst_eager_unprocessed_to_passive     true
% 6.70/1.48  --inst_prop_sim_given                   true
% 6.70/1.48  --inst_prop_sim_new                     false
% 6.70/1.48  --inst_subs_new                         false
% 6.70/1.48  --inst_eq_res_simp                      false
% 6.70/1.48  --inst_subs_given                       false
% 6.70/1.48  --inst_orphan_elimination               true
% 6.70/1.48  --inst_learning_loop_flag               true
% 6.70/1.48  --inst_learning_start                   3000
% 6.70/1.48  --inst_learning_factor                  2
% 6.70/1.48  --inst_start_prop_sim_after_learn       3
% 6.70/1.48  --inst_sel_renew                        solver
% 6.70/1.48  --inst_lit_activity_flag                true
% 6.70/1.48  --inst_restr_to_given                   false
% 6.70/1.48  --inst_activity_threshold               500
% 6.70/1.48  --inst_out_proof                        true
% 6.70/1.48  
% 6.70/1.48  ------ Resolution Options
% 6.70/1.48  
% 6.70/1.48  --resolution_flag                       false
% 6.70/1.48  --res_lit_sel                           adaptive
% 6.70/1.48  --res_lit_sel_side                      none
% 6.70/1.48  --res_ordering                          kbo
% 6.70/1.48  --res_to_prop_solver                    active
% 6.70/1.48  --res_prop_simpl_new                    false
% 6.70/1.48  --res_prop_simpl_given                  true
% 6.70/1.48  --res_passive_queue_type                priority_queues
% 6.70/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.70/1.48  --res_passive_queues_freq               [15;5]
% 6.70/1.48  --res_forward_subs                      full
% 6.70/1.48  --res_backward_subs                     full
% 6.70/1.48  --res_forward_subs_resolution           true
% 6.70/1.48  --res_backward_subs_resolution          true
% 6.70/1.48  --res_orphan_elimination                true
% 6.70/1.48  --res_time_limit                        2.
% 6.70/1.48  --res_out_proof                         true
% 6.70/1.48  
% 6.70/1.48  ------ Superposition Options
% 6.70/1.48  
% 6.70/1.48  --superposition_flag                    true
% 6.70/1.48  --sup_passive_queue_type                priority_queues
% 6.70/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.70/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.70/1.48  --demod_completeness_check              fast
% 6.70/1.48  --demod_use_ground                      true
% 6.70/1.48  --sup_to_prop_solver                    passive
% 6.70/1.48  --sup_prop_simpl_new                    true
% 6.70/1.48  --sup_prop_simpl_given                  true
% 6.70/1.48  --sup_fun_splitting                     false
% 6.70/1.48  --sup_smt_interval                      50000
% 6.70/1.48  
% 6.70/1.48  ------ Superposition Simplification Setup
% 6.70/1.48  
% 6.70/1.48  --sup_indices_passive                   []
% 6.70/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.70/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.70/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.70/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.70/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.70/1.48  --sup_full_bw                           [BwDemod]
% 6.70/1.48  --sup_immed_triv                        [TrivRules]
% 6.70/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.70/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.70/1.48  --sup_immed_bw_main                     []
% 6.70/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.70/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.70/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.70/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.70/1.48  
% 6.70/1.48  ------ Combination Options
% 6.70/1.48  
% 6.70/1.48  --comb_res_mult                         3
% 6.70/1.48  --comb_sup_mult                         2
% 6.70/1.48  --comb_inst_mult                        10
% 6.70/1.48  
% 6.70/1.48  ------ Debug Options
% 6.70/1.48  
% 6.70/1.48  --dbg_backtrace                         false
% 6.70/1.48  --dbg_dump_prop_clauses                 false
% 6.70/1.48  --dbg_dump_prop_clauses_file            -
% 6.70/1.48  --dbg_out_stat                          false
% 6.70/1.48  
% 6.70/1.48  
% 6.70/1.48  
% 6.70/1.48  
% 6.70/1.48  ------ Proving...
% 6.70/1.48  
% 6.70/1.48  
% 6.70/1.48  % SZS status Theorem for theBenchmark.p
% 6.70/1.48  
% 6.70/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.70/1.48  
% 6.70/1.48  fof(f48,conjecture,(
% 6.70/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f49,negated_conjecture,(
% 6.70/1.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 6.70/1.48    inference(negated_conjecture,[],[f48])).
% 6.70/1.48  
% 6.70/1.48  fof(f104,plain,(
% 6.70/1.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.70/1.48    inference(ennf_transformation,[],[f49])).
% 6.70/1.48  
% 6.70/1.48  fof(f105,plain,(
% 6.70/1.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.70/1.48    inference(flattening,[],[f104])).
% 6.70/1.48  
% 6.70/1.48  fof(f123,plain,(
% 6.70/1.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) | ~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v3_funct_2(sK4,sK3,sK3) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 6.70/1.48    introduced(choice_axiom,[])).
% 6.70/1.48  
% 6.70/1.48  fof(f124,plain,(
% 6.70/1.48    (~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) | ~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v3_funct_2(sK4,sK3,sK3) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 6.70/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f105,f123])).
% 6.70/1.48  
% 6.70/1.48  fof(f205,plain,(
% 6.70/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 6.70/1.48    inference(cnf_transformation,[],[f124])).
% 6.70/1.48  
% 6.70/1.48  fof(f37,axiom,(
% 6.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f88,plain,(
% 6.70/1.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.70/1.48    inference(ennf_transformation,[],[f37])).
% 6.70/1.48  
% 6.70/1.48  fof(f177,plain,(
% 6.70/1.48    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f88])).
% 6.70/1.48  
% 6.70/1.48  fof(f33,axiom,(
% 6.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f84,plain,(
% 6.70/1.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.70/1.48    inference(ennf_transformation,[],[f33])).
% 6.70/1.48  
% 6.70/1.48  fof(f171,plain,(
% 6.70/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f84])).
% 6.70/1.48  
% 6.70/1.48  fof(f24,axiom,(
% 6.70/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f75,plain,(
% 6.70/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.70/1.48    inference(ennf_transformation,[],[f24])).
% 6.70/1.48  
% 6.70/1.48  fof(f76,plain,(
% 6.70/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.70/1.48    inference(flattening,[],[f75])).
% 6.70/1.48  
% 6.70/1.48  fof(f157,plain,(
% 6.70/1.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f76])).
% 6.70/1.48  
% 6.70/1.48  fof(f32,axiom,(
% 6.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f83,plain,(
% 6.70/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.70/1.48    inference(ennf_transformation,[],[f32])).
% 6.70/1.48  
% 6.70/1.48  fof(f170,plain,(
% 6.70/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f83])).
% 6.70/1.48  
% 6.70/1.48  fof(f23,axiom,(
% 6.70/1.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f74,plain,(
% 6.70/1.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.70/1.48    inference(ennf_transformation,[],[f23])).
% 6.70/1.48  
% 6.70/1.48  fof(f156,plain,(
% 6.70/1.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f74])).
% 6.70/1.48  
% 6.70/1.48  fof(f39,axiom,(
% 6.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f90,plain,(
% 6.70/1.48    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.70/1.48    inference(ennf_transformation,[],[f39])).
% 6.70/1.48  
% 6.70/1.48  fof(f91,plain,(
% 6.70/1.48    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.70/1.48    inference(flattening,[],[f90])).
% 6.70/1.48  
% 6.70/1.48  fof(f183,plain,(
% 6.70/1.48    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f91])).
% 6.70/1.48  
% 6.70/1.48  fof(f41,axiom,(
% 6.70/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f94,plain,(
% 6.70/1.48    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.70/1.48    inference(ennf_transformation,[],[f41])).
% 6.70/1.48  
% 6.70/1.48  fof(f95,plain,(
% 6.70/1.48    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.70/1.48    inference(flattening,[],[f94])).
% 6.70/1.48  
% 6.70/1.48  fof(f122,plain,(
% 6.70/1.48    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.70/1.48    inference(nnf_transformation,[],[f95])).
% 6.70/1.48  
% 6.70/1.48  fof(f190,plain,(
% 6.70/1.48    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f122])).
% 6.70/1.48  
% 6.70/1.48  fof(f172,plain,(
% 6.70/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f84])).
% 6.70/1.48  
% 6.70/1.48  fof(f202,plain,(
% 6.70/1.48    v1_funct_1(sK4)),
% 6.70/1.48    inference(cnf_transformation,[],[f124])).
% 6.70/1.48  
% 6.70/1.48  fof(f204,plain,(
% 6.70/1.48    v3_funct_2(sK4,sK3,sK3)),
% 6.70/1.48    inference(cnf_transformation,[],[f124])).
% 6.70/1.48  
% 6.70/1.48  fof(f34,axiom,(
% 6.70/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f85,plain,(
% 6.70/1.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.70/1.48    inference(ennf_transformation,[],[f34])).
% 6.70/1.48  
% 6.70/1.48  fof(f173,plain,(
% 6.70/1.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f85])).
% 6.70/1.48  
% 6.70/1.48  fof(f47,axiom,(
% 6.70/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f102,plain,(
% 6.70/1.48    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.70/1.48    inference(ennf_transformation,[],[f47])).
% 6.70/1.48  
% 6.70/1.48  fof(f103,plain,(
% 6.70/1.48    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.70/1.48    inference(flattening,[],[f102])).
% 6.70/1.48  
% 6.70/1.48  fof(f200,plain,(
% 6.70/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f103])).
% 6.70/1.48  
% 6.70/1.48  fof(f203,plain,(
% 6.70/1.48    v1_funct_2(sK4,sK3,sK3)),
% 6.70/1.48    inference(cnf_transformation,[],[f124])).
% 6.70/1.48  
% 6.70/1.48  fof(f182,plain,(
% 6.70/1.48    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f91])).
% 6.70/1.48  
% 6.70/1.48  fof(f28,axiom,(
% 6.70/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f79,plain,(
% 6.70/1.48    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.70/1.48    inference(ennf_transformation,[],[f28])).
% 6.70/1.48  
% 6.70/1.48  fof(f80,plain,(
% 6.70/1.48    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.70/1.48    inference(flattening,[],[f79])).
% 6.70/1.48  
% 6.70/1.48  fof(f164,plain,(
% 6.70/1.48    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f80])).
% 6.70/1.48  
% 6.70/1.48  fof(f46,axiom,(
% 6.70/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f199,plain,(
% 6.70/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f46])).
% 6.70/1.48  
% 6.70/1.48  fof(f212,plain,(
% 6.70/1.48    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.70/1.48    inference(definition_unfolding,[],[f164,f199])).
% 6.70/1.48  
% 6.70/1.48  fof(f45,axiom,(
% 6.70/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f100,plain,(
% 6.70/1.48    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.70/1.48    inference(ennf_transformation,[],[f45])).
% 6.70/1.48  
% 6.70/1.48  fof(f101,plain,(
% 6.70/1.48    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.70/1.48    inference(flattening,[],[f100])).
% 6.70/1.48  
% 6.70/1.48  fof(f198,plain,(
% 6.70/1.48    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f101])).
% 6.70/1.48  
% 6.70/1.48  fof(f42,axiom,(
% 6.70/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f96,plain,(
% 6.70/1.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.70/1.48    inference(ennf_transformation,[],[f42])).
% 6.70/1.48  
% 6.70/1.48  fof(f97,plain,(
% 6.70/1.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.70/1.48    inference(flattening,[],[f96])).
% 6.70/1.48  
% 6.70/1.48  fof(f195,plain,(
% 6.70/1.48    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f97])).
% 6.70/1.48  
% 6.70/1.48  fof(f44,axiom,(
% 6.70/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f98,plain,(
% 6.70/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.70/1.48    inference(ennf_transformation,[],[f44])).
% 6.70/1.48  
% 6.70/1.48  fof(f99,plain,(
% 6.70/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.70/1.48    inference(flattening,[],[f98])).
% 6.70/1.48  
% 6.70/1.48  fof(f197,plain,(
% 6.70/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f99])).
% 6.70/1.48  
% 6.70/1.48  fof(f192,plain,(
% 6.70/1.48    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f97])).
% 6.70/1.48  
% 6.70/1.48  fof(f165,plain,(
% 6.70/1.48    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f80])).
% 6.70/1.48  
% 6.70/1.48  fof(f211,plain,(
% 6.70/1.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.70/1.48    inference(definition_unfolding,[],[f165,f199])).
% 6.70/1.48  
% 6.70/1.48  fof(f206,plain,(
% 6.70/1.48    ~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) | ~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3))),
% 6.70/1.48    inference(cnf_transformation,[],[f124])).
% 6.70/1.48  
% 6.70/1.48  fof(f43,axiom,(
% 6.70/1.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f51,plain,(
% 6.70/1.48    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 6.70/1.48    inference(pure_predicate_removal,[],[f43])).
% 6.70/1.48  
% 6.70/1.48  fof(f196,plain,(
% 6.70/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f51])).
% 6.70/1.48  
% 6.70/1.48  fof(f35,axiom,(
% 6.70/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f86,plain,(
% 6.70/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.70/1.48    inference(ennf_transformation,[],[f35])).
% 6.70/1.48  
% 6.70/1.48  fof(f87,plain,(
% 6.70/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.70/1.48    inference(flattening,[],[f86])).
% 6.70/1.48  
% 6.70/1.48  fof(f120,plain,(
% 6.70/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.70/1.48    inference(nnf_transformation,[],[f87])).
% 6.70/1.48  
% 6.70/1.48  fof(f175,plain,(
% 6.70/1.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f120])).
% 6.70/1.48  
% 6.70/1.48  fof(f217,plain,(
% 6.70/1.48    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.70/1.48    inference(equality_resolution,[],[f175])).
% 6.70/1.48  
% 6.70/1.48  fof(f25,axiom,(
% 6.70/1.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f77,plain,(
% 6.70/1.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 6.70/1.48    inference(ennf_transformation,[],[f25])).
% 6.70/1.48  
% 6.70/1.48  fof(f78,plain,(
% 6.70/1.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 6.70/1.48    inference(flattening,[],[f77])).
% 6.70/1.48  
% 6.70/1.48  fof(f159,plain,(
% 6.70/1.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f78])).
% 6.70/1.48  
% 6.70/1.48  fof(f4,axiom,(
% 6.70/1.48    v1_xboole_0(k1_xboole_0)),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f131,plain,(
% 6.70/1.48    v1_xboole_0(k1_xboole_0)),
% 6.70/1.48    inference(cnf_transformation,[],[f4])).
% 6.70/1.48  
% 6.70/1.48  fof(f18,axiom,(
% 6.70/1.48    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f66,plain,(
% 6.70/1.48    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 6.70/1.48    inference(ennf_transformation,[],[f18])).
% 6.70/1.48  
% 6.70/1.48  fof(f151,plain,(
% 6.70/1.48    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f66])).
% 6.70/1.48  
% 6.70/1.48  fof(f5,axiom,(
% 6.70/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f55,plain,(
% 6.70/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 6.70/1.48    inference(ennf_transformation,[],[f5])).
% 6.70/1.48  
% 6.70/1.48  fof(f132,plain,(
% 6.70/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f55])).
% 6.70/1.48  
% 6.70/1.48  fof(f12,axiom,(
% 6.70/1.48    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f61,plain,(
% 6.70/1.48    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 6.70/1.48    inference(ennf_transformation,[],[f12])).
% 6.70/1.48  
% 6.70/1.48  fof(f142,plain,(
% 6.70/1.48    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f61])).
% 6.70/1.48  
% 6.70/1.48  fof(f36,axiom,(
% 6.70/1.48    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f176,plain,(
% 6.70/1.48    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))) )),
% 6.70/1.48    inference(cnf_transformation,[],[f36])).
% 6.70/1.48  
% 6.70/1.48  fof(f214,plain,(
% 6.70/1.48    ( ! [X0] : (r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0))) )),
% 6.70/1.48    inference(definition_unfolding,[],[f176,f199])).
% 6.70/1.48  
% 6.70/1.48  fof(f8,axiom,(
% 6.70/1.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f138,plain,(
% 6.70/1.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f8])).
% 6.70/1.48  
% 6.70/1.48  fof(f9,axiom,(
% 6.70/1.48    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f57,plain,(
% 6.70/1.48    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 6.70/1.48    inference(ennf_transformation,[],[f9])).
% 6.70/1.48  
% 6.70/1.48  fof(f58,plain,(
% 6.70/1.48    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 6.70/1.48    inference(flattening,[],[f57])).
% 6.70/1.48  
% 6.70/1.48  fof(f139,plain,(
% 6.70/1.48    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f58])).
% 6.70/1.48  
% 6.70/1.48  fof(f15,axiom,(
% 6.70/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f118,plain,(
% 6.70/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.70/1.48    inference(nnf_transformation,[],[f15])).
% 6.70/1.48  
% 6.70/1.48  fof(f147,plain,(
% 6.70/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f118])).
% 6.70/1.48  
% 6.70/1.48  fof(f7,axiom,(
% 6.70/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f116,plain,(
% 6.70/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.70/1.48    inference(nnf_transformation,[],[f7])).
% 6.70/1.48  
% 6.70/1.48  fof(f117,plain,(
% 6.70/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.70/1.48    inference(flattening,[],[f116])).
% 6.70/1.48  
% 6.70/1.48  fof(f135,plain,(
% 6.70/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.70/1.48    inference(cnf_transformation,[],[f117])).
% 6.70/1.48  
% 6.70/1.48  fof(f216,plain,(
% 6.70/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.70/1.48    inference(equality_resolution,[],[f135])).
% 6.70/1.48  
% 6.70/1.48  fof(f11,axiom,(
% 6.70/1.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 6.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.70/1.48  
% 6.70/1.48  fof(f60,plain,(
% 6.70/1.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 6.70/1.48    inference(ennf_transformation,[],[f11])).
% 6.70/1.48  
% 6.70/1.48  fof(f141,plain,(
% 6.70/1.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 6.70/1.48    inference(cnf_transformation,[],[f60])).
% 6.70/1.48  
% 6.70/1.48  cnf(c_77,negated_conjecture,
% 6.70/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 6.70/1.48      inference(cnf_transformation,[],[f205]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4051,plain,
% 6.70/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_53,plain,
% 6.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f177]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4071,plain,
% 6.70/1.48      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12678,plain,
% 6.70/1.48      ( k7_relset_1(sK3,sK3,sK4,sK3) = k2_relset_1(sK3,sK3,sK4) ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4071]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_47,plain,
% 6.70/1.48      ( v4_relat_1(X0,X1)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.70/1.48      inference(cnf_transformation,[],[f171]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_32,plain,
% 6.70/1.48      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 6.70/1.48      inference(cnf_transformation,[],[f157]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_1007,plain,
% 6.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ v1_relat_1(X0)
% 6.70/1.48      | k7_relat_1(X0,X1) = X0 ),
% 6.70/1.48      inference(resolution,[status(thm)],[c_47,c_32]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_45,plain,
% 6.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | v1_relat_1(X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f170]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_1011,plain,
% 6.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | k7_relat_1(X0,X1) = X0 ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_1007,c_47,c_45,c_32]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4044,plain,
% 6.70/1.48      ( k7_relat_1(X0,X1) = X0
% 6.70/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_6522,plain,
% 6.70/1.48      ( k7_relat_1(sK4,sK3) = sK4 ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4044]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4077,plain,
% 6.70/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.70/1.48      | v1_relat_1(X0) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_6198,plain,
% 6.70/1.48      ( v1_relat_1(sK4) = iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4077]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_31,plain,
% 6.70/1.48      ( ~ v1_relat_1(X0)
% 6.70/1.48      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 6.70/1.48      inference(cnf_transformation,[],[f156]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4087,plain,
% 6.70/1.48      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 6.70/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_6730,plain,
% 6.70/1.48      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_6198,c_4087]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_7358,plain,
% 6.70/1.48      ( k9_relat_1(sK4,sK3) = k2_relat_1(sK4) ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_6522,c_6730]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_56,plain,
% 6.70/1.48      ( ~ v3_funct_2(X0,X1,X2)
% 6.70/1.48      | v2_funct_2(X0,X2)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ v1_funct_1(X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f183]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_66,plain,
% 6.70/1.48      ( ~ v2_funct_2(X0,X1)
% 6.70/1.48      | ~ v5_relat_1(X0,X1)
% 6.70/1.48      | ~ v1_relat_1(X0)
% 6.70/1.48      | k2_relat_1(X0) = X1 ),
% 6.70/1.48      inference(cnf_transformation,[],[f190]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_1057,plain,
% 6.70/1.48      ( ~ v3_funct_2(X0,X1,X2)
% 6.70/1.48      | ~ v5_relat_1(X3,X4)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | ~ v1_relat_1(X3)
% 6.70/1.48      | X3 != X0
% 6.70/1.48      | X4 != X2
% 6.70/1.48      | k2_relat_1(X3) = X4 ),
% 6.70/1.48      inference(resolution_lifted,[status(thm)],[c_56,c_66]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_1058,plain,
% 6.70/1.48      ( ~ v3_funct_2(X0,X1,X2)
% 6.70/1.48      | ~ v5_relat_1(X0,X2)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | ~ v1_relat_1(X0)
% 6.70/1.48      | k2_relat_1(X0) = X2 ),
% 6.70/1.48      inference(unflattening,[status(thm)],[c_1057]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_1062,plain,
% 6.70/1.48      ( ~ v1_funct_1(X0)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ v5_relat_1(X0,X2)
% 6.70/1.48      | ~ v3_funct_2(X0,X1,X2)
% 6.70/1.48      | k2_relat_1(X0) = X2 ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_1058,c_45]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_1063,plain,
% 6.70/1.48      ( ~ v3_funct_2(X0,X1,X2)
% 6.70/1.48      | ~ v5_relat_1(X0,X2)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | k2_relat_1(X0) = X2 ),
% 6.70/1.48      inference(renaming,[status(thm)],[c_1062]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_46,plain,
% 6.70/1.48      ( v5_relat_1(X0,X1)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 6.70/1.48      inference(cnf_transformation,[],[f172]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_1078,plain,
% 6.70/1.48      ( ~ v3_funct_2(X0,X1,X2)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | k2_relat_1(X0) = X2 ),
% 6.70/1.48      inference(forward_subsumption_resolution,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_1063,c_46]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4043,plain,
% 6.70/1.48      ( k2_relat_1(X0) = X1
% 6.70/1.48      | v3_funct_2(X0,X2,X1) != iProver_top
% 6.70/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 6.70/1.48      | v1_funct_1(X0) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5899,plain,
% 6.70/1.48      ( k2_relat_1(sK4) = sK3
% 6.70/1.48      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4043]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_80,negated_conjecture,
% 6.70/1.48      ( v1_funct_1(sK4) ),
% 6.70/1.48      inference(cnf_transformation,[],[f202]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_78,negated_conjecture,
% 6.70/1.48      ( v3_funct_2(sK4,sK3,sK3) ),
% 6.70/1.48      inference(cnf_transformation,[],[f204]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4733,plain,
% 6.70/1.48      ( ~ v3_funct_2(sK4,X0,X1)
% 6.70/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.70/1.48      | ~ v1_funct_1(sK4)
% 6.70/1.48      | k2_relat_1(sK4) = X1 ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_1078]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4990,plain,
% 6.70/1.48      ( ~ v3_funct_2(sK4,sK3,sK3)
% 6.70/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.70/1.48      | ~ v1_funct_1(sK4)
% 6.70/1.48      | k2_relat_1(sK4) = sK3 ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_4733]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_6321,plain,
% 6.70/1.48      ( k2_relat_1(sK4) = sK3 ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_5899,c_80,c_78,c_77,c_4990]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_7365,plain,
% 6.70/1.48      ( k9_relat_1(sK4,sK3) = sK3 ),
% 6.70/1.48      inference(light_normalisation,[status(thm)],[c_7358,c_6321]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_48,plain,
% 6.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 6.70/1.48      inference(cnf_transformation,[],[f173]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4076,plain,
% 6.70/1.48      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12095,plain,
% 6.70/1.48      ( k7_relset_1(sK3,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4076]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12685,plain,
% 6.70/1.48      ( k2_relset_1(sK3,sK3,sK4) = sK3 ),
% 6.70/1.48      inference(demodulation,[status(thm)],[c_12678,c_7365,c_12095]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_75,plain,
% 6.70/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ v2_funct_1(X0)
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | k2_relset_1(X1,X2,X0) != X2
% 6.70/1.48      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 6.70/1.48      | k1_xboole_0 = X2 ),
% 6.70/1.48      inference(cnf_transformation,[],[f200]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4053,plain,
% 6.70/1.48      ( k2_relset_1(X0,X1,X2) != X1
% 6.70/1.48      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 6.70/1.48      | k1_xboole_0 = X1
% 6.70/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.70/1.48      | v2_funct_1(X2) != iProver_top
% 6.70/1.48      | v1_funct_1(X2) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12733,plain,
% 6.70/1.48      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
% 6.70/1.48      | sK3 = k1_xboole_0
% 6.70/1.48      | v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 6.70/1.48      | v2_funct_1(sK4) != iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_12685,c_4053]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_79,negated_conjecture,
% 6.70/1.48      ( v1_funct_2(sK4,sK3,sK3) ),
% 6.70/1.48      inference(cnf_transformation,[],[f203]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_57,plain,
% 6.70/1.48      ( ~ v3_funct_2(X0,X1,X2)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | v2_funct_1(X0)
% 6.70/1.48      | ~ v1_funct_1(X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f182]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4707,plain,
% 6.70/1.48      ( ~ v3_funct_2(sK4,X0,X1)
% 6.70/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.70/1.48      | v2_funct_1(sK4)
% 6.70/1.48      | ~ v1_funct_1(sK4) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_57]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4987,plain,
% 6.70/1.48      ( ~ v3_funct_2(sK4,sK3,sK3)
% 6.70/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.70/1.48      | v2_funct_1(sK4)
% 6.70/1.48      | ~ v1_funct_1(sK4) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_4707]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12759,plain,
% 6.70/1.48      ( ~ v1_funct_2(sK4,sK3,sK3)
% 6.70/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.70/1.48      | ~ v2_funct_1(sK4)
% 6.70/1.48      | ~ v1_funct_1(sK4)
% 6.70/1.48      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
% 6.70/1.48      | sK3 = k1_xboole_0 ),
% 6.70/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_12733]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_14200,plain,
% 6.70/1.48      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
% 6.70/1.48      | sK3 = k1_xboole_0 ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_12733,c_80,c_79,c_78,c_77,c_4987,c_12759]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4068,plain,
% 6.70/1.48      ( v3_funct_2(X0,X1,X2) != iProver_top
% 6.70/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.70/1.48      | v2_funct_1(X0) = iProver_top
% 6.70/1.48      | v1_funct_1(X0) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_14939,plain,
% 6.70/1.48      ( v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v2_funct_1(sK4) = iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4068]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_81,plain,
% 6.70/1.48      ( v1_funct_1(sK4) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_80]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_83,plain,
% 6.70/1.48      ( v3_funct_2(sK4,sK3,sK3) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_78]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_84,plain,
% 6.70/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4988,plain,
% 6.70/1.48      ( v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 6.70/1.48      | v2_funct_1(sK4) = iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_4987]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15261,plain,
% 6.70/1.48      ( v2_funct_1(sK4) = iProver_top ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_14939,c_81,c_83,c_84,c_4988]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_40,plain,
% 6.70/1.48      ( ~ v2_funct_1(X0)
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | ~ v1_relat_1(X0)
% 6.70/1.48      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 6.70/1.48      inference(cnf_transformation,[],[f212]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4081,plain,
% 6.70/1.48      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 6.70/1.48      | v2_funct_1(X0) != iProver_top
% 6.70/1.48      | v1_funct_1(X0) != iProver_top
% 6.70/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15267,plain,
% 6.70/1.48      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top
% 6.70/1.48      | v1_relat_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_15261,c_4081]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4646,plain,
% 6.70/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.70/1.48      | v1_relat_1(sK4) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_45]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5256,plain,
% 6.70/1.48      ( ~ v2_funct_1(sK4)
% 6.70/1.48      | ~ v1_funct_1(sK4)
% 6.70/1.48      | ~ v1_relat_1(sK4)
% 6.70/1.48      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_40]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15370,plain,
% 6.70/1.48      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_15267,c_80,c_78,c_77,c_4646,c_4987,c_5256]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15373,plain,
% 6.70/1.48      ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK3)
% 6.70/1.48      | sK3 = k1_xboole_0 ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_14200,c_15370]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_73,plain,
% 6.70/1.48      ( ~ v1_funct_2(X0,X1,X1)
% 6.70/1.48      | ~ v3_funct_2(X0,X1,X1)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f198]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4055,plain,
% 6.70/1.48      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 6.70/1.48      | v1_funct_2(X1,X0,X0) != iProver_top
% 6.70/1.48      | v3_funct_2(X1,X0,X0) != iProver_top
% 6.70/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 6.70/1.48      | v1_funct_1(X1) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_10648,plain,
% 6.70/1.48      ( k2_funct_2(sK3,sK4) = k2_funct_1(sK4)
% 6.70/1.48      | v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4055]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4801,plain,
% 6.70/1.48      ( ~ v1_funct_2(sK4,X0,X0)
% 6.70/1.48      | ~ v3_funct_2(sK4,X0,X0)
% 6.70/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 6.70/1.48      | ~ v1_funct_1(sK4)
% 6.70/1.48      | k2_funct_2(X0,sK4) = k2_funct_1(sK4) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_73]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5086,plain,
% 6.70/1.48      ( ~ v1_funct_2(sK4,sK3,sK3)
% 6.70/1.48      | ~ v3_funct_2(sK4,sK3,sK3)
% 6.70/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.70/1.48      | ~ v1_funct_1(sK4)
% 6.70/1.48      | k2_funct_2(sK3,sK4) = k2_funct_1(sK4) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_4801]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_11139,plain,
% 6.70/1.48      ( k2_funct_2(sK3,sK4) = k2_funct_1(sK4) ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_10648,c_80,c_79,c_78,c_77,c_5086]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_67,plain,
% 6.70/1.48      ( ~ v1_funct_2(X0,X1,X1)
% 6.70/1.48      | ~ v3_funct_2(X0,X1,X1)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.70/1.48      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.70/1.48      | ~ v1_funct_1(X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f195]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4061,plain,
% 6.70/1.48      ( v1_funct_2(X0,X1,X1) != iProver_top
% 6.70/1.48      | v3_funct_2(X0,X1,X1) != iProver_top
% 6.70/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 6.70/1.48      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 6.70/1.48      | v1_funct_1(X0) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_14464,plain,
% 6.70/1.48      ( v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top
% 6.70/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_11139,c_4061]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_82,plain,
% 6.70/1.48      ( v1_funct_2(sK4,sK3,sK3) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_79]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15464,plain,
% 6.70/1.48      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_14464,c_81,c_82,c_83,c_84]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_72,plain,
% 6.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | ~ v1_funct_1(X3)
% 6.70/1.48      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f197]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4056,plain,
% 6.70/1.48      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 6.70/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 6.70/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.70/1.48      | v1_funct_1(X5) != iProver_top
% 6.70/1.48      | v1_funct_1(X4) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15487,plain,
% 6.70/1.48      ( k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4))
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.70/1.48      | v1_funct_1(X2) != iProver_top
% 6.70/1.48      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_15464,c_4056]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_70,plain,
% 6.70/1.48      ( ~ v1_funct_2(X0,X1,X1)
% 6.70/1.48      | ~ v3_funct_2(X0,X1,X1)
% 6.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 6.70/1.48      inference(cnf_transformation,[],[f192]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4058,plain,
% 6.70/1.48      ( v1_funct_2(X0,X1,X1) != iProver_top
% 6.70/1.48      | v3_funct_2(X0,X1,X1) != iProver_top
% 6.70/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 6.70/1.48      | v1_funct_1(X0) != iProver_top
% 6.70/1.48      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12515,plain,
% 6.70/1.48      ( v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v1_funct_1(k2_funct_2(sK3,sK4)) = iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4058]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12531,plain,
% 6.70/1.48      ( v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(light_normalisation,[status(thm)],[c_12515,c_11139]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_19704,plain,
% 6.70/1.48      ( v1_funct_1(X2) != iProver_top
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.70/1.48      | k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4)) ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_15487,c_81,c_82,c_83,c_12531]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_19705,plain,
% 6.70/1.48      ( k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4))
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.70/1.48      | v1_funct_1(X2) != iProver_top ),
% 6.70/1.48      inference(renaming,[status(thm)],[c_19704]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_19716,plain,
% 6.70/1.48      ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k5_relat_1(sK4,k2_funct_1(sK4))
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_19705]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_19731,plain,
% 6.70/1.48      ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(light_normalisation,[status(thm)],[c_19716,c_15370]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_19771,plain,
% 6.70/1.48      ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_19731,c_81]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_11917,plain,
% 6.70/1.48      ( k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4)
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.70/1.48      | v1_funct_1(X2) != iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_4056]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12185,plain,
% 6.70/1.48      ( v1_funct_1(X2) != iProver_top
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.70/1.48      | k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4) ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_11917,c_81]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12186,plain,
% 6.70/1.48      ( k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4)
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.70/1.48      | v1_funct_1(X2) != iProver_top ),
% 6.70/1.48      inference(renaming,[status(thm)],[c_12185]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_14475,plain,
% 6.70/1.48      ( k1_partfun1(X0,X0,sK3,sK3,k2_funct_2(X0,X1),sK4) = k5_relat_1(k2_funct_2(X0,X1),sK4)
% 6.70/1.48      | v1_funct_2(X1,X0,X0) != iProver_top
% 6.70/1.48      | v3_funct_2(X1,X0,X0) != iProver_top
% 6.70/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 6.70/1.48      | v1_funct_1(X1) != iProver_top
% 6.70/1.48      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4061,c_12186]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15597,plain,
% 6.70/1.48      ( k1_partfun1(X0,X0,sK3,sK3,k2_funct_2(X0,X1),sK4) = k5_relat_1(k2_funct_2(X0,X1),sK4)
% 6.70/1.48      | v1_funct_2(X1,X0,X0) != iProver_top
% 6.70/1.48      | v3_funct_2(X1,X0,X0) != iProver_top
% 6.70/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 6.70/1.48      | v1_funct_1(X1) != iProver_top ),
% 6.70/1.48      inference(forward_subsumption_resolution,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_14475,c_4058]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15604,plain,
% 6.70/1.48      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4) = k5_relat_1(k2_funct_2(sK3,sK4),sK4)
% 6.70/1.48      | v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4051,c_15597]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_39,plain,
% 6.70/1.48      ( ~ v2_funct_1(X0)
% 6.70/1.48      | ~ v1_funct_1(X0)
% 6.70/1.48      | ~ v1_relat_1(X0)
% 6.70/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 6.70/1.48      inference(cnf_transformation,[],[f211]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4082,plain,
% 6.70/1.48      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 6.70/1.48      | v2_funct_1(X0) != iProver_top
% 6.70/1.48      | v1_funct_1(X0) != iProver_top
% 6.70/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15266,plain,
% 6.70/1.48      ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(k2_relat_1(sK4))
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top
% 6.70/1.48      | v1_relat_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_15261,c_4082]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15277,plain,
% 6.70/1.48      ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top
% 6.70/1.48      | v1_relat_1(sK4) != iProver_top ),
% 6.70/1.48      inference(light_normalisation,[status(thm)],[c_15266,c_6321]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4647,plain,
% 6.70/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 6.70/1.48      | v1_relat_1(sK4) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_4646]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15366,plain,
% 6.70/1.48      ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(sK3) ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_15277,c_81,c_84,c_4647]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15629,plain,
% 6.70/1.48      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
% 6.70/1.48      | v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.70/1.48      | v1_funct_1(sK4) != iProver_top ),
% 6.70/1.48      inference(light_normalisation,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_15604,c_11139,c_15366]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15480,plain,
% 6.70/1.48      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k5_relat_1(k2_funct_1(sK4),sK4)
% 6.70/1.48      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_15464,c_12186]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15534,plain,
% 6.70/1.48      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
% 6.70/1.48      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 6.70/1.48      inference(light_normalisation,[status(thm)],[c_15480,c_15366]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15907,plain,
% 6.70/1.48      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3) ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_15629,c_81,c_82,c_83,c_12531,c_15534]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_76,negated_conjecture,
% 6.70/1.48      ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
% 6.70/1.48      | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) ),
% 6.70/1.48      inference(cnf_transformation,[],[f206]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4052,plain,
% 6.70/1.48      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) != iProver_top
% 6.70/1.48      | r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_11142,plain,
% 6.70/1.48      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4),k6_partfun1(sK3)) != iProver_top
% 6.70/1.48      | r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
% 6.70/1.48      inference(demodulation,[status(thm)],[c_11139,c_4052]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_15910,plain,
% 6.70/1.48      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top
% 6.70/1.48      | r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
% 6.70/1.48      inference(demodulation,[status(thm)],[c_15907,c_11142]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_19774,plain,
% 6.70/1.48      ( r2_relset_1(sK3,sK3,k6_partfun1(k1_relat_1(sK4)),k6_partfun1(sK3)) != iProver_top
% 6.70/1.48      | r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
% 6.70/1.48      inference(demodulation,[status(thm)],[c_19771,c_15910]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_71,plain,
% 6.70/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 6.70/1.48      inference(cnf_transformation,[],[f196]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4057,plain,
% 6.70/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_49,plain,
% 6.70/1.48      ( r2_relset_1(X0,X1,X2,X2)
% 6.70/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 6.70/1.48      inference(cnf_transformation,[],[f217]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4075,plain,
% 6.70/1.48      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_10946,plain,
% 6.70/1.48      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4057,c_4075]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_20046,plain,
% 6.70/1.48      ( r2_relset_1(sK3,sK3,k6_partfun1(k1_relat_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
% 6.70/1.48      inference(forward_subsumption_resolution,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_19774,c_10946]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_20278,plain,
% 6.70/1.48      ( sK3 = k1_xboole_0
% 6.70/1.48      | r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_15373,c_20046]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_22731,plain,
% 6.70/1.48      ( sK3 = k1_xboole_0 ),
% 6.70/1.48      inference(forward_subsumption_resolution,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_20278,c_10946]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_22748,plain,
% 6.70/1.48      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK4)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 6.70/1.48      inference(demodulation,[status(thm)],[c_22731,c_20046]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_33,plain,
% 6.70/1.48      ( ~ v1_relat_1(X0)
% 6.70/1.48      | k2_relat_1(X0) != k1_xboole_0
% 6.70/1.48      | k1_xboole_0 = X0 ),
% 6.70/1.48      inference(cnf_transformation,[],[f159]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4086,plain,
% 6.70/1.48      ( k2_relat_1(X0) != k1_xboole_0
% 6.70/1.48      | k1_xboole_0 = X0
% 6.70/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_8216,plain,
% 6.70/1.48      ( sK4 = k1_xboole_0
% 6.70/1.48      | sK3 != k1_xboole_0
% 6.70/1.48      | v1_relat_1(sK4) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_6321,c_4086]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_8230,plain,
% 6.70/1.48      ( ~ v1_relat_1(sK4) | sK4 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 6.70/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_8216]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_8665,plain,
% 6.70/1.48      ( sK3 != k1_xboole_0 | sK4 = k1_xboole_0 ),
% 6.70/1.48      inference(global_propositional_subsumption,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_8216,c_77,c_4646,c_8230]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_8666,plain,
% 6.70/1.48      ( sK4 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 6.70/1.48      inference(renaming,[status(thm)],[c_8665]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_22811,plain,
% 6.70/1.48      ( sK4 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 6.70/1.48      inference(demodulation,[status(thm)],[c_22731,c_8666]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_22836,plain,
% 6.70/1.48      ( sK4 = k1_xboole_0 ),
% 6.70/1.48      inference(equality_resolution_simp,[status(thm)],[c_22811]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_23126,plain,
% 6.70/1.48      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 6.70/1.48      inference(light_normalisation,[status(thm)],[c_22748,c_22836]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_6,plain,
% 6.70/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f131]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4104,plain,
% 6.70/1.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_26,plain,
% 6.70/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 6.70/1.48      inference(cnf_transformation,[],[f151]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4092,plain,
% 6.70/1.48      ( v1_xboole_0(X0) != iProver_top
% 6.70/1.48      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_7,plain,
% 6.70/1.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 6.70/1.48      inference(cnf_transformation,[],[f132]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4103,plain,
% 6.70/1.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4953,plain,
% 6.70/1.48      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4092,c_4103]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5301,plain,
% 6.70/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4104,c_4953]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_17,plain,
% 6.70/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 6.70/1.48      inference(cnf_transformation,[],[f142]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4097,plain,
% 6.70/1.48      ( v1_xboole_0(X0) != iProver_top
% 6.70/1.48      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5111,plain,
% 6.70/1.48      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 6.70/1.48      | v1_xboole_0(X1) != iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4097,c_4103]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5690,plain,
% 6.70/1.48      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_4104,c_5111]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_51,plain,
% 6.70/1.48      ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) ),
% 6.70/1.48      inference(cnf_transformation,[],[f214]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4073,plain,
% 6.70/1.48      ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5722,plain,
% 6.70/1.48      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_5690,c_4073]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_13,plain,
% 6.70/1.48      ( r1_xboole_0(X0,k1_xboole_0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f138]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_14,plain,
% 6.70/1.48      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f139]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_994,plain,
% 6.70/1.48      ( ~ r1_tarski(X0,X1)
% 6.70/1.48      | v1_xboole_0(X0)
% 6.70/1.48      | X0 != X2
% 6.70/1.48      | k1_xboole_0 != X1 ),
% 6.70/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_14]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_995,plain,
% 6.70/1.48      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 6.70/1.48      inference(unflattening,[status(thm)],[c_994]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4045,plain,
% 6.70/1.48      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.70/1.48      | v1_xboole_0(X0) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_995]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_6353,plain,
% 6.70/1.48      ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_5722,c_4045]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_6418,plain,
% 6.70/1.48      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 6.70/1.48      inference(superposition,[status(thm)],[c_6353,c_4103]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_23128,plain,
% 6.70/1.48      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.70/1.48      inference(light_normalisation,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_23126,c_5301,c_6418]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_2554,plain,
% 6.70/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.70/1.48      theory(equality) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5184,plain,
% 6.70/1.48      ( ~ r1_tarski(X0,X1)
% 6.70/1.48      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 6.70/1.48      | X2 != X0
% 6.70/1.48      | k2_zfmisc_1(X3,X4) != X1 ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_2554]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5185,plain,
% 6.70/1.48      ( X0 != X1
% 6.70/1.48      | k2_zfmisc_1(X2,X3) != X4
% 6.70/1.48      | r1_tarski(X1,X4) != iProver_top
% 6.70/1.48      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_5184]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5187,plain,
% 6.70/1.48      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 6.70/1.48      | k1_xboole_0 != k1_xboole_0
% 6.70/1.48      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 6.70/1.48      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_5185]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_5124,plain,
% 6.70/1.48      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 6.70/1.48      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_5111]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_21,plain,
% 6.70/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.70/1.48      inference(cnf_transformation,[],[f147]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4640,plain,
% 6.70/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.70/1.48      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4641,plain,
% 6.70/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 6.70/1.48      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_4640]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_4643,plain,
% 6.70/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 6.70/1.48      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_4641]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_12,plain,
% 6.70/1.48      ( r1_tarski(X0,X0) ),
% 6.70/1.48      inference(cnf_transformation,[],[f216]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_263,plain,
% 6.70/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_265,plain,
% 6.70/1.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_263]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_264,plain,
% 6.70/1.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_260,plain,
% 6.70/1.48      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_262,plain,
% 6.70/1.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_260]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_261,plain,
% 6.70/1.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_257,plain,
% 6.70/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 6.70/1.48      | r1_tarski(X0,X1) != iProver_top
% 6.70/1.48      | v1_xboole_0(X0) = iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_259,plain,
% 6.70/1.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 6.70/1.48      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 6.70/1.48      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_257]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_258,plain,
% 6.70/1.48      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 6.70/1.48      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 6.70/1.48      | v1_xboole_0(k1_xboole_0) ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_16,plain,
% 6.70/1.48      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 6.70/1.48      inference(cnf_transformation,[],[f141]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_252,plain,
% 6.70/1.48      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_162,plain,
% 6.70/1.48      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 6.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.70/1.48      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(c_164,plain,
% 6.70/1.48      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 6.70/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.70/1.48      inference(instantiation,[status(thm)],[c_162]) ).
% 6.70/1.48  
% 6.70/1.48  cnf(contradiction,plain,
% 6.70/1.48      ( $false ),
% 6.70/1.48      inference(minisat,
% 6.70/1.48                [status(thm)],
% 6.70/1.48                [c_23128,c_5187,c_5124,c_4643,c_265,c_264,c_262,c_261,
% 6.70/1.48                 c_259,c_258,c_252,c_164]) ).
% 6.70/1.48  
% 6.70/1.48  
% 6.70/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.70/1.48  
% 6.70/1.48  ------                               Statistics
% 6.70/1.48  
% 6.70/1.48  ------ General
% 6.70/1.48  
% 6.70/1.48  abstr_ref_over_cycles:                  0
% 6.70/1.48  abstr_ref_under_cycles:                 0
% 6.70/1.48  gc_basic_clause_elim:                   0
% 6.70/1.48  forced_gc_time:                         0
% 6.70/1.48  parsing_time:                           0.013
% 6.70/1.48  unif_index_cands_time:                  0.
% 6.70/1.48  unif_index_add_time:                    0.
% 6.70/1.48  orderings_time:                         0.
% 6.70/1.48  out_proof_time:                         0.02
% 6.70/1.48  total_time:                             0.533
% 6.70/1.48  num_of_symbols:                         70
% 6.70/1.48  num_of_terms:                           17362
% 6.70/1.48  
% 6.70/1.48  ------ Preprocessing
% 6.70/1.48  
% 6.70/1.48  num_of_splits:                          0
% 6.70/1.48  num_of_split_atoms:                     0
% 6.70/1.48  num_of_reused_defs:                     0
% 6.70/1.48  num_eq_ax_congr_red:                    86
% 6.70/1.48  num_of_sem_filtered_clauses:            1
% 6.70/1.48  num_of_subtypes:                        0
% 6.70/1.48  monotx_restored_types:                  0
% 6.70/1.48  sat_num_of_epr_types:                   0
% 6.70/1.48  sat_num_of_non_cyclic_types:            0
% 6.70/1.48  sat_guarded_non_collapsed_types:        0
% 6.70/1.48  num_pure_diseq_elim:                    0
% 6.70/1.48  simp_replaced_by:                       0
% 6.70/1.48  res_preprocessed:                       345
% 6.70/1.48  prep_upred:                             0
% 6.70/1.48  prep_unflattend:                        28
% 6.70/1.48  smt_new_axioms:                         0
% 6.70/1.48  pred_elim_cands:                        11
% 6.70/1.48  pred_elim:                              4
% 6.70/1.48  pred_elim_cl:                           6
% 6.70/1.48  pred_elim_cycles:                       10
% 6.70/1.48  merged_defs:                            8
% 6.70/1.48  merged_defs_ncl:                        0
% 6.70/1.48  bin_hyper_res:                          10
% 6.70/1.48  prep_cycles:                            4
% 6.70/1.48  pred_elim_time:                         0.02
% 6.70/1.48  splitting_time:                         0.
% 6.70/1.48  sem_filter_time:                        0.
% 6.70/1.48  monotx_time:                            0.001
% 6.70/1.48  subtype_inf_time:                       0.
% 6.70/1.48  
% 6.70/1.48  ------ Problem properties
% 6.70/1.48  
% 6.70/1.48  clauses:                                72
% 6.70/1.48  conjectures:                            5
% 6.70/1.48  epr:                                    14
% 6.70/1.48  horn:                                   63
% 6.70/1.48  ground:                                 6
% 6.70/1.48  unary:                                  13
% 6.70/1.48  binary:                                 29
% 6.70/1.48  lits:                                   189
% 6.70/1.48  lits_eq:                                41
% 6.70/1.48  fd_pure:                                0
% 6.70/1.48  fd_pseudo:                              0
% 6.70/1.48  fd_cond:                                8
% 6.70/1.48  fd_pseudo_cond:                         5
% 6.70/1.48  ac_symbols:                             0
% 6.70/1.48  
% 6.70/1.48  ------ Propositional Solver
% 6.70/1.48  
% 6.70/1.48  prop_solver_calls:                      29
% 6.70/1.48  prop_fast_solver_calls:                 2684
% 6.70/1.48  smt_solver_calls:                       0
% 6.70/1.48  smt_fast_solver_calls:                  0
% 6.70/1.48  prop_num_of_clauses:                    7458
% 6.70/1.48  prop_preprocess_simplified:             19058
% 6.70/1.48  prop_fo_subsumed:                       86
% 6.70/1.48  prop_solver_time:                       0.
% 6.70/1.48  smt_solver_time:                        0.
% 6.70/1.48  smt_fast_solver_time:                   0.
% 6.70/1.48  prop_fast_solver_time:                  0.
% 6.70/1.48  prop_unsat_core_time:                   0.001
% 6.70/1.48  
% 6.70/1.48  ------ QBF
% 6.70/1.48  
% 6.70/1.48  qbf_q_res:                              0
% 6.70/1.48  qbf_num_tautologies:                    0
% 6.70/1.48  qbf_prep_cycles:                        0
% 6.70/1.48  
% 6.70/1.48  ------ BMC1
% 6.70/1.48  
% 6.70/1.48  bmc1_current_bound:                     -1
% 6.70/1.48  bmc1_last_solved_bound:                 -1
% 6.70/1.48  bmc1_unsat_core_size:                   -1
% 6.70/1.48  bmc1_unsat_core_parents_size:           -1
% 6.70/1.48  bmc1_merge_next_fun:                    0
% 6.70/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.70/1.48  
% 6.70/1.48  ------ Instantiation
% 6.70/1.48  
% 6.70/1.48  inst_num_of_clauses:                    1882
% 6.70/1.48  inst_num_in_passive:                    770
% 6.70/1.48  inst_num_in_active:                     824
% 6.70/1.48  inst_num_in_unprocessed:                290
% 6.70/1.48  inst_num_of_loops:                      1170
% 6.70/1.48  inst_num_of_learning_restarts:          0
% 6.70/1.48  inst_num_moves_active_passive:          343
% 6.70/1.48  inst_lit_activity:                      0
% 6.70/1.48  inst_lit_activity_moves:                0
% 6.70/1.48  inst_num_tautologies:                   0
% 6.70/1.48  inst_num_prop_implied:                  0
% 6.70/1.48  inst_num_existing_simplified:           0
% 6.70/1.48  inst_num_eq_res_simplified:             0
% 6.70/1.48  inst_num_child_elim:                    0
% 6.70/1.48  inst_num_of_dismatching_blockings:      971
% 6.70/1.48  inst_num_of_non_proper_insts:           2138
% 6.70/1.48  inst_num_of_duplicates:                 0
% 6.70/1.48  inst_inst_num_from_inst_to_res:         0
% 6.70/1.48  inst_dismatching_checking_time:         0.
% 6.70/1.48  
% 6.70/1.48  ------ Resolution
% 6.70/1.48  
% 6.70/1.48  res_num_of_clauses:                     0
% 6.70/1.48  res_num_in_passive:                     0
% 6.70/1.48  res_num_in_active:                      0
% 6.70/1.48  res_num_of_loops:                       349
% 6.70/1.48  res_forward_subset_subsumed:            38
% 6.70/1.48  res_backward_subset_subsumed:           4
% 6.70/1.48  res_forward_subsumed:                   0
% 6.70/1.48  res_backward_subsumed:                  0
% 6.70/1.48  res_forward_subsumption_resolution:     1
% 6.70/1.48  res_backward_subsumption_resolution:    0
% 6.70/1.48  res_clause_to_clause_subsumption:       1321
% 6.70/1.48  res_orphan_elimination:                 0
% 6.70/1.48  res_tautology_del:                      38
% 6.70/1.48  res_num_eq_res_simplified:              0
% 6.70/1.48  res_num_sel_changes:                    0
% 6.70/1.48  res_moves_from_active_to_pass:          0
% 6.70/1.48  
% 6.70/1.48  ------ Superposition
% 6.70/1.48  
% 6.70/1.48  sup_time_total:                         0.
% 6.70/1.48  sup_time_generating:                    0.
% 6.70/1.48  sup_time_sim_full:                      0.
% 6.70/1.48  sup_time_sim_immed:                     0.
% 6.70/1.48  
% 6.70/1.48  sup_num_of_clauses:                     361
% 6.70/1.48  sup_num_in_active:                      129
% 6.70/1.48  sup_num_in_passive:                     232
% 6.70/1.48  sup_num_of_loops:                       233
% 6.70/1.48  sup_fw_superposition:                   327
% 6.70/1.48  sup_bw_superposition:                   184
% 6.70/1.48  sup_immediate_simplified:               192
% 6.70/1.48  sup_given_eliminated:                   1
% 6.70/1.48  comparisons_done:                       0
% 6.70/1.48  comparisons_avoided:                    30
% 6.70/1.48  
% 6.70/1.48  ------ Simplifications
% 6.70/1.48  
% 6.70/1.48  
% 6.70/1.48  sim_fw_subset_subsumed:                 14
% 6.70/1.48  sim_bw_subset_subsumed:                 12
% 6.70/1.48  sim_fw_subsumed:                        11
% 6.70/1.48  sim_bw_subsumed:                        2
% 6.70/1.48  sim_fw_subsumption_res:                 5
% 6.70/1.48  sim_bw_subsumption_res:                 0
% 6.70/1.48  sim_tautology_del:                      8
% 6.70/1.48  sim_eq_tautology_del:                   59
% 6.70/1.48  sim_eq_res_simp:                        2
% 6.70/1.48  sim_fw_demodulated:                     44
% 6.70/1.48  sim_bw_demodulated:                     111
% 6.70/1.48  sim_light_normalised:                   177
% 6.70/1.48  sim_joinable_taut:                      0
% 6.70/1.48  sim_joinable_simp:                      0
% 6.70/1.48  sim_ac_normalised:                      0
% 6.70/1.48  sim_smt_subsumption:                    0
% 6.70/1.48  
%------------------------------------------------------------------------------
