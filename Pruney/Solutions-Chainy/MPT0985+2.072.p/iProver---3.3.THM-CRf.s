%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:34 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  200 (29435 expanded)
%              Number of clauses        :  134 (9928 expanded)
%              Number of leaves         :   15 (5522 expanded)
%              Depth                    :   33
%              Number of atoms          :  573 (153515 expanded)
%              Number of equality atoms :  327 (32007 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f55,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
      & k2_relset_1(sK2,sK3,sK4) = sK3
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f55])).

fof(f95,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f99,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f106,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_692,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_40])).

cnf(c_693,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_695,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_39])).

cnf(c_1397,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1404,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3810,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1397,c_1404])).

cnf(c_3996,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_695,c_3810])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1403,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3043,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1397,c_1403])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3055,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3043,c_37])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1405,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2599,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1397,c_1405])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_424,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_425,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_427,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_41])).

cnf(c_1395,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_2644,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2599,c_1395])).

cnf(c_3080,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3055,c_2644])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1398,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3261,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k2_relat_1(k2_funct_1(sK4))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_1398])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_438,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_439,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_441,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_41])).

cnf(c_1394,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_2645,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2599,c_1394])).

cnf(c_3270,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3261,c_2645])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1724,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1725,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1737,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1738,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1737])).

cnf(c_1755,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1756,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1755])).

cnf(c_4148,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3270,c_42,c_44,c_1725,c_1738,c_1756])).

cnf(c_4156,plain,
    ( k1_relset_1(sK3,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_4148,c_1404])).

cnf(c_4162,plain,
    ( k1_relset_1(sK3,k1_relat_1(sK4),k2_funct_1(sK4)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_4156,c_3080])).

cnf(c_4178,plain,
    ( k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3996,c_4162])).

cnf(c_34,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_36,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_716,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK4) != X0
    | k2_relat_1(X0) != sK2
    | k1_relat_1(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_36])).

cnf(c_717,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_729,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_717,c_19])).

cnf(c_1383,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_718,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_1866,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1383,c_42,c_44,c_718,c_1725,c_1738,c_1756])).

cnf(c_1867,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1866])).

cnf(c_2659,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | k2_relat_1(sK4) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2644,c_1867])).

cnf(c_2753,plain,
    ( k2_relat_1(sK4) != sK3
    | k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2659,c_2645])).

cnf(c_3078,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3055,c_2753])).

cnf(c_3092,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3078])).

cnf(c_4060,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3996,c_3092])).

cnf(c_4153,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3996,c_4148])).

cnf(c_4346,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4178,c_4060,c_4153])).

cnf(c_4350,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4346,c_4148])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1410,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2661,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2644,c_1410])).

cnf(c_2673,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2661,c_42,c_44,c_1738,c_1756])).

cnf(c_2674,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2673])).

cnf(c_2675,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2674,c_2645])).

cnf(c_3079,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3055,c_2675])).

cnf(c_4359,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4346,c_3079])).

cnf(c_4426,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4359])).

cnf(c_4451,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4350,c_4426])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4453,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4451,c_5])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK4) != X0
    | sK2 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_610,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_1388,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_1612,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1388,c_5])).

cnf(c_2045,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | sK3 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1612,c_42,c_44,c_1725,c_1756])).

cnf(c_2046,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2045])).

cnf(c_4364,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4346,c_2046])).

cnf(c_4403,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4364])).

cnf(c_4407,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4403,c_5])).

cnf(c_4456,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4453,c_4407])).

cnf(c_4356,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4346,c_3092])).

cnf(c_4435,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4356,c_4426])).

cnf(c_4438,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4435,c_5])).

cnf(c_4457,plain,
    ( sK2 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4453,c_4438])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != X1
    | sK3 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_40])).

cnf(c_555,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_1390,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1529,plain,
    ( sK2 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1390,c_4])).

cnf(c_4363,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4346,c_1529])).

cnf(c_4410,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4363])).

cnf(c_4371,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4346,c_1397])).

cnf(c_4376,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4371,c_4])).

cnf(c_4414,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4410,c_4376])).

cnf(c_4460,plain,
    ( sK4 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4457,c_4414])).

cnf(c_4490,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4456,c_4460])).

cnf(c_2881,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2645,c_1398])).

cnf(c_2895,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2881,c_2644])).

cnf(c_5173,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2895,c_42,c_44,c_1725,c_1738,c_1756])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1412,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5179,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4))) != iProver_top
    | v1_xboole_0(k2_funct_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5173,c_1412])).

cnf(c_4466,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4460,c_4426])).

cnf(c_4361,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4346,c_3055])).

cnf(c_4468,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4460,c_4361])).

cnf(c_6145,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5179,c_4460,c_4466,c_4468])).

cnf(c_6146,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6145,c_5])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1415,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6149,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6146,c_1415])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1414,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6151,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6149,c_1414])).

cnf(c_6660,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4490,c_6151])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1413,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3813,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1404])).

cnf(c_3961,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1413,c_3813])).

cnf(c_6116,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3961,c_4466])).

cnf(c_6661,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6660,c_6116])).

cnf(c_6662,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6661])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:37 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.99  
% 3.02/0.99  ------  iProver source info
% 3.02/0.99  
% 3.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.99  git: non_committed_changes: false
% 3.02/0.99  git: last_make_outside_of_git: false
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     num_symb
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       true
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  ------ Parsing...
% 3.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.99  ------ Proving...
% 3.02/0.99  ------ Problem Properties 
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  clauses                                 42
% 3.02/0.99  conjectures                             3
% 3.02/0.99  EPR                                     3
% 3.02/0.99  Horn                                    34
% 3.02/0.99  unary                                   14
% 3.02/0.99  binary                                  9
% 3.02/0.99  lits                                    101
% 3.02/0.99  lits eq                                 46
% 3.02/0.99  fd_pure                                 0
% 3.02/0.99  fd_pseudo                               0
% 3.02/0.99  fd_cond                                 4
% 3.02/0.99  fd_pseudo_cond                          0
% 3.02/0.99  AC symbols                              0
% 3.02/0.99  
% 3.02/0.99  ------ Schedule dynamic 5 is on 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  Current options:
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     none
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       false
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ Proving...
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS status Theorem for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99   Resolution empty clause
% 3.02/0.99  
% 3.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  fof(f16,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f39,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f16])).
% 3.02/0.99  
% 3.02/0.99  fof(f40,plain,(
% 3.02/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(flattening,[],[f39])).
% 3.02/0.99  
% 3.02/0.99  fof(f52,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(nnf_transformation,[],[f40])).
% 3.02/0.99  
% 3.02/0.99  fof(f79,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f52])).
% 3.02/0.99  
% 3.02/0.99  fof(f21,conjecture,(
% 3.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f22,negated_conjecture,(
% 3.02/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.02/0.99    inference(negated_conjecture,[],[f21])).
% 3.02/0.99  
% 3.02/0.99  fof(f43,plain,(
% 3.02/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.02/0.99    inference(ennf_transformation,[],[f22])).
% 3.02/0.99  
% 3.02/0.99  fof(f44,plain,(
% 3.02/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.02/0.99    inference(flattening,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f55,plain,(
% 3.02/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f56,plain,(
% 3.02/0.99    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f55])).
% 3.02/0.99  
% 3.02/0.99  fof(f95,plain,(
% 3.02/0.99    v1_funct_2(sK4,sK2,sK3)),
% 3.02/0.99    inference(cnf_transformation,[],[f56])).
% 3.02/0.99  
% 3.02/0.99  fof(f96,plain,(
% 3.02/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.02/0.99    inference(cnf_transformation,[],[f56])).
% 3.02/0.99  
% 3.02/0.99  fof(f14,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f37,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f14])).
% 3.02/0.99  
% 3.02/0.99  fof(f77,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f37])).
% 3.02/0.99  
% 3.02/0.99  fof(f15,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f38,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f15])).
% 3.02/0.99  
% 3.02/0.99  fof(f78,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f38])).
% 3.02/0.99  
% 3.02/0.99  fof(f98,plain,(
% 3.02/0.99    k2_relset_1(sK2,sK3,sK4) = sK3),
% 3.02/0.99    inference(cnf_transformation,[],[f56])).
% 3.02/0.99  
% 3.02/0.99  fof(f13,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f36,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f13])).
% 3.02/0.99  
% 3.02/0.99  fof(f76,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f36])).
% 3.02/0.99  
% 3.02/0.99  fof(f12,axiom,(
% 3.02/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f34,plain,(
% 3.02/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f12])).
% 3.02/0.99  
% 3.02/0.99  fof(f35,plain,(
% 3.02/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/0.99    inference(flattening,[],[f34])).
% 3.02/0.99  
% 3.02/0.99  fof(f74,plain,(
% 3.02/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f35])).
% 3.02/0.99  
% 3.02/0.99  fof(f97,plain,(
% 3.02/0.99    v2_funct_1(sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f56])).
% 3.02/0.99  
% 3.02/0.99  fof(f94,plain,(
% 3.02/0.99    v1_funct_1(sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f56])).
% 3.02/0.99  
% 3.02/0.99  fof(f20,axiom,(
% 3.02/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f41,plain,(
% 3.02/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f20])).
% 3.02/0.99  
% 3.02/0.99  fof(f42,plain,(
% 3.02/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/0.99    inference(flattening,[],[f41])).
% 3.02/0.99  
% 3.02/0.99  fof(f93,plain,(
% 3.02/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f42])).
% 3.02/0.99  
% 3.02/0.99  fof(f75,plain,(
% 3.02/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f35])).
% 3.02/0.99  
% 3.02/0.99  fof(f10,axiom,(
% 3.02/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f32,plain,(
% 3.02/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f10])).
% 3.02/0.99  
% 3.02/0.99  fof(f33,plain,(
% 3.02/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/0.99    inference(flattening,[],[f32])).
% 3.02/0.99  
% 3.02/0.99  fof(f71,plain,(
% 3.02/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f70,plain,(
% 3.02/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f92,plain,(
% 3.02/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f42])).
% 3.02/0.99  
% 3.02/0.99  fof(f99,plain,(
% 3.02/0.99    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 3.02/0.99    inference(cnf_transformation,[],[f56])).
% 3.02/0.99  
% 3.02/0.99  fof(f9,axiom,(
% 3.02/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f31,plain,(
% 3.02/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.02/0.99    inference(ennf_transformation,[],[f9])).
% 3.02/0.99  
% 3.02/0.99  fof(f51,plain,(
% 3.02/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.02/0.99    inference(nnf_transformation,[],[f31])).
% 3.02/0.99  
% 3.02/0.99  fof(f68,plain,(
% 3.02/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f51])).
% 3.02/0.99  
% 3.02/0.99  fof(f4,axiom,(
% 3.02/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f49,plain,(
% 3.02/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.02/0.99    inference(nnf_transformation,[],[f4])).
% 3.02/0.99  
% 3.02/0.99  fof(f50,plain,(
% 3.02/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.02/0.99    inference(flattening,[],[f49])).
% 3.02/0.99  
% 3.02/0.99  fof(f62,plain,(
% 3.02/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.02/0.99    inference(cnf_transformation,[],[f50])).
% 3.02/0.99  
% 3.02/0.99  fof(f103,plain,(
% 3.02/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.02/0.99    inference(equality_resolution,[],[f62])).
% 3.02/0.99  
% 3.02/0.99  fof(f82,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f52])).
% 3.02/0.99  
% 3.02/0.99  fof(f107,plain,(
% 3.02/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.02/0.99    inference(equality_resolution,[],[f82])).
% 3.02/0.99  
% 3.02/0.99  fof(f83,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f52])).
% 3.02/0.99  
% 3.02/0.99  fof(f106,plain,(
% 3.02/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.02/0.99    inference(equality_resolution,[],[f83])).
% 3.02/0.99  
% 3.02/0.99  fof(f63,plain,(
% 3.02/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.02/0.99    inference(cnf_transformation,[],[f50])).
% 3.02/0.99  
% 3.02/0.99  fof(f102,plain,(
% 3.02/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.02/0.99    inference(equality_resolution,[],[f63])).
% 3.02/0.99  
% 3.02/0.99  fof(f6,axiom,(
% 3.02/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f27,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.02/0.99    inference(ennf_transformation,[],[f6])).
% 3.02/0.99  
% 3.02/0.99  fof(f65,plain,(
% 3.02/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f27])).
% 3.02/0.99  
% 3.02/0.99  fof(f2,axiom,(
% 3.02/0.99    v1_xboole_0(k1_xboole_0)),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f59,plain,(
% 3.02/0.99    v1_xboole_0(k1_xboole_0)),
% 3.02/0.99    inference(cnf_transformation,[],[f2])).
% 3.02/0.99  
% 3.02/0.99  fof(f3,axiom,(
% 3.02/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f26,plain,(
% 3.02/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.02/0.99    inference(ennf_transformation,[],[f3])).
% 3.02/0.99  
% 3.02/0.99  fof(f60,plain,(
% 3.02/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f26])).
% 3.02/0.99  
% 3.02/0.99  fof(f5,axiom,(
% 3.02/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f64,plain,(
% 3.02/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f5])).
% 3.02/0.99  
% 3.02/0.99  cnf(c_27,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.02/0.99      | k1_xboole_0 = X2 ),
% 3.02/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_40,negated_conjecture,
% 3.02/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.02/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_692,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.02/0.99      | sK2 != X1
% 3.02/0.99      | sK3 != X2
% 3.02/0.99      | sK4 != X0
% 3.02/0.99      | k1_xboole_0 = X2 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_40]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_693,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.02/0.99      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.02/0.99      | k1_xboole_0 = sK3 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_692]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_39,negated_conjecture,
% 3.02/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.02/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_695,plain,
% 3.02/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.02/0.99      inference(global_propositional_subsumption,[status(thm)],[c_693,c_39]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1397,plain,
% 3.02/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_20,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1404,plain,
% 3.02/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3810,plain,
% 3.02/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1397,c_1404]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3996,plain,
% 3.02/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_695,c_3810]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_21,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1403,plain,
% 3.02/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3043,plain,
% 3.02/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1397,c_1403]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_37,negated_conjecture,
% 3.02/0.99      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.02/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3055,plain,
% 3.02/0.99      ( k2_relat_1(sK4) = sK3 ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_3043,c_37]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_19,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1405,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2599,plain,
% 3.02/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1397,c_1405]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_18,plain,
% 3.02/0.99      ( ~ v2_funct_1(X0)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v1_relat_1(X0)
% 3.02/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_38,negated_conjecture,
% 3.02/0.99      ( v2_funct_1(sK4) ),
% 3.02/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_424,plain,
% 3.02/0.99      ( ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v1_relat_1(X0)
% 3.02/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.02/0.99      | sK4 != X0 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_425,plain,
% 3.02/0.99      ( ~ v1_funct_1(sK4)
% 3.02/0.99      | ~ v1_relat_1(sK4)
% 3.02/0.99      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_424]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_41,negated_conjecture,
% 3.02/0.99      ( v1_funct_1(sK4) ),
% 3.02/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_427,plain,
% 3.02/0.99      ( ~ v1_relat_1(sK4) | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.02/0.99      inference(global_propositional_subsumption,[status(thm)],[c_425,c_41]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1395,plain,
% 3.02/0.99      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.02/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2644,plain,
% 3.02/0.99      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2599,c_1395]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3080,plain,
% 3.02/0.99      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_3055,c_2644]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_33,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1398,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top
% 3.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3261,plain,
% 3.02/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k2_relat_1(k2_funct_1(sK4))))) = iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.02/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3080,c_1398]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_17,plain,
% 3.02/0.99      ( ~ v2_funct_1(X0)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v1_relat_1(X0)
% 3.02/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_438,plain,
% 3.02/0.99      ( ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v1_relat_1(X0)
% 3.02/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.02/0.99      | sK4 != X0 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_439,plain,
% 3.02/0.99      ( ~ v1_funct_1(sK4)
% 3.02/0.99      | ~ v1_relat_1(sK4)
% 3.02/0.99      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_438]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_441,plain,
% 3.02/0.99      ( ~ v1_relat_1(sK4) | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.02/0.99      inference(global_propositional_subsumption,[status(thm)],[c_439,c_41]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1394,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.02/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2645,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2599,c_1394]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3270,plain,
% 3.02/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.02/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_3261,c_2645]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_42,plain,
% 3.02/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_44,plain,
% 3.02/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_13,plain,
% 3.02/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1724,plain,
% 3.02/0.99      ( v1_funct_1(k2_funct_1(sK4)) | ~ v1_funct_1(sK4) | ~ v1_relat_1(sK4) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1725,plain,
% 3.02/0.99      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 3.02/0.99      | v1_funct_1(sK4) != iProver_top
% 3.02/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1724]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_14,plain,
% 3.02/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.02/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1737,plain,
% 3.02/0.99      ( ~ v1_funct_1(sK4) | v1_relat_1(k2_funct_1(sK4)) | ~ v1_relat_1(sK4) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1738,plain,
% 3.02/0.99      ( v1_funct_1(sK4) != iProver_top
% 3.02/0.99      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 3.02/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1737]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1755,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.02/0.99      | v1_relat_1(sK4) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1756,plain,
% 3.02/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.02/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1755]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4148,plain,
% 3.02/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_3270,c_42,c_44,c_1725,c_1738,c_1756]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4156,plain,
% 3.02/0.99      ( k1_relset_1(sK3,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_4148,c_1404]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4162,plain,
% 3.02/0.99      ( k1_relset_1(sK3,k1_relat_1(sK4),k2_funct_1(sK4)) = sK3 ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_4156,c_3080]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4178,plain,
% 3.02/0.99      ( k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = sK3 | sK3 = k1_xboole_0 ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3996,c_4162]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_34,plain,
% 3.02/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_36,negated_conjecture,
% 3.02/0.99      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 3.02/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.02/0.99      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 3.02/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_716,plain,
% 3.02/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.02/0.99      | ~ v1_relat_1(X0)
% 3.02/0.99      | k2_funct_1(sK4) != X0
% 3.02/0.99      | k2_relat_1(X0) != sK2
% 3.02/0.99      | k1_relat_1(X0) != sK3 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_36]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_717,plain,
% 3.02/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.02/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.02/0.99      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.02/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.02/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_716]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_729,plain,
% 3.02/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.02/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.02/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.02/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 3.02/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_717,c_19]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1383,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.02/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_718,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.02/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.02/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1866,plain,
% 3.02/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.02/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.02/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_1383,c_42,c_44,c_718,c_1725,c_1738,c_1756]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1867,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.02/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_1866]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2659,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.02/0.99      | k2_relat_1(sK4) != sK3
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_2644,c_1867]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2753,plain,
% 3.02/0.99      ( k2_relat_1(sK4) != sK3
% 3.02/0.99      | k1_relat_1(sK4) != sK2
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_2659,c_2645]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3078,plain,
% 3.02/0.99      ( k1_relat_1(sK4) != sK2
% 3.02/0.99      | sK3 != sK3
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_3055,c_2753]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3092,plain,
% 3.02/0.99      ( k1_relat_1(sK4) != sK2
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.02/0.99      inference(equality_resolution_simp,[status(thm)],[c_3078]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4060,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3996,c_3092]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4153,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3996,c_4148]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4346,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4178,c_4060,c_4153]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4350,plain,
% 3.02/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4346,c_4148]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_12,plain,
% 3.02/0.99      ( ~ v1_relat_1(X0)
% 3.02/0.99      | k2_relat_1(X0) = k1_xboole_0
% 3.02/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1410,plain,
% 3.02/0.99      ( k2_relat_1(X0) = k1_xboole_0
% 3.02/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2661,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.02/0.99      | k2_relat_1(sK4) != k1_xboole_0
% 3.02/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2644,c_1410]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2673,plain,
% 3.02/0.99      ( k2_relat_1(sK4) != k1_xboole_0
% 3.02/0.99      | k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_2661,c_42,c_44,c_1738,c_1756]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2674,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.02/0.99      | k2_relat_1(sK4) != k1_xboole_0 ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_2673]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2675,plain,
% 3.02/0.99      ( k2_relat_1(sK4) != k1_xboole_0 | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_2674,c_2645]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3079,plain,
% 3.02/0.99      ( k1_relat_1(sK4) = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_3055,c_2675]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4359,plain,
% 3.02/0.99      ( k1_relat_1(sK4) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4346,c_3079]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4426,plain,
% 3.02/0.99      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.02/0.99      inference(equality_resolution_simp,[status(thm)],[c_4359]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4451,plain,
% 3.02/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_4350,c_4426]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5,plain,
% 3.02/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4453,plain,
% 3.02/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4451,c_5]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_24,plain,
% 3.02/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.02/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_609,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.02/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.02/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.02/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.02/0.99      | k2_funct_1(sK4) != X0
% 3.02/0.99      | sK2 != X1
% 3.02/0.99      | sK3 != k1_xboole_0 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_610,plain,
% 3.02/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.02/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.02/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.02/0.99      | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.02/0.99      | sK3 != k1_xboole_0 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_609]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1388,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.02/0.99      | sK3 != k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1612,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.02/0.99      | sK3 != k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_1388,c_5]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2045,plain,
% 3.02/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.02/0.99      | sK3 != k1_xboole_0
% 3.02/0.99      | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_1612,c_42,c_44,c_1725,c_1756]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2046,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.02/0.99      | sK3 != k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_2045]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4364,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.02/0.99      | k1_xboole_0 != k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4346,c_2046]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4403,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/0.99      inference(equality_resolution_simp,[status(thm)],[c_4364]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4407,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4403,c_5]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4456,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
% 3.02/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_4453,c_4407]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4356,plain,
% 3.02/0.99      ( k1_relat_1(sK4) != sK2
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4346,c_3092]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4435,plain,
% 3.02/0.99      ( sK2 != k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_4356,c_4426]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4438,plain,
% 3.02/0.99      ( sK2 != k1_xboole_0
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4435,c_5]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4457,plain,
% 3.02/0.99      ( sK2 != k1_xboole_0 ),
% 3.02/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_4453,c_4438]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_23,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.02/0.99      | k1_xboole_0 = X1
% 3.02/0.99      | k1_xboole_0 = X0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_554,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.02/0.99      | sK2 != X1
% 3.02/0.99      | sK3 != k1_xboole_0
% 3.02/0.99      | sK4 != X0
% 3.02/0.99      | k1_xboole_0 = X0
% 3.02/0.99      | k1_xboole_0 = X1 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_40]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_555,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.02/0.99      | sK3 != k1_xboole_0
% 3.02/0.99      | k1_xboole_0 = sK2
% 3.02/0.99      | k1_xboole_0 = sK4 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_554]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1390,plain,
% 3.02/0.99      ( sK3 != k1_xboole_0
% 3.02/0.99      | k1_xboole_0 = sK2
% 3.02/0.99      | k1_xboole_0 = sK4
% 3.02/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4,plain,
% 3.02/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1529,plain,
% 3.02/0.99      ( sK2 = k1_xboole_0
% 3.02/0.99      | sK3 != k1_xboole_0
% 3.02/0.99      | sK4 = k1_xboole_0
% 3.02/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_1390,c_4]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4363,plain,
% 3.02/0.99      ( sK2 = k1_xboole_0
% 3.02/0.99      | sK4 = k1_xboole_0
% 3.02/0.99      | k1_xboole_0 != k1_xboole_0
% 3.02/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4346,c_1529]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4410,plain,
% 3.02/1.00      ( sK2 = k1_xboole_0
% 3.02/1.00      | sK4 = k1_xboole_0
% 3.02/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_4363]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4371,plain,
% 3.02/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_4346,c_1397]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4376,plain,
% 3.02/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_4371,c_4]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4414,plain,
% 3.02/1.00      ( sK2 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4410,c_4376]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4460,plain,
% 3.02/1.00      ( sK4 = k1_xboole_0 ),
% 3.02/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_4457,c_4414]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4490,plain,
% 3.02/1.00      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_4456,c_4460]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2881,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2645,c_1398]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2895,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_2881,c_2644]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5173,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2895,c_42,c_44,c_1725,c_1738,c_1756]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_8,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/1.00      | ~ v1_xboole_0(X1)
% 3.02/1.00      | v1_xboole_0(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1412,plain,
% 3.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.02/1.00      | v1_xboole_0(X1) != iProver_top
% 3.02/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5179,plain,
% 3.02/1.00      ( v1_xboole_0(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4))) != iProver_top
% 3.02/1.00      | v1_xboole_0(k2_funct_1(sK4)) = iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_5173,c_1412]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4466,plain,
% 3.02/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_4460,c_4426]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4361,plain,
% 3.02/1.00      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_4346,c_3055]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4468,plain,
% 3.02/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_4460,c_4361]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6145,plain,
% 3.02/1.00      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.02/1.00      | v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 3.02/1.00      inference(light_normalisation,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_5179,c_4460,c_4466,c_4468]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6146,plain,
% 3.02/1.00      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top
% 3.02/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_6145,c_5]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2,plain,
% 3.02/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1415,plain,
% 3.02/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6149,plain,
% 3.02/1.00      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 3.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6146,c_1415]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3,plain,
% 3.02/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.02/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1414,plain,
% 3.02/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6151,plain,
% 3.02/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_6149,c_1414]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6660,plain,
% 3.02/1.00      ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) != k1_xboole_0 ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_4490,c_6151]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_7,plain,
% 3.02/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1413,plain,
% 3.02/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3813,plain,
% 3.02/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.02/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_5,c_1404]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3961,plain,
% 3.02/1.00      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1413,c_3813]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6116,plain,
% 3.02/1.00      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_3961,c_4466]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6661,plain,
% 3.02/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_6660,c_6116]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6662,plain,
% 3.02/1.00      ( $false ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_6661]) ).
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  ------                               Statistics
% 3.02/1.00  
% 3.02/1.00  ------ General
% 3.02/1.00  
% 3.02/1.00  abstr_ref_over_cycles:                  0
% 3.02/1.00  abstr_ref_under_cycles:                 0
% 3.02/1.00  gc_basic_clause_elim:                   0
% 3.02/1.00  forced_gc_time:                         0
% 3.02/1.00  parsing_time:                           0.01
% 3.02/1.00  unif_index_cands_time:                  0.
% 3.02/1.00  unif_index_add_time:                    0.
% 3.02/1.00  orderings_time:                         0.
% 3.02/1.00  out_proof_time:                         0.011
% 3.02/1.00  total_time:                             0.213
% 3.02/1.00  num_of_symbols:                         52
% 3.02/1.00  num_of_terms:                           4935
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing
% 3.02/1.00  
% 3.02/1.00  num_of_splits:                          0
% 3.02/1.00  num_of_split_atoms:                     0
% 3.02/1.00  num_of_reused_defs:                     0
% 3.02/1.00  num_eq_ax_congr_red:                    9
% 3.02/1.00  num_of_sem_filtered_clauses:            1
% 3.02/1.00  num_of_subtypes:                        0
% 3.02/1.00  monotx_restored_types:                  0
% 3.02/1.00  sat_num_of_epr_types:                   0
% 3.02/1.00  sat_num_of_non_cyclic_types:            0
% 3.02/1.00  sat_guarded_non_collapsed_types:        0
% 3.02/1.00  num_pure_diseq_elim:                    0
% 3.02/1.00  simp_replaced_by:                       0
% 3.02/1.00  res_preprocessed:                       154
% 3.02/1.00  prep_upred:                             0
% 3.02/1.00  prep_unflattend:                        60
% 3.02/1.00  smt_new_axioms:                         0
% 3.02/1.00  pred_elim_cands:                        7
% 3.02/1.00  pred_elim:                              3
% 3.02/1.00  pred_elim_cl:                           -1
% 3.02/1.00  pred_elim_cycles:                       4
% 3.02/1.00  merged_defs:                            0
% 3.02/1.00  merged_defs_ncl:                        0
% 3.02/1.00  bin_hyper_res:                          0
% 3.02/1.00  prep_cycles:                            3
% 3.02/1.00  pred_elim_time:                         0.009
% 3.02/1.00  splitting_time:                         0.
% 3.02/1.00  sem_filter_time:                        0.
% 3.02/1.00  monotx_time:                            0.
% 3.02/1.00  subtype_inf_time:                       0.
% 3.02/1.00  
% 3.02/1.00  ------ Problem properties
% 3.02/1.00  
% 3.02/1.00  clauses:                                42
% 3.02/1.00  conjectures:                            3
% 3.02/1.00  epr:                                    3
% 3.02/1.00  horn:                                   34
% 3.02/1.00  ground:                                 15
% 3.02/1.00  unary:                                  14
% 3.02/1.00  binary:                                 9
% 3.02/1.00  lits:                                   101
% 3.02/1.00  lits_eq:                                46
% 3.02/1.00  fd_pure:                                0
% 3.02/1.00  fd_pseudo:                              0
% 3.02/1.00  fd_cond:                                4
% 3.02/1.00  fd_pseudo_cond:                         0
% 3.02/1.00  ac_symbols:                             0
% 3.02/1.00  
% 3.02/1.00  ------ Propositional Solver
% 3.02/1.00  
% 3.02/1.00  prop_solver_calls:                      23
% 3.02/1.00  prop_fast_solver_calls:                 1091
% 3.02/1.00  smt_solver_calls:                       0
% 3.02/1.00  smt_fast_solver_calls:                  0
% 3.02/1.00  prop_num_of_clauses:                    2232
% 3.02/1.00  prop_preprocess_simplified:             6720
% 3.02/1.00  prop_fo_subsumed:                       31
% 3.02/1.00  prop_solver_time:                       0.
% 3.02/1.00  smt_solver_time:                        0.
% 3.02/1.00  smt_fast_solver_time:                   0.
% 3.02/1.00  prop_fast_solver_time:                  0.
% 3.02/1.00  prop_unsat_core_time:                   0.
% 3.02/1.00  
% 3.02/1.00  ------ QBF
% 3.02/1.00  
% 3.02/1.00  qbf_q_res:                              0
% 3.02/1.00  qbf_num_tautologies:                    0
% 3.02/1.00  qbf_prep_cycles:                        0
% 3.02/1.00  
% 3.02/1.00  ------ BMC1
% 3.02/1.00  
% 3.02/1.00  bmc1_current_bound:                     -1
% 3.02/1.00  bmc1_last_solved_bound:                 -1
% 3.02/1.00  bmc1_unsat_core_size:                   -1
% 3.02/1.00  bmc1_unsat_core_parents_size:           -1
% 3.02/1.00  bmc1_merge_next_fun:                    0
% 3.02/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation
% 3.02/1.00  
% 3.02/1.00  inst_num_of_clauses:                    909
% 3.02/1.00  inst_num_in_passive:                    34
% 3.02/1.00  inst_num_in_active:                     429
% 3.02/1.00  inst_num_in_unprocessed:                446
% 3.02/1.00  inst_num_of_loops:                      530
% 3.02/1.00  inst_num_of_learning_restarts:          0
% 3.02/1.00  inst_num_moves_active_passive:          99
% 3.02/1.00  inst_lit_activity:                      0
% 3.02/1.00  inst_lit_activity_moves:                0
% 3.02/1.00  inst_num_tautologies:                   0
% 3.02/1.00  inst_num_prop_implied:                  0
% 3.02/1.00  inst_num_existing_simplified:           0
% 3.02/1.00  inst_num_eq_res_simplified:             0
% 3.02/1.00  inst_num_child_elim:                    0
% 3.02/1.00  inst_num_of_dismatching_blockings:      243
% 3.02/1.00  inst_num_of_non_proper_insts:           584
% 3.02/1.00  inst_num_of_duplicates:                 0
% 3.02/1.00  inst_inst_num_from_inst_to_res:         0
% 3.02/1.00  inst_dismatching_checking_time:         0.
% 3.02/1.00  
% 3.02/1.00  ------ Resolution
% 3.02/1.00  
% 3.02/1.00  res_num_of_clauses:                     0
% 3.02/1.00  res_num_in_passive:                     0
% 3.02/1.00  res_num_in_active:                      0
% 3.02/1.00  res_num_of_loops:                       157
% 3.02/1.00  res_forward_subset_subsumed:            31
% 3.02/1.00  res_backward_subset_subsumed:           0
% 3.02/1.00  res_forward_subsumed:                   0
% 3.02/1.00  res_backward_subsumed:                  0
% 3.02/1.00  res_forward_subsumption_resolution:     6
% 3.02/1.00  res_backward_subsumption_resolution:    0
% 3.02/1.00  res_clause_to_clause_subsumption:       257
% 3.02/1.00  res_orphan_elimination:                 0
% 3.02/1.00  res_tautology_del:                      129
% 3.02/1.00  res_num_eq_res_simplified:              0
% 3.02/1.00  res_num_sel_changes:                    0
% 3.02/1.00  res_moves_from_active_to_pass:          0
% 3.02/1.00  
% 3.02/1.00  ------ Superposition
% 3.02/1.00  
% 3.02/1.00  sup_time_total:                         0.
% 3.02/1.00  sup_time_generating:                    0.
% 3.02/1.00  sup_time_sim_full:                      0.
% 3.02/1.00  sup_time_sim_immed:                     0.
% 3.02/1.00  
% 3.02/1.00  sup_num_of_clauses:                     93
% 3.02/1.00  sup_num_in_active:                      52
% 3.02/1.00  sup_num_in_passive:                     41
% 3.02/1.00  sup_num_of_loops:                       105
% 3.02/1.00  sup_fw_superposition:                   82
% 3.02/1.00  sup_bw_superposition:                   68
% 3.02/1.00  sup_immediate_simplified:               97
% 3.02/1.00  sup_given_eliminated:                   1
% 3.02/1.00  comparisons_done:                       0
% 3.02/1.00  comparisons_avoided:                    11
% 3.02/1.00  
% 3.02/1.00  ------ Simplifications
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  sim_fw_subset_subsumed:                 26
% 3.02/1.00  sim_bw_subset_subsumed:                 9
% 3.02/1.00  sim_fw_subsumed:                        15
% 3.02/1.00  sim_bw_subsumed:                        2
% 3.02/1.00  sim_fw_subsumption_res:                 3
% 3.02/1.00  sim_bw_subsumption_res:                 4
% 3.02/1.00  sim_tautology_del:                      3
% 3.02/1.00  sim_eq_tautology_del:                   10
% 3.02/1.00  sim_eq_res_simp:                        4
% 3.02/1.00  sim_fw_demodulated:                     31
% 3.02/1.00  sim_bw_demodulated:                     59
% 3.02/1.00  sim_light_normalised:                   47
% 3.02/1.00  sim_joinable_taut:                      0
% 3.02/1.00  sim_joinable_simp:                      0
% 3.02/1.00  sim_ac_normalised:                      0
% 3.02/1.00  sim_smt_subsumption:                    0
% 3.02/1.00  
%------------------------------------------------------------------------------
