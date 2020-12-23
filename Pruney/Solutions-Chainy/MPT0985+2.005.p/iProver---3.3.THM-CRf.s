%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:20 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  279 (10765 expanded)
%              Number of clauses        :  181 (3607 expanded)
%              Number of leaves         :   22 (2031 expanded)
%              Depth                    :   31
%              Number of atoms          :  791 (56047 expanded)
%              Number of equality atoms :  389 (11025 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f61,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f62,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f61])).

fof(f73,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f62,f73])).

fof(f125,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f74])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f104,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f126,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f123,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f27,axiom,(
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

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f136,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f117])).

fof(f128,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f74])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f69])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f132,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f106,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f124,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f108,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f127,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f74])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f122,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f109,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f121,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f137,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f115])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f131,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f67])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f130,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f64,f65])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f129,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_51,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2502,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2506,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5422,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2502,c_2506])).

cnf(c_29,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_50,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_729,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_50])).

cnf(c_730,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_53,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_732,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_53])).

cnf(c_2491,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_5640,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5422,c_2491])).

cnf(c_41,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_48,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_893,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_48])).

cnf(c_894,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_2485,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_2764,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2485,c_8])).

cnf(c_54,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_30,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2898,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2899,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2898])).

cnf(c_2907,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3095,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2907])).

cnf(c_3096,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3095])).

cnf(c_3192,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2764,c_54,c_56,c_2899,c_3096])).

cnf(c_3193,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3192])).

cnf(c_5657,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5640,c_3193])).

cnf(c_2508,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8064,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5640,c_2508])).

cnf(c_44,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_52,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_965,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_52])).

cnf(c_966,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_968,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_51])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2505,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6923,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2502,c_2505])).

cnf(c_7415,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_968,c_6923])).

cnf(c_34,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_701,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_50])).

cnf(c_702,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_704,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_702,c_53])).

cnf(c_2493,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_5638,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5422,c_2493])).

cnf(c_5646,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5638,c_5640])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2504,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6235,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2502,c_2504])).

cnf(c_49,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_6250,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_6235,c_49])).

cnf(c_7906,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5646,c_6250])).

cnf(c_45,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2503,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_7908,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k4_relat_1(sK3))))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7906,c_2503])).

cnf(c_33,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_715,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_50])).

cnf(c_716,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_718,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_53])).

cnf(c_2492,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_5639,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5422,c_2492])).

cnf(c_5643,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5639,c_5640])).

cnf(c_7909,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7908,c_5643])).

cnf(c_31,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2507,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7952,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5640,c_2507])).

cnf(c_9900,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7909,c_54,c_56,c_3096,c_7952,c_8064])).

cnf(c_9905,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7415,c_9900])).

cnf(c_46,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_976,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_48])).

cnf(c_977,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_989,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_977,c_35])).

cnf(c_2481,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_994,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_3103,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2481,c_54,c_56,c_994,c_2899,c_3096])).

cnf(c_3104,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3103])).

cnf(c_5658,plain,
    ( k1_relat_1(k4_relat_1(sK3)) != sK2
    | k2_relat_1(k4_relat_1(sK3)) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5640,c_3104])).

cnf(c_9403,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5658,c_7906])).

cnf(c_9407,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9403,c_5643])).

cnf(c_9411,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7415,c_9407])).

cnf(c_9927,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9905,c_9411])).

cnf(c_9930,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9927,c_9900])).

cnf(c_10045,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9930,c_8])).

cnf(c_42,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_48])).

cnf(c_950,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_2482,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_5659,plain,
    ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5640,c_2482])).

cnf(c_9955,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9927,c_5659])).

cnf(c_9997,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9955,c_8])).

cnf(c_10049,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10045,c_9997])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_912,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_52])).

cnf(c_913,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_2484,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_913])).

cnf(c_2678,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2484,c_8])).

cnf(c_9959,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9927,c_2678])).

cnf(c_9961,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9927,c_2502])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_9966,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9961,c_7])).

cnf(c_9971,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9959,c_9966])).

cnf(c_6927,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2505])).

cnf(c_10676,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_9966,c_6927])).

cnf(c_12041,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9971,c_10676])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_159,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_161,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_166,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3030,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(X1)),X0)
    | r1_tarski(X0,k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3843,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
    | r1_tarski(X0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_3844,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3843])).

cnf(c_3846,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3844])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_375,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_376,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_375])).

cnf(c_457,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_376])).

cnf(c_6339,plain,
    ( ~ r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_6345,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6339])).

cnf(c_6347,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6345])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2516,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4523,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2502,c_2516])).

cnf(c_9957,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9927,c_4523])).

cnf(c_9982,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9957,c_7])).

cnf(c_2517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_36,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_22,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_36,c_22])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_36,c_35,c_22])).

cnf(c_2498,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_4502,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2498])).

cnf(c_4729,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_4502])).

cnf(c_10667,plain,
    ( k7_relat_1(sK3,X0) = sK3 ),
    inference(superposition,[status(thm)],[c_9982,c_4729])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2510,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5636,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_5422,c_2510])).

cnf(c_11860,plain,
    ( k9_relat_1(sK3,X0) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_10667,c_5636])).

cnf(c_9954,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9927,c_6250])).

cnf(c_11862,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11860,c_9954])).

cnf(c_32,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_743,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_50])).

cnf(c_744,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_748,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_53])).

cnf(c_2490,plain,
    ( k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_5661,plain,
    ( k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5640,c_2490])).

cnf(c_6048,plain,
    ( r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5661,c_56,c_3096])).

cnf(c_6049,plain,
    ( k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6048])).

cnf(c_11910,plain,
    ( k9_relat_1(k4_relat_1(sK3),k1_xboole_0) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11862,c_6049])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2519,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3395,plain,
    ( k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2519,c_2490])).

cnf(c_2997,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3365,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2997])).

cnf(c_3366,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_3577,plain,
    ( k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3395,c_51,c_3095,c_3365,c_3366])).

cnf(c_5655,plain,
    ( k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5640,c_3577])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2511,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5637,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5422,c_2511])).

cnf(c_6275,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_6250,c_5637])).

cnf(c_8209,plain,
    ( k9_relat_1(k4_relat_1(sK3),sK2) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5655,c_6275])).

cnf(c_9939,plain,
    ( k9_relat_1(k4_relat_1(sK3),k1_xboole_0) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_9927,c_8209])).

cnf(c_11911,plain,
    ( k1_relat_1(sK3) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11910,c_9939])).

cnf(c_11913,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11911])).

cnf(c_12044,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12041,c_161,c_166,c_3846,c_6347,c_11913])).

cnf(c_9931,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9927,c_9407])).

cnf(c_10041,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9931,c_8])).

cnf(c_10047,plain,
    ( k1_relat_1(sK3) != sK1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10045,c_10041])).

cnf(c_12046,plain,
    ( sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12044,c_10047])).

cnf(c_12499,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5657,c_54,c_56,c_3096,c_8064,c_10049,c_12046])).

cnf(c_10835,plain,
    ( k1_relset_1(k1_xboole_0,X0,k4_relat_1(sK3)) = k1_relat_1(k4_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_10045,c_6927])).

cnf(c_9941,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9927,c_7906])).

cnf(c_10849,plain,
    ( k1_relset_1(k1_xboole_0,X0,k4_relat_1(sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10835,c_9941])).

cnf(c_12501,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12499,c_10849])).

cnf(c_12502,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_12501])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:22:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.52/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.99  
% 3.52/0.99  ------  iProver source info
% 3.52/0.99  
% 3.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.99  git: non_committed_changes: false
% 3.52/0.99  git: last_make_outside_of_git: false
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    --mode clausify
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         false
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     num_symb
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       true
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     false
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   []
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_full_bw                           [BwDemod]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  ------ Parsing...
% 3.52/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/1.00  ------ Proving...
% 3.52/1.00  ------ Problem Properties 
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  clauses                                 53
% 3.52/1.00  conjectures                             3
% 3.52/1.00  EPR                                     9
% 3.52/1.00  Horn                                    47
% 3.52/1.00  unary                                   11
% 3.52/1.00  binary                                  22
% 3.52/1.00  lits                                    128
% 3.52/1.00  lits eq                                 48
% 3.52/1.00  fd_pure                                 0
% 3.52/1.00  fd_pseudo                               0
% 3.52/1.00  fd_cond                                 2
% 3.52/1.00  fd_pseudo_cond                          1
% 3.52/1.00  AC symbols                              0
% 3.52/1.00  
% 3.52/1.00  ------ Schedule dynamic 5 is on 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  Current options:
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options
% 3.52/1.00  
% 3.52/1.00  --out_options                           all
% 3.52/1.00  --tptp_safe_out                         true
% 3.52/1.00  --problem_path                          ""
% 3.52/1.00  --include_path                          ""
% 3.52/1.00  --clausifier                            res/vclausify_rel
% 3.52/1.00  --clausifier_options                    --mode clausify
% 3.52/1.00  --stdin                                 false
% 3.52/1.00  --stats_out                             all
% 3.52/1.00  
% 3.52/1.00  ------ General Options
% 3.52/1.00  
% 3.52/1.00  --fof                                   false
% 3.52/1.00  --time_out_real                         305.
% 3.52/1.00  --time_out_virtual                      -1.
% 3.52/1.00  --symbol_type_check                     false
% 3.52/1.00  --clausify_out                          false
% 3.52/1.00  --sig_cnt_out                           false
% 3.52/1.00  --trig_cnt_out                          false
% 3.52/1.00  --trig_cnt_out_tolerance                1.
% 3.52/1.00  --trig_cnt_out_sk_spl                   false
% 3.52/1.00  --abstr_cl_out                          false
% 3.52/1.00  
% 3.52/1.00  ------ Global Options
% 3.52/1.00  
% 3.52/1.00  --schedule                              default
% 3.52/1.00  --add_important_lit                     false
% 3.52/1.00  --prop_solver_per_cl                    1000
% 3.52/1.00  --min_unsat_core                        false
% 3.52/1.00  --soft_assumptions                      false
% 3.52/1.00  --soft_lemma_size                       3
% 3.52/1.00  --prop_impl_unit_size                   0
% 3.52/1.00  --prop_impl_unit                        []
% 3.52/1.00  --share_sel_clauses                     true
% 3.52/1.00  --reset_solvers                         false
% 3.52/1.00  --bc_imp_inh                            [conj_cone]
% 3.52/1.00  --conj_cone_tolerance                   3.
% 3.52/1.00  --extra_neg_conj                        none
% 3.52/1.00  --large_theory_mode                     true
% 3.52/1.00  --prolific_symb_bound                   200
% 3.52/1.00  --lt_threshold                          2000
% 3.52/1.00  --clause_weak_htbl                      true
% 3.52/1.00  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         false
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     none
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       false
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     false
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   []
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_full_bw                           [BwDemod]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ Proving...
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS status Theorem for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00   Resolution empty clause
% 3.52/1.00  
% 3.52/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  fof(f29,conjecture,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f30,negated_conjecture,(
% 3.52/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.52/1.00    inference(negated_conjecture,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f61,plain,(
% 3.52/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f30])).
% 3.52/1.00  
% 3.52/1.00  fof(f62,plain,(
% 3.52/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.52/1.00    inference(flattening,[],[f61])).
% 3.52/1.00  
% 3.52/1.00  fof(f73,plain,(
% 3.52/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f74,plain,(
% 3.52/1.00    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f62,f73])).
% 3.52/1.00  
% 3.52/1.00  fof(f125,plain,(
% 3.52/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.52/1.00    inference(cnf_transformation,[],[f74])).
% 3.52/1.00  
% 3.52/1.00  fof(f23,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f53,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f23])).
% 3.52/1.00  
% 3.52/1.00  fof(f110,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f53])).
% 3.52/1.00  
% 3.52/1.00  fof(f19,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f45,plain,(
% 3.52/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f19])).
% 3.52/1.00  
% 3.52/1.00  fof(f46,plain,(
% 3.52/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f45])).
% 3.52/1.00  
% 3.52/1.00  fof(f104,plain,(
% 3.52/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f46])).
% 3.52/1.00  
% 3.52/1.00  fof(f126,plain,(
% 3.52/1.00    v2_funct_1(sK3)),
% 3.52/1.00    inference(cnf_transformation,[],[f74])).
% 3.52/1.00  
% 3.52/1.00  fof(f123,plain,(
% 3.52/1.00    v1_funct_1(sK3)),
% 3.52/1.00    inference(cnf_transformation,[],[f74])).
% 3.52/1.00  
% 3.52/1.00  fof(f27,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f57,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f58,plain,(
% 3.52/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(flattening,[],[f57])).
% 3.52/1.00  
% 3.52/1.00  fof(f72,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(nnf_transformation,[],[f58])).
% 3.52/1.00  
% 3.52/1.00  fof(f117,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f72])).
% 3.52/1.00  
% 3.52/1.00  fof(f136,plain,(
% 3.52/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.52/1.00    inference(equality_resolution,[],[f117])).
% 3.52/1.00  
% 3.52/1.00  fof(f128,plain,(
% 3.52/1.00    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.52/1.00    inference(cnf_transformation,[],[f74])).
% 3.52/1.00  
% 3.52/1.00  fof(f4,axiom,(
% 3.52/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f69,plain,(
% 3.52/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.52/1.00    inference(nnf_transformation,[],[f4])).
% 3.52/1.00  
% 3.52/1.00  fof(f70,plain,(
% 3.52/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.52/1.00    inference(flattening,[],[f69])).
% 3.52/1.00  
% 3.52/1.00  fof(f83,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.52/1.00    inference(cnf_transformation,[],[f70])).
% 3.52/1.00  
% 3.52/1.00  fof(f132,plain,(
% 3.52/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.52/1.00    inference(equality_resolution,[],[f83])).
% 3.52/1.00  
% 3.52/1.00  fof(f20,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f47,plain,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f20])).
% 3.52/1.00  
% 3.52/1.00  fof(f48,plain,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f47])).
% 3.52/1.00  
% 3.52/1.00  fof(f106,plain,(
% 3.52/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f48])).
% 3.52/1.00  
% 3.52/1.00  fof(f114,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f72])).
% 3.52/1.00  
% 3.52/1.00  fof(f124,plain,(
% 3.52/1.00    v1_funct_2(sK3,sK1,sK2)),
% 3.52/1.00    inference(cnf_transformation,[],[f74])).
% 3.52/1.00  
% 3.52/1.00  fof(f25,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f55,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f25])).
% 3.52/1.00  
% 3.52/1.00  fof(f112,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f55])).
% 3.52/1.00  
% 3.52/1.00  fof(f22,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f51,plain,(
% 3.52/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f22])).
% 3.52/1.00  
% 3.52/1.00  fof(f52,plain,(
% 3.52/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f51])).
% 3.52/1.00  
% 3.52/1.00  fof(f108,plain,(
% 3.52/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f52])).
% 3.52/1.00  
% 3.52/1.00  fof(f26,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f56,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f26])).
% 3.52/1.00  
% 3.52/1.00  fof(f113,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f56])).
% 3.52/1.00  
% 3.52/1.00  fof(f127,plain,(
% 3.52/1.00    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.52/1.00    inference(cnf_transformation,[],[f74])).
% 3.52/1.00  
% 3.52/1.00  fof(f28,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f59,plain,(
% 3.52/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f28])).
% 3.52/1.00  
% 3.52/1.00  fof(f60,plain,(
% 3.52/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f59])).
% 3.52/1.00  
% 3.52/1.00  fof(f122,plain,(
% 3.52/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f60])).
% 3.52/1.00  
% 3.52/1.00  fof(f109,plain,(
% 3.52/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f52])).
% 3.52/1.00  
% 3.52/1.00  fof(f105,plain,(
% 3.52/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f48])).
% 3.52/1.00  
% 3.52/1.00  fof(f121,plain,(
% 3.52/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f60])).
% 3.52/1.00  
% 3.52/1.00  fof(f116,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f72])).
% 3.52/1.00  
% 3.52/1.00  fof(f115,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f72])).
% 3.52/1.00  
% 3.52/1.00  fof(f137,plain,(
% 3.52/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.52/1.00    inference(equality_resolution,[],[f115])).
% 3.52/1.00  
% 3.52/1.00  fof(f84,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.52/1.00    inference(cnf_transformation,[],[f70])).
% 3.52/1.00  
% 3.52/1.00  fof(f131,plain,(
% 3.52/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.52/1.00    inference(equality_resolution,[],[f84])).
% 3.52/1.00  
% 3.52/1.00  fof(f3,axiom,(
% 3.52/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f67,plain,(
% 3.52/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/1.00    inference(nnf_transformation,[],[f3])).
% 3.52/1.00  
% 3.52/1.00  fof(f68,plain,(
% 3.52/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/1.00    inference(flattening,[],[f67])).
% 3.52/1.00  
% 3.52/1.00  fof(f79,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.52/1.00    inference(cnf_transformation,[],[f68])).
% 3.52/1.00  
% 3.52/1.00  fof(f130,plain,(
% 3.52/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.52/1.00    inference(equality_resolution,[],[f79])).
% 3.52/1.00  
% 3.52/1.00  fof(f2,axiom,(
% 3.52/1.00    v1_xboole_0(k1_xboole_0)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f78,plain,(
% 3.52/1.00    v1_xboole_0(k1_xboole_0)),
% 3.52/1.00    inference(cnf_transformation,[],[f2])).
% 3.52/1.00  
% 3.52/1.00  fof(f1,axiom,(
% 3.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f32,plain,(
% 3.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f1])).
% 3.52/1.00  
% 3.52/1.00  fof(f63,plain,(
% 3.52/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.52/1.00    inference(nnf_transformation,[],[f32])).
% 3.52/1.00  
% 3.52/1.00  fof(f64,plain,(
% 3.52/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.52/1.00    inference(rectify,[],[f63])).
% 3.52/1.00  
% 3.52/1.00  fof(f65,plain,(
% 3.52/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f66,plain,(
% 3.52/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f64,f65])).
% 3.52/1.00  
% 3.52/1.00  fof(f76,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f9,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f34,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.52/1.00    inference(ennf_transformation,[],[f9])).
% 3.52/1.00  
% 3.52/1.00  fof(f90,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f34])).
% 3.52/1.00  
% 3.52/1.00  fof(f8,axiom,(
% 3.52/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f71,plain,(
% 3.52/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.52/1.00    inference(nnf_transformation,[],[f8])).
% 3.52/1.00  
% 3.52/1.00  fof(f89,plain,(
% 3.52/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f71])).
% 3.52/1.00  
% 3.52/1.00  fof(f88,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f71])).
% 3.52/1.00  
% 3.52/1.00  fof(f24,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f31,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.52/1.00    inference(pure_predicate_removal,[],[f24])).
% 3.52/1.00  
% 3.52/1.00  fof(f54,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f31])).
% 3.52/1.00  
% 3.52/1.00  fof(f111,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f54])).
% 3.52/1.00  
% 3.52/1.00  fof(f15,axiom,(
% 3.52/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f40,plain,(
% 3.52/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.52/1.00    inference(ennf_transformation,[],[f15])).
% 3.52/1.00  
% 3.52/1.00  fof(f41,plain,(
% 3.52/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.52/1.00    inference(flattening,[],[f40])).
% 3.52/1.00  
% 3.52/1.00  fof(f97,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f41])).
% 3.52/1.00  
% 3.52/1.00  fof(f14,axiom,(
% 3.52/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f39,plain,(
% 3.52/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.52/1.00    inference(ennf_transformation,[],[f14])).
% 3.52/1.00  
% 3.52/1.00  fof(f96,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f39])).
% 3.52/1.00  
% 3.52/1.00  fof(f21,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f49,plain,(
% 3.52/1.00    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f21])).
% 3.52/1.00  
% 3.52/1.00  fof(f50,plain,(
% 3.52/1.00    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f49])).
% 3.52/1.00  
% 3.52/1.00  fof(f107,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f50])).
% 3.52/1.00  
% 3.52/1.00  fof(f80,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.52/1.00    inference(cnf_transformation,[],[f68])).
% 3.52/1.00  
% 3.52/1.00  fof(f129,plain,(
% 3.52/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.52/1.00    inference(equality_resolution,[],[f80])).
% 3.52/1.00  
% 3.52/1.00  fof(f13,axiom,(
% 3.52/1.00    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f38,plain,(
% 3.52/1.00    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(ennf_transformation,[],[f13])).
% 3.52/1.00  
% 3.52/1.00  fof(f95,plain,(
% 3.52/1.00    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f38])).
% 3.52/1.00  
% 3.52/1.00  cnf(c_51,negated_conjecture,
% 3.52/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f125]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2502,plain,
% 3.52/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_35,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2506,plain,
% 3.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.52/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5422,plain,
% 3.52/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2502,c_2506]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_29,plain,
% 3.52/1.00      ( ~ v2_funct_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_50,negated_conjecture,
% 3.52/1.00      ( v2_funct_1(sK3) ),
% 3.52/1.00      inference(cnf_transformation,[],[f126]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_729,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.52/1.00      | sK3 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_50]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_730,plain,
% 3.52/1.00      ( ~ v1_funct_1(sK3)
% 3.52/1.00      | ~ v1_relat_1(sK3)
% 3.52/1.00      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_729]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_53,negated_conjecture,
% 3.52/1.00      ( v1_funct_1(sK3) ),
% 3.52/1.00      inference(cnf_transformation,[],[f123]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_732,plain,
% 3.52/1.00      ( ~ v1_relat_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.52/1.00      inference(global_propositional_subsumption,[status(thm)],[c_730,c_53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2491,plain,
% 3.52/1.00      ( k2_funct_1(sK3) = k4_relat_1(sK3) | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5640,plain,
% 3.52/1.00      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5422,c_2491]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_41,plain,
% 3.52/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.52/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f136]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_48,negated_conjecture,
% 3.52/1.00      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.52/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.52/1.00      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f128]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_893,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.52/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.52/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.52/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.52/1.00      | k2_funct_1(sK3) != X0
% 3.52/1.00      | sK1 != X1
% 3.52/1.00      | sK2 != k1_xboole_0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_41,c_48]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_894,plain,
% 3.52/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.52/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.52/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.52/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.52/1.00      | sK2 != k1_xboole_0 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_893]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2485,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.52/1.00      | sK2 != k1_xboole_0
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.52/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_8,plain,
% 3.52/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f132]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2764,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.52/1.00      | sK2 != k1_xboole_0
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.52/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_2485,c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_54,plain,
% 3.52/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_56,plain,
% 3.52/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_30,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2898,plain,
% 3.52/1.00      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2899,plain,
% 3.52/1.00      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.52/1.00      | v1_funct_1(sK3) != iProver_top
% 3.52/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2898]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2907,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK3) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_35]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3095,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.52/1.00      | v1_relat_1(sK3) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_2907]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3096,plain,
% 3.52/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.52/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_3095]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3192,plain,
% 3.52/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | sK2 != k1_xboole_0
% 3.52/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_2764,c_54,c_56,c_2899,c_3096]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3193,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.52/1.00      | sK2 != k1_xboole_0
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_3192]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5657,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.52/1.00      | sK2 != k1_xboole_0
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5640,c_3193]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2508,plain,
% 3.52/1.00      ( v1_funct_1(X0) != iProver_top
% 3.52/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.52/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_8064,plain,
% 3.52/1.00      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 3.52/1.00      | v1_funct_1(sK3) != iProver_top
% 3.52/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5640,c_2508]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_44,plain,
% 3.52/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.52/1.00      | k1_xboole_0 = X2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_52,negated_conjecture,
% 3.52/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.52/1.00      inference(cnf_transformation,[],[f124]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_965,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.52/1.00      | sK1 != X1
% 3.52/1.00      | sK2 != X2
% 3.52/1.00      | sK3 != X0
% 3.52/1.00      | k1_xboole_0 = X2 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_44,c_52]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_966,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.52/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.52/1.00      | k1_xboole_0 = sK2 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_965]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_968,plain,
% 3.52/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.52/1.00      inference(global_propositional_subsumption,[status(thm)],[c_966,c_51]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_37,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2505,plain,
% 3.52/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.52/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6923,plain,
% 3.52/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2502,c_2505]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7415,plain,
% 3.52/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_968,c_6923]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_34,plain,
% 3.52/1.00      ( ~ v2_funct_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_701,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.52/1.00      | sK3 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_34,c_50]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_702,plain,
% 3.52/1.00      ( ~ v1_funct_1(sK3)
% 3.52/1.00      | ~ v1_relat_1(sK3)
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_701]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_704,plain,
% 3.52/1.00      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.52/1.00      inference(global_propositional_subsumption,[status(thm)],[c_702,c_53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2493,plain,
% 3.52/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.52/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5638,plain,
% 3.52/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5422,c_2493]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5646,plain,
% 3.52/1.00      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_5638,c_5640]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_38,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2504,plain,
% 3.52/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.52/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6235,plain,
% 3.52/1.00      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2502,c_2504]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_49,negated_conjecture,
% 3.52/1.00      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f127]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6250,plain,
% 3.52/1.00      ( k2_relat_1(sK3) = sK2 ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_6235,c_49]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7906,plain,
% 3.52/1.00      ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_5646,c_6250]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_45,plain,
% 3.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f122]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2503,plain,
% 3.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.52/1.00      | v1_funct_1(X0) != iProver_top
% 3.52/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7908,plain,
% 3.52/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k4_relat_1(sK3))))) = iProver_top
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.52/1.00      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_7906,c_2503]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_33,plain,
% 3.52/1.00      ( ~ v2_funct_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_715,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.52/1.00      | sK3 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_33,c_50]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_716,plain,
% 3.52/1.00      ( ~ v1_funct_1(sK3)
% 3.52/1.00      | ~ v1_relat_1(sK3)
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_715]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_718,plain,
% 3.52/1.00      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(global_propositional_subsumption,[status(thm)],[c_716,c_53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2492,plain,
% 3.52/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.52/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5639,plain,
% 3.52/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5422,c_2492]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5643,plain,
% 3.52/1.00      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_5639,c_5640]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7909,plain,
% 3.52/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.52/1.00      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_7908,c_5643]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_31,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2507,plain,
% 3.52/1.00      ( v1_funct_1(X0) != iProver_top
% 3.52/1.00      | v1_relat_1(X0) != iProver_top
% 3.52/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7952,plain,
% 3.52/1.00      ( v1_funct_1(sK3) != iProver_top
% 3.52/1.00      | v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 3.52/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5640,c_2507]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9900,plain,
% 3.52/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_7909,c_54,c_56,c_3096,c_7952,c_8064]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9905,plain,
% 3.52/1.00      ( sK2 = k1_xboole_0
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_7415,c_9900]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_46,plain,
% 3.52/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_976,plain,
% 3.52/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k2_funct_1(sK3) != X0
% 3.52/1.00      | k1_relat_1(X0) != sK2
% 3.52/1.00      | k2_relat_1(X0) != sK1 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_46,c_48]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_977,plain,
% 3.52/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.52/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.52/1.00      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_976]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_989,plain,
% 3.52/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.52/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.52/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_977,c_35]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2481,plain,
% 3.52/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_994,plain,
% 3.52/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3103,plain,
% 3.52/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_2481,c_54,c_56,c_994,c_2899,c_3096]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3104,plain,
% 3.52/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_3103]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5658,plain,
% 3.52/1.00      ( k1_relat_1(k4_relat_1(sK3)) != sK2
% 3.52/1.00      | k2_relat_1(k4_relat_1(sK3)) != sK1
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5640,c_3104]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9403,plain,
% 3.52/1.00      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5658,c_7906]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9407,plain,
% 3.52/1.00      ( k1_relat_1(sK3) != sK1
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_9403,c_5643]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9411,plain,
% 3.52/1.00      ( sK2 = k1_xboole_0
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_7415,c_9407]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9927,plain,
% 3.52/1.00      ( sK2 = k1_xboole_0 ),
% 3.52/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9905,c_9411]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9930,plain,
% 3.52/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_9900]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10045,plain,
% 3.52/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9930,c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_42,plain,
% 3.52/1.00      ( v1_funct_2(X0,X1,X2)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.52/1.00      | k1_xboole_0 = X2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_949,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.52/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.52/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.52/1.00      | k2_funct_1(sK3) != X0
% 3.52/1.00      | sK1 != X2
% 3.52/1.00      | sK2 != X1
% 3.52/1.00      | k1_xboole_0 = X2 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_42,c_48]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_950,plain,
% 3.52/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.52/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.52/1.00      | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 3.52/1.00      | k1_xboole_0 = sK1 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_949]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2482,plain,
% 3.52/1.00      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 3.52/1.00      | k1_xboole_0 = sK1
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_950]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5659,plain,
% 3.52/1.00      ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) != sK2
% 3.52/1.00      | sK1 = k1_xboole_0
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5640,c_2482]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9955,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_5659]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9997,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9955,c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10049,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_10045,c_9997]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_43,plain,
% 3.52/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.52/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f137]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_912,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.52/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.52/1.00      | sK1 != k1_xboole_0
% 3.52/1.00      | sK2 != X1
% 3.52/1.00      | sK3 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_43,c_52]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_913,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.52/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 3.52/1.00      | sK1 != k1_xboole_0 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_912]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2484,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 3.52/1.00      | sK1 != k1_xboole_0
% 3.52/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_913]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2678,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 3.52/1.00      | sK1 != k1_xboole_0
% 3.52/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_2484,c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9959,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.52/1.00      | sK1 != k1_xboole_0
% 3.52/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_2678]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9961,plain,
% 3.52/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_2502]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7,plain,
% 3.52/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f131]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9966,plain,
% 3.52/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9961,c_7]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9971,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.52/1.00      | sK1 != k1_xboole_0 ),
% 3.52/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_9959,c_9966]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6927,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.52/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_8,c_2505]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10676,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_9966,c_6927]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12041,plain,
% 3.52/1.00      ( k1_relat_1(sK3) = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9971,c_10676]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f130]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_159,plain,
% 3.52/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_161,plain,
% 3.52/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_159]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3,plain,
% 3.52/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_166,plain,
% 3.52/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1,plain,
% 3.52/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3030,plain,
% 3.52/1.00      ( r2_hidden(sK0(X0,k1_relat_1(X1)),X0) | r1_tarski(X0,k1_relat_1(X1)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3843,plain,
% 3.52/1.00      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) | r1_tarski(X0,k1_relat_1(sK3)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_3030]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3844,plain,
% 3.52/1.00      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) = iProver_top
% 3.52/1.00      | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_3843]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3846,plain,
% 3.52/1.00      ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
% 3.52/1.00      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) = iProver_top ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_3844]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_15,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/1.00      | ~ r2_hidden(X2,X0)
% 3.52/1.00      | ~ v1_xboole_0(X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_13,plain,
% 3.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_375,plain,
% 3.52/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.52/1.00      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_376,plain,
% 3.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_375]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_457,plain,
% 3.52/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.52/1.00      inference(bin_hyper_res,[status(thm)],[c_15,c_376]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6339,plain,
% 3.52/1.00      ( ~ r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
% 3.52/1.00      | ~ r1_tarski(X0,X1)
% 3.52/1.00      | ~ v1_xboole_0(X1) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_457]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6345,plain,
% 3.52/1.00      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) != iProver_top
% 3.52/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.52/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_6339]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6347,plain,
% 3.52/1.00      ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) != iProver_top
% 3.52/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.52/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_6345]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_14,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2516,plain,
% 3.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.52/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4523,plain,
% 3.52/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2502,c_2516]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9957,plain,
% 3.52/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_4523]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9982,plain,
% 3.52/1.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9957,c_7]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2517,plain,
% 3.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.52/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_36,plain,
% 3.52/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_22,plain,
% 3.52/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_608,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.52/1.00      inference(resolution,[status(thm)],[c_36,c_22]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_612,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_608,c_36,c_35,c_22]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2498,plain,
% 3.52/1.00      ( k7_relat_1(X0,X1) = X0
% 3.52/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4502,plain,
% 3.52/1.00      ( k7_relat_1(X0,X1) = X0
% 3.52/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_7,c_2498]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4729,plain,
% 3.52/1.00      ( k7_relat_1(X0,X1) = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2517,c_4502]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10667,plain,
% 3.52/1.00      ( k7_relat_1(sK3,X0) = sK3 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_9982,c_4729]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_21,plain,
% 3.52/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2510,plain,
% 3.52/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.52/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5636,plain,
% 3.52/1.00      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5422,c_2510]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_11860,plain,
% 3.52/1.00      ( k9_relat_1(sK3,X0) = k2_relat_1(sK3) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_10667,c_5636]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9954,plain,
% 3.52/1.00      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_6250]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_11862,plain,
% 3.52/1.00      ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_11860,c_9954]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_32,plain,
% 3.52/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.52/1.00      | ~ v2_funct_1(X1)
% 3.52/1.00      | ~ v1_funct_1(X1)
% 3.52/1.00      | ~ v1_relat_1(X1)
% 3.52/1.00      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_743,plain,
% 3.52/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.52/1.00      | ~ v1_funct_1(X1)
% 3.52/1.00      | ~ v1_relat_1(X1)
% 3.52/1.00      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
% 3.52/1.00      | sK3 != X1 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_50]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_744,plain,
% 3.52/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.52/1.00      | ~ v1_funct_1(sK3)
% 3.52/1.00      | ~ v1_relat_1(sK3)
% 3.52/1.00      | k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,X0)) = X0 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_743]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_748,plain,
% 3.52/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.52/1.00      | ~ v1_relat_1(sK3)
% 3.52/1.00      | k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,X0)) = X0 ),
% 3.52/1.00      inference(global_propositional_subsumption,[status(thm)],[c_744,c_53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2490,plain,
% 3.52/1.00      ( k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,X0)) = X0
% 3.52/1.00      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5661,plain,
% 3.52/1.00      ( k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,X0)) = X0
% 3.52/1.00      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5640,c_2490]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6048,plain,
% 3.52/1.00      ( r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.52/1.00      | k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,X0)) = X0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_5661,c_56,c_3096]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6049,plain,
% 3.52/1.00      ( k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,X0)) = X0
% 3.52/1.00      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_6048]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_11910,plain,
% 3.52/1.00      ( k9_relat_1(k4_relat_1(sK3),k1_xboole_0) = X0
% 3.52/1.00      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_11862,c_6049]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f129]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2519,plain,
% 3.52/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3395,plain,
% 3.52/1.00      ( k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3)
% 3.52/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2519,c_2490]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2997,plain,
% 3.52/1.00      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3365,plain,
% 3.52/1.00      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_2997]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3366,plain,
% 3.52/1.00      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 3.52/1.00      | ~ v1_relat_1(sK3)
% 3.52/1.00      | k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_748]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3577,plain,
% 3.52/1.00      ( k9_relat_1(k2_funct_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_3395,c_51,c_3095,c_3365,c_3366]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5655,plain,
% 3.52/1.00      ( k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5640,c_3577]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_20,plain,
% 3.52/1.00      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2511,plain,
% 3.52/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.52/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5637,plain,
% 3.52/1.00      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5422,c_2511]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6275,plain,
% 3.52/1.00      ( k9_relat_1(sK3,k1_relat_1(sK3)) = sK2 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_6250,c_5637]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_8209,plain,
% 3.52/1.00      ( k9_relat_1(k4_relat_1(sK3),sK2) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_5655,c_6275]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9939,plain,
% 3.52/1.00      ( k9_relat_1(k4_relat_1(sK3),k1_xboole_0) = k1_relat_1(sK3) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_8209]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_11911,plain,
% 3.52/1.00      ( k1_relat_1(sK3) = X0 | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_11910,c_9939]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_11913,plain,
% 3.52/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.52/1.00      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_11911]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12044,plain,
% 3.52/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_12041,c_161,c_166,c_3846,c_6347,c_11913]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9931,plain,
% 3.52/1.00      ( k1_relat_1(sK3) != sK1
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_9407]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10041,plain,
% 3.52/1.00      ( k1_relat_1(sK3) != sK1
% 3.52/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9931,c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10047,plain,
% 3.52/1.00      ( k1_relat_1(sK3) != sK1 ),
% 3.52/1.00      inference(backward_subsumption_resolution,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_10045,c_10041]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12046,plain,
% 3.52/1.00      ( sK1 != k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_12044,c_10047]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12499,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_5657,c_54,c_56,c_3096,c_8064,c_10049,c_12046]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10835,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,X0,k4_relat_1(sK3)) = k1_relat_1(k4_relat_1(sK3)) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_10045,c_6927]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9941,plain,
% 3.52/1.00      ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_9927,c_7906]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10849,plain,
% 3.52/1.00      ( k1_relset_1(k1_xboole_0,X0,k4_relat_1(sK3)) = k1_xboole_0 ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_10835,c_9941]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12501,plain,
% 3.52/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_12499,c_10849]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12502,plain,
% 3.52/1.00      ( $false ),
% 3.52/1.00      inference(equality_resolution_simp,[status(thm)],[c_12501]) ).
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  ------                               Statistics
% 3.52/1.00  
% 3.52/1.00  ------ General
% 3.52/1.00  
% 3.52/1.00  abstr_ref_over_cycles:                  0
% 3.52/1.00  abstr_ref_under_cycles:                 0
% 3.52/1.00  gc_basic_clause_elim:                   0
% 3.52/1.00  forced_gc_time:                         0
% 3.52/1.00  parsing_time:                           0.012
% 3.52/1.00  unif_index_cands_time:                  0.
% 3.52/1.00  unif_index_add_time:                    0.
% 3.52/1.00  orderings_time:                         0.
% 3.52/1.00  out_proof_time:                         0.015
% 3.52/1.00  total_time:                             0.317
% 3.52/1.00  num_of_symbols:                         56
% 3.52/1.00  num_of_terms:                           9925
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing
% 3.52/1.00  
% 3.52/1.00  num_of_splits:                          0
% 3.52/1.00  num_of_split_atoms:                     0
% 3.52/1.00  num_of_reused_defs:                     0
% 3.52/1.00  num_eq_ax_congr_red:                    26
% 3.52/1.00  num_of_sem_filtered_clauses:            1
% 3.52/1.00  num_of_subtypes:                        0
% 3.52/1.00  monotx_restored_types:                  0
% 3.52/1.00  sat_num_of_epr_types:                   0
% 3.52/1.00  sat_num_of_non_cyclic_types:            0
% 3.52/1.00  sat_guarded_non_collapsed_types:        0
% 3.52/1.00  num_pure_diseq_elim:                    0
% 3.52/1.00  simp_replaced_by:                       0
% 3.52/1.00  res_preprocessed:                       244
% 3.52/1.00  prep_upred:                             0
% 3.52/1.00  prep_unflattend:                        46
% 3.52/1.00  smt_new_axioms:                         0
% 3.52/1.00  pred_elim_cands:                        6
% 3.52/1.00  pred_elim:                              3
% 3.52/1.00  pred_elim_cl:                           -3
% 3.52/1.00  pred_elim_cycles:                       5
% 3.52/1.00  merged_defs:                            8
% 3.52/1.00  merged_defs_ncl:                        0
% 3.52/1.00  bin_hyper_res:                          10
% 3.52/1.00  prep_cycles:                            4
% 3.52/1.00  pred_elim_time:                         0.012
% 3.52/1.00  splitting_time:                         0.
% 3.52/1.00  sem_filter_time:                        0.
% 3.52/1.00  monotx_time:                            0.001
% 3.52/1.00  subtype_inf_time:                       0.
% 3.52/1.00  
% 3.52/1.00  ------ Problem properties
% 3.52/1.00  
% 3.52/1.00  clauses:                                53
% 3.52/1.00  conjectures:                            3
% 3.52/1.00  epr:                                    9
% 3.52/1.00  horn:                                   47
% 3.52/1.00  ground:                                 17
% 3.52/1.00  unary:                                  11
% 3.52/1.00  binary:                                 22
% 3.52/1.00  lits:                                   128
% 3.52/1.00  lits_eq:                                48
% 3.52/1.00  fd_pure:                                0
% 3.52/1.00  fd_pseudo:                              0
% 3.52/1.00  fd_cond:                                2
% 3.52/1.00  fd_pseudo_cond:                         1
% 3.52/1.00  ac_symbols:                             0
% 3.52/1.00  
% 3.52/1.00  ------ Propositional Solver
% 3.52/1.00  
% 3.52/1.00  prop_solver_calls:                      29
% 3.52/1.00  prop_fast_solver_calls:                 1668
% 3.52/1.00  smt_solver_calls:                       0
% 3.52/1.00  smt_fast_solver_calls:                  0
% 3.52/1.00  prop_num_of_clauses:                    4403
% 3.52/1.00  prop_preprocess_simplified:             12656
% 3.52/1.00  prop_fo_subsumed:                       49
% 3.52/1.00  prop_solver_time:                       0.
% 3.52/1.00  smt_solver_time:                        0.
% 3.52/1.00  smt_fast_solver_time:                   0.
% 3.52/1.00  prop_fast_solver_time:                  0.
% 3.52/1.00  prop_unsat_core_time:                   0.
% 3.52/1.00  
% 3.52/1.00  ------ QBF
% 3.52/1.00  
% 3.52/1.00  qbf_q_res:                              0
% 3.52/1.00  qbf_num_tautologies:                    0
% 3.52/1.00  qbf_prep_cycles:                        0
% 3.52/1.00  
% 3.52/1.00  ------ BMC1
% 3.52/1.00  
% 3.52/1.00  bmc1_current_bound:                     -1
% 3.52/1.00  bmc1_last_solved_bound:                 -1
% 3.52/1.00  bmc1_unsat_core_size:                   -1
% 3.52/1.00  bmc1_unsat_core_parents_size:           -1
% 3.52/1.00  bmc1_merge_next_fun:                    0
% 3.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation
% 3.52/1.00  
% 3.52/1.00  inst_num_of_clauses:                    1361
% 3.52/1.00  inst_num_in_passive:                    662
% 3.52/1.00  inst_num_in_active:                     556
% 3.52/1.00  inst_num_in_unprocessed:                145
% 3.52/1.00  inst_num_of_loops:                      820
% 3.52/1.00  inst_num_of_learning_restarts:          0
% 3.52/1.00  inst_num_moves_active_passive:          261
% 3.52/1.00  inst_lit_activity:                      0
% 3.52/1.00  inst_lit_activity_moves:                0
% 3.52/1.00  inst_num_tautologies:                   0
% 3.52/1.00  inst_num_prop_implied:                  0
% 3.52/1.00  inst_num_existing_simplified:           0
% 3.52/1.00  inst_num_eq_res_simplified:             0
% 3.52/1.00  inst_num_child_elim:                    0
% 3.52/1.00  inst_num_of_dismatching_blockings:      512
% 3.52/1.00  inst_num_of_non_proper_insts:           1378
% 3.52/1.00  inst_num_of_duplicates:                 0
% 3.52/1.00  inst_inst_num_from_inst_to_res:         0
% 3.52/1.00  inst_dismatching_checking_time:         0.
% 3.52/1.00  
% 3.52/1.00  ------ Resolution
% 3.52/1.00  
% 3.52/1.00  res_num_of_clauses:                     0
% 3.52/1.00  res_num_in_passive:                     0
% 3.52/1.00  res_num_in_active:                      0
% 3.52/1.00  res_num_of_loops:                       248
% 3.52/1.00  res_forward_subset_subsumed:            92
% 3.52/1.00  res_backward_subset_subsumed:           6
% 3.52/1.00  res_forward_subsumed:                   0
% 3.52/1.00  res_backward_subsumed:                  0
% 3.52/1.00  res_forward_subsumption_resolution:     5
% 3.52/1.00  res_backward_subsumption_resolution:    0
% 3.52/1.00  res_clause_to_clause_subsumption:       599
% 3.52/1.00  res_orphan_elimination:                 0
% 3.52/1.00  res_tautology_del:                      101
% 3.52/1.00  res_num_eq_res_simplified:              0
% 3.52/1.00  res_num_sel_changes:                    0
% 3.52/1.00  res_moves_from_active_to_pass:          0
% 3.52/1.00  
% 3.52/1.00  ------ Superposition
% 3.52/1.00  
% 3.52/1.00  sup_time_total:                         0.
% 3.52/1.00  sup_time_generating:                    0.
% 3.52/1.00  sup_time_sim_full:                      0.
% 3.52/1.00  sup_time_sim_immed:                     0.
% 3.52/1.00  
% 3.52/1.00  sup_num_of_clauses:                     187
% 3.52/1.00  sup_num_in_active:                      100
% 3.52/1.00  sup_num_in_passive:                     87
% 3.52/1.00  sup_num_of_loops:                       163
% 3.52/1.00  sup_fw_superposition:                   128
% 3.52/1.00  sup_bw_superposition:                   115
% 3.52/1.00  sup_immediate_simplified:               120
% 3.52/1.00  sup_given_eliminated:                   0
% 3.52/1.00  comparisons_done:                       0
% 3.52/1.00  comparisons_avoided:                    14
% 3.52/1.00  
% 3.52/1.00  ------ Simplifications
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  sim_fw_subset_subsumed:                 27
% 3.52/1.00  sim_bw_subset_subsumed:                 6
% 3.52/1.00  sim_fw_subsumed:                        12
% 3.52/1.00  sim_bw_subsumed:                        3
% 3.52/1.00  sim_fw_subsumption_res:                 4
% 3.52/1.00  sim_bw_subsumption_res:                 3
% 3.52/1.00  sim_tautology_del:                      3
% 3.52/1.00  sim_eq_tautology_del:                   17
% 3.52/1.00  sim_eq_res_simp:                        2
% 3.52/1.00  sim_fw_demodulated:                     30
% 3.52/1.00  sim_bw_demodulated:                     60
% 3.52/1.00  sim_light_normalised:                   70
% 3.52/1.00  sim_joinable_taut:                      0
% 3.52/1.00  sim_joinable_simp:                      0
% 3.52/1.00  sim_ac_normalised:                      0
% 3.52/1.00  sim_smt_subsumption:                    0
% 3.52/1.00  
%------------------------------------------------------------------------------
