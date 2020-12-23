%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:28 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  212 (2966 expanded)
%              Number of leaves         :   21 ( 926 expanded)
%              Depth                    :   58
%              Number of atoms          :  873 (30472 expanded)
%              Number of equality atoms :  289 (10266 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f660,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f60,f653,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f653,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f652,f66])).

fof(f66,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f51,f50])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f652,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f651,f243])).

fof(f243,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f241,f60])).

fof(f241,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f240,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f240,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f239,f58])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f239,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f238,f59])).

fof(f59,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f238,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f237,f60])).

fof(f237,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f236,f55])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f236,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f235,f56])).

fof(f56,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f235,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f234,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f234,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f232,f190])).

fof(f190,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f62,f188])).

fof(f188,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f187,f55])).

fof(f187,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f186,f57])).

fof(f186,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f185,f58])).

fof(f185,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f183,f60])).

fof(f183,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f132,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f132,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f129,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f129,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f96,f62])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f232,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f91,f188])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f651,plain,
    ( ~ v1_relat_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f650,f58])).

fof(f650,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(trivial_inequality_removal,[],[f642])).

fof(f642,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(superposition,[],[f415,f587])).

fof(f587,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f484,f576])).

fof(f576,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(resolution,[],[f568,f57])).

fof(f568,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = k2_funct_1(sK3) ) ),
    inference(resolution,[],[f557,f82])).

fof(f557,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f556])).

fof(f556,plain,
    ( sK1 != sK1
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f436,f551])).

fof(f551,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f546,f60])).

fof(f546,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK1 = k1_relat_1(sK3) ) ),
    inference(resolution,[],[f545,f82])).

fof(f545,plain,
    ( ~ v1_relat_1(sK3)
    | sK1 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f544,f58])).

fof(f544,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f542,f259])).

fof(f259,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f258,f55])).

fof(f258,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f257,f56])).

fof(f257,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f256,f57])).

fof(f256,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f255,f58])).

fof(f255,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f254,f59])).

fof(f254,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f253,f60])).

fof(f253,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f252,f61])).

fof(f61,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f252,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f251,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f52])).

fof(f251,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f249,f101])).

fof(f101,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f69,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f249,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f94,f188])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | v2_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f542,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f538,f77])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f538,plain,(
    sK1 = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f537,f59])).

fof(f537,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(subsumption_resolution,[],[f536,f240])).

fof(f536,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f524,f60])).

fof(f524,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK3) != X1
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ v1_funct_2(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f523,f58])).

fof(f523,plain,(
    ! [X0,X1] :
      ( sK1 = k2_relat_1(k2_funct_1(sK3))
      | k2_relset_1(X0,X1,sK3) != X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f522,f259])).

fof(f522,plain,(
    ! [X0,X1] :
      ( sK1 = k2_relat_1(k2_funct_1(sK3))
      | k2_relset_1(X0,X1,sK3) != X1
      | ~ v2_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f520,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f520,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK1 = k2_relat_1(k2_funct_1(sK3)) ) ),
    inference(resolution,[],[f518,f82])).

fof(f518,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | sK1 = k2_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f515,f60])).

fof(f515,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(k2_funct_1(sK3))
      | sK1 = k2_relat_1(k2_funct_1(sK3)) ) ),
    inference(resolution,[],[f505,f82])).

fof(f505,plain,
    ( ~ v1_relat_1(sK3)
    | sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f504,f133])).

fof(f133,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f116,f71])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f113,f104])).

fof(f104,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f67])).

fof(f72,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f112,f82])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f504,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f503,f291])).

fof(f291,plain,(
    sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f278,f60])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK0 = k1_relat_1(k2_funct_1(sK3)) ) ),
    inference(resolution,[],[f260,f82])).

fof(f260,plain,
    ( ~ v1_relat_1(sK3)
    | sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f259,f244])).

fof(f244,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f118,f243])).

fof(f118,plain,
    ( ~ v2_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f76,f58])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f503,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0)
    | sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f502,f243])).

fof(f502,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f489,f103])).

fof(f103,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f73,f67])).

fof(f73,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f489,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k2_relat_1(k6_partfun1(sK1))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f74,f484])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f436,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f435,f125])).

fof(f125,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f123,f57])).

fof(f123,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f83,f61])).

fof(f435,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f434,f55])).

fof(f434,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f433])).

fof(f433,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2) ),
    inference(superposition,[],[f432,f200])).

fof(f200,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f199,f55])).

fof(f199,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f198,f57])).

fof(f198,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f197,f58])).

fof(f197,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f193,f60])).

fof(f193,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f188,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f432,plain,(
    ! [X0] :
      ( k6_partfun1(sK0) != k5_relat_1(X0,sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK3) = X0
      | k2_relat_1(X0) != k1_relat_1(sK3) ) ),
    inference(resolution,[],[f371,f60])).

fof(f371,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_funct_1(sK3) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_partfun1(sK0) != k5_relat_1(X0,sK3)
      | k2_relat_1(X0) != k1_relat_1(sK3) ) ),
    inference(resolution,[],[f267,f82])).

fof(f267,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK3)
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k6_partfun1(sK0) != k5_relat_1(X4,sK3) ) ),
    inference(forward_demodulation,[],[f266,f243])).

fof(f266,plain,(
    ! [X4] :
      ( k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X4,sK3)
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f263,f58])).

fof(f263,plain,(
    ! [X4] :
      ( k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X4,sK3)
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f259,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f67])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f484,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f483,f59])).

fof(f483,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(subsumption_resolution,[],[f482,f64])).

fof(f482,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(subsumption_resolution,[],[f481,f240])).

fof(f481,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f265,f60])).

fof(f265,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3))
      | k2_relset_1(X3,X2,sK3) != X2
      | k1_xboole_0 = X2
      | ~ v1_funct_2(sK3,X3,X2) ) ),
    inference(subsumption_resolution,[],[f262,f58])).

fof(f262,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3))
      | k2_relset_1(X3,X2,sK3) != X2
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK3,X3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f259,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f415,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != sK0
      | k2_funct_1(sK2) = X0 ) ),
    inference(resolution,[],[f410,f57])).

fof(f410,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != sK0
      | k5_relat_1(X0,sK2) != k6_partfun1(sK1) ) ),
    inference(resolution,[],[f405,f82])).

fof(f405,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | k5_relat_1(X0,sK2) != k6_partfun1(sK1)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != sK0 ) ),
    inference(backward_demodulation,[],[f152,f404])).

fof(f404,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f399,f57])).

fof(f399,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK0 = k1_relat_1(sK2) ) ),
    inference(resolution,[],[f395,f82])).

fof(f395,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f394,f55])).

fof(f394,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f392,f63])).

fof(f63,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f392,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f391,f77])).

fof(f391,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f390,f56])).

fof(f390,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f389,f61])).

fof(f389,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f328,f57])).

fof(f328,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | sK0 = k2_relat_1(k2_funct_1(sK2))
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f327,f55])).

fof(f327,plain,(
    ! [X0,X1] :
      ( sK0 = k2_relat_1(k2_funct_1(sK2))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f326,f63])).

fof(f326,plain,(
    ! [X0,X1] :
      ( sK0 = k2_relat_1(k2_funct_1(sK2))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f324,f88])).

fof(f324,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK0 = k2_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f323,f82])).

fof(f323,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f281,f57])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | sK0 = k2_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f277,f82])).

fof(f277,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f276,f133])).

fof(f276,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f275,f126])).

fof(f126,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f122,f125])).

fof(f122,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f120,f57])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f119,f82])).

fof(f119,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f117,f63])).

fof(f117,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f76,f55])).

fof(f275,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1)
    | sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f274,f125])).

fof(f274,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f273,f103])).

fof(f273,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k2_relat_1(k2_funct_1(sK2))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f74,f271])).

fof(f271,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f270,f56])).

fof(f270,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f269,f65])).

fof(f65,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f269,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f268,f61])).

fof(f268,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f182,f57])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2))
      | k2_relset_1(X1,X0,sK2) != X0
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f180,f55])).

fof(f180,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2))
      | k2_relset_1(X1,X0,sK2) != X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK2,X1,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f89,f63])).

fof(f152,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(sK1)
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f151,f125])).

fof(f151,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f149,f55])).

fof(f149,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f105,f63])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (1685)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (1686)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (1696)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (1675)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (1695)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (1677)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.56  % (1681)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (1683)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.57  % (1704)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.57  % (1697)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.57  % (1689)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.59/0.57  % (1705)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.57  % (1693)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.59/0.57  % (1707)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.59/0.57  % (1692)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.59/0.57  % (1687)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.58  % (1676)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.59/0.58  % (1678)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.59/0.58  % (1706)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.59/0.58  % (1698)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.59/0.58  % (1690)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.59/0.58  % (1700)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.59/0.58  % (1699)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.59/0.58  % (1702)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.75/0.59  % (1688)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.75/0.59  % (1691)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.75/0.59  % (1693)Refutation not found, incomplete strategy% (1693)------------------------------
% 1.75/0.59  % (1693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (1693)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.59  
% 1.75/0.59  % (1693)Memory used [KB]: 10746
% 1.75/0.59  % (1693)Time elapsed: 0.170 s
% 1.75/0.59  % (1693)------------------------------
% 1.75/0.59  % (1693)------------------------------
% 1.75/0.60  % (1674)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.75/0.62  % (1701)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.75/0.63  % (1694)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.75/0.64  % (1679)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 2.23/0.67  % (1699)Refutation found. Thanks to Tanya!
% 2.23/0.67  % SZS status Theorem for theBenchmark
% 2.23/0.67  % SZS output start Proof for theBenchmark
% 2.23/0.67  fof(f660,plain,(
% 2.23/0.67    $false),
% 2.23/0.67    inference(unit_resulting_resolution,[],[f60,f653,f82])).
% 2.23/0.67  fof(f82,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f33])).
% 2.23/0.67  fof(f33,plain,(
% 2.23/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.67    inference(ennf_transformation,[],[f9])).
% 2.23/0.67  fof(f9,axiom,(
% 2.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.23/0.67  fof(f653,plain,(
% 2.23/0.67    ~v1_relat_1(sK3)),
% 2.23/0.67    inference(subsumption_resolution,[],[f652,f66])).
% 2.23/0.67  fof(f66,plain,(
% 2.23/0.67    k2_funct_1(sK2) != sK3),
% 2.23/0.67    inference(cnf_transformation,[],[f52])).
% 2.23/0.67  fof(f52,plain,(
% 2.23/0.67    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.23/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f51,f50])).
% 2.23/0.69  fof(f50,plain,(
% 2.23/0.69    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.23/0.69    introduced(choice_axiom,[])).
% 2.23/0.69  fof(f51,plain,(
% 2.23/0.69    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.23/0.69    introduced(choice_axiom,[])).
% 2.23/0.69  fof(f24,plain,(
% 2.23/0.69    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.23/0.69    inference(flattening,[],[f23])).
% 2.23/0.69  fof(f23,plain,(
% 2.23/0.69    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.23/0.69    inference(ennf_transformation,[],[f22])).
% 2.23/0.69  fof(f22,negated_conjecture,(
% 2.23/0.69    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.23/0.69    inference(negated_conjecture,[],[f21])).
% 2.23/0.69  fof(f21,conjecture,(
% 2.23/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.23/0.69  fof(f652,plain,(
% 2.23/0.69    ~v1_relat_1(sK3) | k2_funct_1(sK2) = sK3),
% 2.23/0.69    inference(subsumption_resolution,[],[f651,f243])).
% 2.23/0.69  fof(f243,plain,(
% 2.23/0.69    sK0 = k2_relat_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f241,f60])).
% 2.23/0.69  fof(f241,plain,(
% 2.23/0.69    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.23/0.69    inference(superposition,[],[f240,f83])).
% 2.23/0.69  fof(f83,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.69    inference(cnf_transformation,[],[f34])).
% 2.23/0.69  fof(f34,plain,(
% 2.23/0.69    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.69    inference(ennf_transformation,[],[f11])).
% 2.23/0.69  fof(f11,axiom,(
% 2.23/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.23/0.69  fof(f240,plain,(
% 2.23/0.69    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f239,f58])).
% 2.23/0.69  fof(f58,plain,(
% 2.23/0.69    v1_funct_1(sK3)),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f239,plain,(
% 2.23/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f238,f59])).
% 2.23/0.69  fof(f59,plain,(
% 2.23/0.69    v1_funct_2(sK3,sK1,sK0)),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f238,plain,(
% 2.23/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f237,f60])).
% 2.23/0.69  fof(f237,plain,(
% 2.23/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f236,f55])).
% 2.23/0.69  fof(f55,plain,(
% 2.23/0.69    v1_funct_1(sK2)),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f236,plain,(
% 2.23/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f235,f56])).
% 2.23/0.69  fof(f56,plain,(
% 2.23/0.69    v1_funct_2(sK2,sK0,sK1)),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f235,plain,(
% 2.23/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f234,f57])).
% 2.23/0.69  fof(f57,plain,(
% 2.23/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f234,plain,(
% 2.23/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f232,f190])).
% 2.23/0.69  fof(f190,plain,(
% 2.23/0.69    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 2.23/0.69    inference(backward_demodulation,[],[f62,f188])).
% 2.23/0.69  fof(f188,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f187,f55])).
% 2.23/0.69  fof(f187,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f186,f57])).
% 2.23/0.69  fof(f186,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f185,f58])).
% 2.23/0.69  fof(f185,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f183,f60])).
% 2.23/0.69  fof(f183,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(resolution,[],[f132,f100])).
% 2.23/0.69  fof(f100,plain,(
% 2.23/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f49])).
% 2.23/0.69  fof(f49,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.23/0.69    inference(flattening,[],[f48])).
% 2.23/0.69  fof(f48,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.23/0.69    inference(ennf_transformation,[],[f13])).
% 2.23/0.69  fof(f13,axiom,(
% 2.23/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.23/0.69  fof(f132,plain,(
% 2.23/0.69    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f129,f71])).
% 2.23/0.69  fof(f71,plain,(
% 2.23/0.69    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.23/0.69    inference(cnf_transformation,[],[f14])).
% 2.23/0.69  fof(f14,axiom,(
% 2.23/0.69    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.23/0.69  fof(f129,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.23/0.69    inference(resolution,[],[f96,f62])).
% 2.23/0.69  fof(f96,plain,(
% 2.23/0.69    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.69    inference(cnf_transformation,[],[f54])).
% 2.23/0.69  fof(f54,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.69    inference(nnf_transformation,[],[f45])).
% 2.23/0.69  fof(f45,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.69    inference(flattening,[],[f44])).
% 2.23/0.69  fof(f44,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.23/0.69    inference(ennf_transformation,[],[f12])).
% 2.23/0.69  fof(f12,axiom,(
% 2.23/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.23/0.69  fof(f62,plain,(
% 2.23/0.69    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f232,plain,(
% 2.23/0.69    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.23/0.69    inference(superposition,[],[f91,f188])).
% 2.23/0.69  fof(f91,plain,(
% 2.23/0.69    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f41])).
% 2.23/0.69  fof(f41,plain,(
% 2.23/0.69    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.23/0.69    inference(flattening,[],[f40])).
% 2.23/0.69  fof(f40,plain,(
% 2.23/0.69    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.23/0.69    inference(ennf_transformation,[],[f17])).
% 2.23/0.69  fof(f17,axiom,(
% 2.23/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.23/0.69  fof(f651,plain,(
% 2.23/0.69    ~v1_relat_1(sK3) | sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3),
% 2.23/0.69    inference(subsumption_resolution,[],[f650,f58])).
% 2.23/0.69  fof(f650,plain,(
% 2.23/0.69    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3),
% 2.23/0.69    inference(trivial_inequality_removal,[],[f642])).
% 2.23/0.69  fof(f642,plain,(
% 2.23/0.69    k6_partfun1(sK1) != k6_partfun1(sK1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3),
% 2.23/0.69    inference(superposition,[],[f415,f587])).
% 2.23/0.69  fof(f587,plain,(
% 2.23/0.69    k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 2.23/0.69    inference(backward_demodulation,[],[f484,f576])).
% 2.23/0.69  fof(f576,plain,(
% 2.23/0.69    sK2 = k2_funct_1(sK3)),
% 2.23/0.69    inference(resolution,[],[f568,f57])).
% 2.23/0.69  fof(f568,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = k2_funct_1(sK3)) )),
% 2.23/0.69    inference(resolution,[],[f557,f82])).
% 2.23/0.69  fof(f557,plain,(
% 2.23/0.69    ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3)),
% 2.23/0.69    inference(trivial_inequality_removal,[],[f556])).
% 2.23/0.69  fof(f556,plain,(
% 2.23/0.69    sK1 != sK1 | ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3)),
% 2.23/0.69    inference(backward_demodulation,[],[f436,f551])).
% 2.23/0.69  fof(f551,plain,(
% 2.23/0.69    sK1 = k1_relat_1(sK3)),
% 2.23/0.69    inference(resolution,[],[f546,f60])).
% 2.23/0.69  fof(f546,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK1 = k1_relat_1(sK3)) )),
% 2.23/0.69    inference(resolution,[],[f545,f82])).
% 2.23/0.69  fof(f545,plain,(
% 2.23/0.69    ~v1_relat_1(sK3) | sK1 = k1_relat_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f544,f58])).
% 2.23/0.69  fof(f544,plain,(
% 2.23/0.69    sK1 = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f542,f259])).
% 2.23/0.69  fof(f259,plain,(
% 2.23/0.69    v2_funct_1(sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f258,f55])).
% 2.23/0.69  fof(f258,plain,(
% 2.23/0.69    v2_funct_1(sK3) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f257,f56])).
% 2.23/0.69  fof(f257,plain,(
% 2.23/0.69    v2_funct_1(sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f256,f57])).
% 2.23/0.69  fof(f256,plain,(
% 2.23/0.69    v2_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f255,f58])).
% 2.23/0.69  fof(f255,plain,(
% 2.23/0.69    v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f254,f59])).
% 2.23/0.69  fof(f254,plain,(
% 2.23/0.69    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f253,f60])).
% 2.23/0.69  fof(f253,plain,(
% 2.23/0.69    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f252,f61])).
% 2.23/0.69  fof(f61,plain,(
% 2.23/0.69    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f252,plain,(
% 2.23/0.69    sK1 != k2_relset_1(sK0,sK1,sK2) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f251,f64])).
% 2.23/0.69  fof(f64,plain,(
% 2.23/0.69    k1_xboole_0 != sK0),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f251,plain,(
% 2.23/0.69    k1_xboole_0 = sK0 | sK1 != k2_relset_1(sK0,sK1,sK2) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f249,f101])).
% 2.23/0.69  fof(f101,plain,(
% 2.23/0.69    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.23/0.69    inference(definition_unfolding,[],[f69,f67])).
% 2.23/0.69  fof(f67,plain,(
% 2.23/0.69    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f16])).
% 2.23/0.69  fof(f16,axiom,(
% 2.23/0.69    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.23/0.69  fof(f69,plain,(
% 2.23/0.69    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.23/0.69    inference(cnf_transformation,[],[f6])).
% 2.23/0.69  fof(f6,axiom,(
% 2.23/0.69    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.23/0.69  fof(f249,plain,(
% 2.23/0.69    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | sK1 != k2_relset_1(sK0,sK1,sK2) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(superposition,[],[f94,f188])).
% 2.23/0.69  fof(f94,plain,(
% 2.23/0.69    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | v2_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f43])).
% 2.23/0.69  fof(f43,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.23/0.69    inference(flattening,[],[f42])).
% 2.23/0.69  fof(f42,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.23/0.69    inference(ennf_transformation,[],[f18])).
% 2.23/0.69  fof(f18,axiom,(
% 2.23/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.23/0.69  fof(f542,plain,(
% 2.23/0.69    sK1 = k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.23/0.69    inference(superposition,[],[f538,f77])).
% 2.23/0.69  fof(f77,plain,(
% 2.23/0.69    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f29])).
% 2.23/0.69  fof(f29,plain,(
% 2.23/0.69    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.69    inference(flattening,[],[f28])).
% 2.23/0.69  fof(f28,plain,(
% 2.23/0.69    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.23/0.69    inference(ennf_transformation,[],[f7])).
% 2.23/0.69  fof(f7,axiom,(
% 2.23/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.23/0.69  fof(f538,plain,(
% 2.23/0.69    sK1 = k2_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(subsumption_resolution,[],[f537,f59])).
% 2.23/0.69  fof(f537,plain,(
% 2.23/0.69    sK1 = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0)),
% 2.23/0.69    inference(subsumption_resolution,[],[f536,f240])).
% 2.23/0.69  fof(f536,plain,(
% 2.23/0.69    sK0 != k2_relset_1(sK1,sK0,sK3) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0)),
% 2.23/0.69    inference(resolution,[],[f524,f60])).
% 2.23/0.69  fof(f524,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK3) != X1 | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_2(sK3,X0,X1)) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f523,f58])).
% 2.23/0.69  fof(f523,plain,(
% 2.23/0.69    ( ! [X0,X1] : (sK1 = k2_relat_1(k2_funct_1(sK3)) | k2_relset_1(X0,X1,sK3) != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f522,f259])).
% 2.23/0.69  fof(f522,plain,(
% 2.23/0.69    ( ! [X0,X1] : (sK1 = k2_relat_1(k2_funct_1(sK3)) | k2_relset_1(X0,X1,sK3) != X1 | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 2.23/0.69    inference(resolution,[],[f520,f88])).
% 2.23/0.69  fof(f88,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f37])).
% 2.23/0.69  fof(f37,plain,(
% 2.23/0.69    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.23/0.69    inference(flattening,[],[f36])).
% 2.23/0.69  fof(f36,plain,(
% 2.23/0.69    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.23/0.69    inference(ennf_transformation,[],[f19])).
% 2.23/0.69  fof(f19,axiom,(
% 2.23/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.23/0.69  fof(f520,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK1 = k2_relat_1(k2_funct_1(sK3))) )),
% 2.23/0.69    inference(resolution,[],[f518,f82])).
% 2.23/0.69  fof(f518,plain,(
% 2.23/0.69    ~v1_relat_1(k2_funct_1(sK3)) | sK1 = k2_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(resolution,[],[f515,f60])).
% 2.23/0.69  fof(f515,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(k2_funct_1(sK3)) | sK1 = k2_relat_1(k2_funct_1(sK3))) )),
% 2.23/0.69    inference(resolution,[],[f505,f82])).
% 2.23/0.69  fof(f505,plain,(
% 2.23/0.69    ~v1_relat_1(sK3) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(subsumption_resolution,[],[f504,f133])).
% 2.23/0.69  fof(f133,plain,(
% 2.23/0.69    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.23/0.69    inference(resolution,[],[f116,f71])).
% 2.23/0.69  fof(f116,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(X0,X1)) )),
% 2.23/0.69    inference(superposition,[],[f113,f104])).
% 2.23/0.69  fof(f104,plain,(
% 2.23/0.69    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.23/0.69    inference(definition_unfolding,[],[f72,f67])).
% 2.23/0.69  fof(f72,plain,(
% 2.23/0.69    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.23/0.69    inference(cnf_transformation,[],[f5])).
% 2.23/0.69  fof(f5,axiom,(
% 2.23/0.69    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.23/0.69  fof(f113,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f112,f82])).
% 2.23/0.69  fof(f112,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 2.23/0.69    inference(resolution,[],[f84,f80])).
% 2.23/0.69  fof(f80,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f53])).
% 2.23/0.69  fof(f53,plain,(
% 2.23/0.69    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.23/0.69    inference(nnf_transformation,[],[f32])).
% 2.23/0.69  fof(f32,plain,(
% 2.23/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/0.69    inference(ennf_transformation,[],[f2])).
% 2.23/0.69  fof(f2,axiom,(
% 2.23/0.69    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.23/0.69  fof(f84,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.69    inference(cnf_transformation,[],[f35])).
% 2.23/0.69  fof(f35,plain,(
% 2.23/0.69    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.69    inference(ennf_transformation,[],[f10])).
% 2.23/0.69  fof(f10,axiom,(
% 2.23/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.23/0.69  fof(f504,plain,(
% 2.23/0.69    ~r1_tarski(sK0,sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(forward_demodulation,[],[f503,f291])).
% 2.23/0.69  fof(f291,plain,(
% 2.23/0.69    sK0 = k1_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(resolution,[],[f278,f60])).
% 2.23/0.69  fof(f278,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k1_relat_1(k2_funct_1(sK3))) )),
% 2.23/0.69    inference(resolution,[],[f260,f82])).
% 2.23/0.69  fof(f260,plain,(
% 2.23/0.69    ~v1_relat_1(sK3) | sK0 = k1_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(resolution,[],[f259,f244])).
% 2.23/0.69  fof(f244,plain,(
% 2.23/0.69    ~v2_funct_1(sK3) | sK0 = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 2.23/0.69    inference(backward_demodulation,[],[f118,f243])).
% 2.23/0.69  fof(f118,plain,(
% 2.23/0.69    ~v2_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 2.23/0.69    inference(resolution,[],[f76,f58])).
% 2.23/0.69  fof(f76,plain,(
% 2.23/0.69    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f29])).
% 2.23/0.69  fof(f503,plain,(
% 2.23/0.69    ~r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(forward_demodulation,[],[f502,f243])).
% 2.23/0.69  fof(f502,plain,(
% 2.23/0.69    sK1 = k2_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(forward_demodulation,[],[f489,f103])).
% 2.23/0.69  fof(f103,plain,(
% 2.23/0.69    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.23/0.69    inference(definition_unfolding,[],[f73,f67])).
% 2.23/0.69  fof(f73,plain,(
% 2.23/0.69    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.23/0.69    inference(cnf_transformation,[],[f5])).
% 2.23/0.69  fof(f489,plain,(
% 2.23/0.69    k2_relat_1(k2_funct_1(sK3)) = k2_relat_1(k6_partfun1(sK1)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3))),
% 2.23/0.69    inference(superposition,[],[f74,f484])).
% 2.23/0.69  fof(f74,plain,(
% 2.23/0.69    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f26])).
% 2.23/0.69  fof(f26,plain,(
% 2.23/0.69    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.23/0.69    inference(flattening,[],[f25])).
% 2.23/0.69  fof(f25,plain,(
% 2.23/0.69    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.23/0.69    inference(ennf_transformation,[],[f4])).
% 2.23/0.69  fof(f4,axiom,(
% 2.23/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 2.23/0.69  fof(f436,plain,(
% 2.23/0.69    sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3)),
% 2.23/0.69    inference(forward_demodulation,[],[f435,f125])).
% 2.23/0.69  fof(f125,plain,(
% 2.23/0.69    sK1 = k2_relat_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f123,f57])).
% 2.23/0.69  fof(f123,plain,(
% 2.23/0.69    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.23/0.69    inference(superposition,[],[f83,f61])).
% 2.23/0.69  fof(f435,plain,(
% 2.23/0.69    ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f434,f55])).
% 2.23/0.69  fof(f434,plain,(
% 2.23/0.69    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2)),
% 2.23/0.69    inference(trivial_inequality_removal,[],[f433])).
% 2.23/0.69  fof(f433,plain,(
% 2.23/0.69    k6_partfun1(sK0) != k6_partfun1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2)),
% 2.23/0.69    inference(superposition,[],[f432,f200])).
% 2.23/0.69  fof(f200,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.23/0.69    inference(subsumption_resolution,[],[f199,f55])).
% 2.23/0.69  fof(f199,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f198,f57])).
% 2.23/0.69  fof(f198,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f197,f58])).
% 2.23/0.69  fof(f197,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f193,f60])).
% 2.23/0.69  fof(f193,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.23/0.69    inference(superposition,[],[f188,f98])).
% 2.23/0.69  fof(f98,plain,(
% 2.23/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f47])).
% 2.23/0.69  fof(f47,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.23/0.69    inference(flattening,[],[f46])).
% 2.23/0.69  fof(f46,plain,(
% 2.23/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.23/0.69    inference(ennf_transformation,[],[f15])).
% 2.23/0.69  fof(f15,axiom,(
% 2.23/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.23/0.69  fof(f432,plain,(
% 2.23/0.69    ( ! [X0] : (k6_partfun1(sK0) != k5_relat_1(X0,sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK3) = X0 | k2_relat_1(X0) != k1_relat_1(sK3)) )),
% 2.23/0.69    inference(resolution,[],[f371,f60])).
% 2.23/0.69  fof(f371,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK3) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_partfun1(sK0) != k5_relat_1(X0,sK3) | k2_relat_1(X0) != k1_relat_1(sK3)) )),
% 2.23/0.69    inference(resolution,[],[f267,f82])).
% 2.23/0.69  fof(f267,plain,(
% 2.23/0.69    ( ! [X4] : (~v1_relat_1(sK3) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k6_partfun1(sK0) != k5_relat_1(X4,sK3)) )),
% 2.23/0.69    inference(forward_demodulation,[],[f266,f243])).
% 2.23/0.69  fof(f266,plain,(
% 2.23/0.69    ( ! [X4] : (k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X4,sK3) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_relat_1(sK3)) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f263,f58])).
% 2.23/0.69  fof(f263,plain,(
% 2.23/0.69    ( ! [X4] : (k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X4,sK3) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 2.23/0.69    inference(resolution,[],[f259,f105])).
% 2.23/0.69  fof(f105,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~v2_funct_1(X0) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.69    inference(definition_unfolding,[],[f78,f67])).
% 2.23/0.69  fof(f78,plain,(
% 2.23/0.69    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f31])).
% 2.23/0.69  fof(f31,plain,(
% 2.23/0.69    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.69    inference(flattening,[],[f30])).
% 2.23/0.69  fof(f30,plain,(
% 2.23/0.69    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.23/0.69    inference(ennf_transformation,[],[f8])).
% 2.23/0.69  fof(f8,axiom,(
% 2.23/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 2.23/0.69  fof(f484,plain,(
% 2.23/0.69    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.23/0.69    inference(subsumption_resolution,[],[f483,f59])).
% 2.23/0.69  fof(f483,plain,(
% 2.23/0.69    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0)),
% 2.23/0.69    inference(subsumption_resolution,[],[f482,f64])).
% 2.23/0.69  fof(f482,plain,(
% 2.23/0.69    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0)),
% 2.23/0.69    inference(subsumption_resolution,[],[f481,f240])).
% 2.23/0.69  fof(f481,plain,(
% 2.23/0.69    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | sK0 != k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0)),
% 2.23/0.69    inference(resolution,[],[f265,f60])).
% 2.23/0.69  fof(f265,plain,(
% 2.23/0.69    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3)) | k2_relset_1(X3,X2,sK3) != X2 | k1_xboole_0 = X2 | ~v1_funct_2(sK3,X3,X2)) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f262,f58])).
% 2.23/0.69  fof(f262,plain,(
% 2.23/0.69    ( ! [X2,X3] : (k1_xboole_0 = X2 | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3)) | k2_relset_1(X3,X2,sK3) != X2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK3,X3,X2) | ~v1_funct_1(sK3)) )),
% 2.23/0.69    inference(resolution,[],[f259,f89])).
% 2.23/0.69  fof(f89,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.23/0.69    inference(cnf_transformation,[],[f39])).
% 2.23/0.69  fof(f39,plain,(
% 2.23/0.69    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.23/0.69    inference(flattening,[],[f38])).
% 2.23/0.69  fof(f38,plain,(
% 2.23/0.69    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.23/0.69    inference(ennf_transformation,[],[f20])).
% 2.23/0.69  fof(f20,axiom,(
% 2.23/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.23/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.23/0.69  fof(f415,plain,(
% 2.23/0.69    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != sK0 | k2_funct_1(sK2) = X0) )),
% 2.23/0.69    inference(resolution,[],[f410,f57])).
% 2.23/0.69  fof(f410,plain,(
% 2.23/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != sK0 | k5_relat_1(X0,sK2) != k6_partfun1(sK1)) )),
% 2.23/0.69    inference(resolution,[],[f405,f82])).
% 2.23/0.69  fof(f405,plain,(
% 2.23/0.69    ( ! [X0] : (~v1_relat_1(sK2) | k5_relat_1(X0,sK2) != k6_partfun1(sK1) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != sK0) )),
% 2.23/0.69    inference(backward_demodulation,[],[f152,f404])).
% 2.23/0.69  fof(f404,plain,(
% 2.23/0.69    sK0 = k1_relat_1(sK2)),
% 2.23/0.69    inference(resolution,[],[f399,f57])).
% 2.23/0.69  fof(f399,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k1_relat_1(sK2)) )),
% 2.23/0.69    inference(resolution,[],[f395,f82])).
% 2.23/0.69  fof(f395,plain,(
% 2.23/0.69    ~v1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f394,f55])).
% 2.23/0.69  fof(f394,plain,(
% 2.23/0.69    sK0 = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.23/0.69    inference(subsumption_resolution,[],[f392,f63])).
% 2.23/0.69  fof(f63,plain,(
% 2.23/0.69    v2_funct_1(sK2)),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f392,plain,(
% 2.23/0.69    sK0 = k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.23/0.69    inference(superposition,[],[f391,f77])).
% 2.23/0.69  fof(f391,plain,(
% 2.23/0.69    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(subsumption_resolution,[],[f390,f56])).
% 2.23/0.69  fof(f390,plain,(
% 2.23/0.69    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1)),
% 2.23/0.69    inference(subsumption_resolution,[],[f389,f61])).
% 2.23/0.69  fof(f389,plain,(
% 2.23/0.69    sK1 != k2_relset_1(sK0,sK1,sK2) | sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1)),
% 2.23/0.69    inference(resolution,[],[f328,f57])).
% 2.23/0.69  fof(f328,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,X0,X1)) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f327,f55])).
% 2.23/0.69  fof(f327,plain,(
% 2.23/0.69    ( ! [X0,X1] : (sK0 = k2_relat_1(k2_funct_1(sK2)) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f326,f63])).
% 2.23/0.69  fof(f326,plain,(
% 2.23/0.69    ( ! [X0,X1] : (sK0 = k2_relat_1(k2_funct_1(sK2)) | k2_relset_1(X0,X1,sK2) != X1 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 2.23/0.69    inference(resolution,[],[f324,f88])).
% 2.23/0.69  fof(f324,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k2_relat_1(k2_funct_1(sK2))) )),
% 2.23/0.69    inference(resolution,[],[f323,f82])).
% 2.23/0.69  fof(f323,plain,(
% 2.23/0.69    ~v1_relat_1(k2_funct_1(sK2)) | sK0 = k2_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(resolution,[],[f281,f57])).
% 2.23/0.69  fof(f281,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(k2_funct_1(sK2)) | sK0 = k2_relat_1(k2_funct_1(sK2))) )),
% 2.23/0.69    inference(resolution,[],[f277,f82])).
% 2.23/0.69  fof(f277,plain,(
% 2.23/0.69    ~v1_relat_1(sK2) | sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(subsumption_resolution,[],[f276,f133])).
% 2.23/0.69  fof(f276,plain,(
% 2.23/0.69    ~r1_tarski(sK1,sK1) | sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(forward_demodulation,[],[f275,f126])).
% 2.23/0.69  fof(f126,plain,(
% 2.23/0.69    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(backward_demodulation,[],[f122,f125])).
% 2.23/0.69  fof(f122,plain,(
% 2.23/0.69    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(resolution,[],[f120,f57])).
% 2.23/0.69  fof(f120,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))) )),
% 2.23/0.69    inference(resolution,[],[f119,f82])).
% 2.23/0.69  fof(f119,plain,(
% 2.23/0.69    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(subsumption_resolution,[],[f117,f63])).
% 2.23/0.69  fof(f117,plain,(
% 2.23/0.69    ~v2_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.23/0.69    inference(resolution,[],[f76,f55])).
% 2.23/0.69  fof(f275,plain,(
% 2.23/0.69    ~r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) | sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(forward_demodulation,[],[f274,f125])).
% 2.23/0.69  fof(f274,plain,(
% 2.23/0.69    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(forward_demodulation,[],[f273,f103])).
% 2.23/0.69  fof(f273,plain,(
% 2.23/0.69    k2_relat_1(k6_partfun1(sK0)) = k2_relat_1(k2_funct_1(sK2)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))),
% 2.23/0.69    inference(superposition,[],[f74,f271])).
% 2.23/0.69  fof(f271,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.23/0.69    inference(subsumption_resolution,[],[f270,f56])).
% 2.23/0.69  fof(f270,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1)),
% 2.23/0.69    inference(subsumption_resolution,[],[f269,f65])).
% 2.23/0.69  fof(f65,plain,(
% 2.23/0.69    k1_xboole_0 != sK1),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  fof(f269,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 2.23/0.69    inference(subsumption_resolution,[],[f268,f61])).
% 2.23/0.69  fof(f268,plain,(
% 2.23/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 2.23/0.69    inference(resolution,[],[f182,f57])).
% 2.23/0.69  fof(f182,plain,(
% 2.23/0.69    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) | k2_relset_1(X1,X0,sK2) != X0 | k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X0)) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f180,f55])).
% 2.23/0.69  fof(f180,plain,(
% 2.23/0.69    ( ! [X0,X1] : (k1_xboole_0 = X0 | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | ~v1_funct_1(sK2)) )),
% 2.23/0.69    inference(resolution,[],[f89,f63])).
% 2.23/0.69  fof(f152,plain,(
% 2.23/0.69    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(sK1) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 2.23/0.69    inference(forward_demodulation,[],[f151,f125])).
% 2.23/0.69  fof(f151,plain,(
% 2.23/0.69    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 2.23/0.69    inference(subsumption_resolution,[],[f149,f55])).
% 2.23/0.69  fof(f149,plain,(
% 2.23/0.69    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 2.23/0.69    inference(resolution,[],[f105,f63])).
% 2.23/0.69  fof(f60,plain,(
% 2.23/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.23/0.69    inference(cnf_transformation,[],[f52])).
% 2.23/0.69  % SZS output end Proof for theBenchmark
% 2.23/0.69  % (1699)------------------------------
% 2.23/0.69  % (1699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.69  % (1699)Termination reason: Refutation
% 2.23/0.69  
% 2.23/0.69  % (1699)Memory used [KB]: 6780
% 2.23/0.69  % (1699)Time elapsed: 0.241 s
% 2.23/0.69  % (1699)------------------------------
% 2.23/0.69  % (1699)------------------------------
% 2.23/0.70  % (1671)Success in time 0.336 s
%------------------------------------------------------------------------------
