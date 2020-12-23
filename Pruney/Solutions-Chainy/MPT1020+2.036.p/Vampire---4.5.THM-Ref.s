%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  155 (2254 expanded)
%              Number of leaves         :   20 ( 675 expanded)
%              Depth                    :   30
%              Number of atoms          :  567 (17970 expanded)
%              Number of equality atoms :  167 ( 818 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(subsumption_resolution,[],[f343,f222])).

fof(f222,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f95,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f95,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f88,f59])).

fof(f59,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f65,f62])).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f343,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f317,f273])).

fof(f273,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f237,f239])).

fof(f239,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f238,f111])).

fof(f111,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f238,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f138,f216])).

fof(f216,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f215,f49])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f215,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f214,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f214,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f213,f87])).

fof(f87,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f57,f62])).

fof(f57,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f213,plain,
    ( k1_xboole_0 = sK0
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f211,f165])).

fof(f165,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f113,f164])).

fof(f164,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f163,f96])).

fof(f96,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f73,f52])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f163,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f162,f105])).

fof(f105,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f75,f52])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f162,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f128,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f128,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f127,f52])).

fof(f127,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f125,f49])).

fof(f125,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f113,plain,(
    k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f74,f52])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f211,plain,
    ( k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f161,f50])).

fof(f50,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f161,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,sK0,sK0)
      | k1_xboole_0 = sK0
      | sK0 != k2_relset_1(sK0,sK0,X1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k2_funct_1(X1) = sK2
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f160,f53])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f160,plain,(
    ! [X1] :
      ( k2_funct_1(X1) = sK2
      | k1_xboole_0 = sK0
      | sK0 != k2_relset_1(sK0,sK0,X1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f156,f56])).

fof(f156,plain,(
    ! [X1] :
      ( k2_funct_1(X1) = sK2
      | k1_xboole_0 = sK0
      | sK0 != k2_relset_1(sK0,sK0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X1] :
      ( k2_funct_1(X1) = sK2
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | sK0 != k2_relset_1(sK0,sK0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f92,f54])).

% (6890)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

% (6883)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f91,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f79,f62])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

% (6890)Refutation not found, incomplete strategy% (6890)------------------------------
% (6890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6890)Termination reason: Refutation not found, incomplete strategy

% (6890)Memory used [KB]: 1663
% (6890)Time elapsed: 0.002 s
% (6890)------------------------------
% (6890)------------------------------
fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f81,f62])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
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
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
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
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
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
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f138,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f58,f137])).

fof(f137,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f136,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f135,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f133,f52])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f72,f50])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f58,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f237,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f122,f169])).

fof(f169,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f168,f97])).

fof(f97,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f56])).

fof(f168,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f167,f106])).

fof(f106,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f75,f56])).

fof(f167,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f130,f70])).

fof(f130,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f129,f56])).

fof(f129,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f126,f53])).

fof(f126,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f122,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f97,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

% (6889)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (6882)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (6873)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (6888)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f317,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f298,f316])).

fof(f316,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f315,f59])).

fof(f315,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f314,f60])).

fof(f60,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

% (6887)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f314,plain,
    ( k1_xboole_0 != k6_relat_1(k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f313,f181])).

fof(f181,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f180,f59])).

fof(f180,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k6_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f179,f61])).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f179,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k6_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f94,f66])).

% (6874)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (6873)Refutation not found, incomplete strategy% (6873)------------------------------
% (6873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6873)Termination reason: Refutation not found, incomplete strategy

% (6873)Memory used [KB]: 10746
% (6873)Time elapsed: 0.150 s
% (6873)------------------------------
% (6873)------------------------------
% (6881)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (6879)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (6875)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (6887)Refutation not found, incomplete strategy% (6887)------------------------------
% (6887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6887)Termination reason: Refutation not found, incomplete strategy

% (6887)Memory used [KB]: 6396
% (6887)Time elapsed: 0.152 s
% (6887)------------------------------
% (6887)------------------------------
% (6875)Refutation not found, incomplete strategy% (6875)------------------------------
% (6875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6875)Termination reason: Refutation not found, incomplete strategy
% (6877)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark

% (6875)Memory used [KB]: 1791
% (6875)Time elapsed: 0.150 s
% (6875)------------------------------
% (6875)------------------------------
% (6870)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (6885)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f94,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f63,f59])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f313,plain,
    ( k6_relat_1(k1_relat_1(k1_xboole_0)) != k5_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f312,f274])).

fof(f274,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f271])).

fof(f271,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f236,f239])).

fof(f236,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f104,f164])).

fof(f104,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f68,f96])).

fof(f312,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f311,f274])).

fof(f311,plain,
    ( sK1 = k2_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f301,f60])).

fof(f301,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | sK1 = k2_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f267,f274])).

fof(f267,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | sK1 = k2_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f186,f239])).

fof(f186,plain,
    ( sK0 != k1_relat_1(sK1)
    | sK1 = k2_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f185,f164])).

fof(f185,plain,
    ( k2_relat_1(sK1) != k1_relat_1(sK1)
    | sK1 = k2_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f184,f96])).

fof(f184,plain,
    ( k2_relat_1(sK1) != k1_relat_1(sK1)
    | sK1 = k2_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f182,f119])).

fof(f119,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f118,f52])).

fof(f118,plain,
    ( v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f116,f49])).

fof(f116,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f77,f51])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f182,plain,
    ( k2_relat_1(sK1) != k1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | sK1 = k2_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f144,f49])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(sK1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f142,f96])).

fof(f142,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,sK1)
      | k2_relat_1(X0) != k1_relat_1(sK1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK1
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

% (6879)Refutation not found, incomplete strategy% (6879)------------------------------
% (6879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6879)Termination reason: Refutation not found, incomplete strategy

% (6879)Memory used [KB]: 1791
% (6879)Time elapsed: 0.151 s
% (6879)------------------------------
% (6879)------------------------------
fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f298,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f255,f274])).

fof(f255,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f138,f239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:01:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (6866)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (6865)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (6884)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (6876)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (6862)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (6862)Refutation not found, incomplete strategy% (6862)------------------------------
% 0.22/0.53  % (6862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6862)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6862)Memory used [KB]: 1791
% 0.22/0.53  % (6862)Time elapsed: 0.107 s
% 0.22/0.53  % (6862)------------------------------
% 0.22/0.53  % (6862)------------------------------
% 0.22/0.53  % (6867)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (6868)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (6861)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (6863)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (6868)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.55  % (6869)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f352,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(subsumption_resolution,[],[f343,f222])).
% 1.40/0.55  fof(f222,plain,(
% 1.40/0.55    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.40/0.55    inference(resolution,[],[f95,f86])).
% 1.40/0.55  fof(f86,plain,(
% 1.40/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f85])).
% 1.40/0.55  fof(f85,plain,(
% 1.40/0.55    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(equality_resolution,[],[f83])).
% 1.40/0.55  fof(f83,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f48])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(nnf_transformation,[],[f43])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(flattening,[],[f42])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.40/0.55    inference(ennf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.40/0.55  fof(f95,plain,(
% 1.40/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.40/0.55    inference(superposition,[],[f88,f59])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.40/0.55    inference(cnf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.40/0.55  fof(f88,plain,(
% 1.40/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.40/0.55    inference(forward_demodulation,[],[f65,f62])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,axiom,(
% 1.40/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.40/0.55  fof(f65,plain,(
% 1.40/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.40/0.55    inference(pure_predicate_removal,[],[f13])).
% 1.40/0.55  fof(f13,axiom,(
% 1.40/0.55    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.40/0.55  fof(f343,plain,(
% 1.40/0.55    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.40/0.55    inference(backward_demodulation,[],[f317,f273])).
% 1.40/0.55  fof(f273,plain,(
% 1.40/0.55    k1_xboole_0 = sK2),
% 1.40/0.55    inference(trivial_inequality_removal,[],[f272])).
% 1.40/0.55  fof(f272,plain,(
% 1.40/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 1.40/0.55    inference(backward_demodulation,[],[f237,f239])).
% 1.40/0.55  fof(f239,plain,(
% 1.40/0.55    k1_xboole_0 = sK0),
% 1.40/0.55    inference(subsumption_resolution,[],[f238,f111])).
% 1.40/0.55  fof(f111,plain,(
% 1.40/0.55    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.40/0.55    inference(resolution,[],[f86,f56])).
% 1.40/0.55  fof(f56,plain,(
% 1.40/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f46,plain,(
% 1.40/0.55    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f45,f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f45,plain,(
% 1.40/0.55    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.40/0.55    inference(flattening,[],[f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.40/0.55    inference(negated_conjecture,[],[f18])).
% 1.40/0.55  fof(f18,conjecture,(
% 1.40/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 1.40/0.55  fof(f238,plain,(
% 1.40/0.55    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0),
% 1.40/0.55    inference(superposition,[],[f138,f216])).
% 1.40/0.55  fof(f216,plain,(
% 1.40/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0),
% 1.40/0.55    inference(subsumption_resolution,[],[f215,f49])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    v1_funct_1(sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f215,plain,(
% 1.40/0.55    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f214,f52])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f214,plain,(
% 1.40/0.55    k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f213,f87])).
% 1.40/0.55  fof(f87,plain,(
% 1.40/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 1.40/0.55    inference(forward_demodulation,[],[f57,f62])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f213,plain,(
% 1.40/0.55    k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f211,f165])).
% 1.40/0.55  fof(f165,plain,(
% 1.40/0.55    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.40/0.55    inference(backward_demodulation,[],[f113,f164])).
% 1.40/0.55  fof(f164,plain,(
% 1.40/0.55    sK0 = k2_relat_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f163,f96])).
% 1.40/0.55  fof(f96,plain,(
% 1.40/0.55    v1_relat_1(sK1)),
% 1.40/0.55    inference(resolution,[],[f73,f52])).
% 1.40/0.55  fof(f73,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.40/0.55  fof(f163,plain,(
% 1.40/0.55    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f162,f105])).
% 1.40/0.55  fof(f105,plain,(
% 1.40/0.55    v5_relat_1(sK1,sK0)),
% 1.40/0.55    inference(resolution,[],[f75,f52])).
% 1.40/0.55  fof(f75,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f35])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.40/0.55    inference(pure_predicate_removal,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.40/0.55  fof(f162,plain,(
% 1.40/0.55    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.40/0.55    inference(resolution,[],[f128,f70])).
% 1.40/0.55  fof(f70,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f47])).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f30])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(flattening,[],[f29])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,axiom,(
% 1.40/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.40/0.55  fof(f128,plain,(
% 1.40/0.55    v2_funct_2(sK1,sK0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f127,f52])).
% 1.40/0.55  fof(f127,plain,(
% 1.40/0.55    v2_funct_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.55    inference(subsumption_resolution,[],[f125,f49])).
% 1.40/0.55  fof(f125,plain,(
% 1.40/0.55    v2_funct_2(sK1,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.55    inference(resolution,[],[f78,f51])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    v3_funct_2(sK1,sK0,sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f78,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(flattening,[],[f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.40/0.55  fof(f113,plain,(
% 1.40/0.55    k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1)),
% 1.40/0.55    inference(resolution,[],[f74,f52])).
% 1.40/0.55  fof(f74,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.40/0.55  fof(f211,plain,(
% 1.40/0.55    k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.40/0.55    inference(resolution,[],[f161,f50])).
% 1.40/0.55  fof(f50,plain,(
% 1.40/0.55    v1_funct_2(sK1,sK0,sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f161,plain,(
% 1.40/0.55    ( ! [X1] : (~v1_funct_2(X1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,X1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_1(X1) = sK2 | ~v1_funct_1(X1)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f160,f53])).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    v1_funct_1(sK2)),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f160,plain,(
% 1.40/0.55    ( ! [X1] : (k2_funct_1(X1) = sK2 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,X1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X1,sK0,sK0) | ~v1_funct_1(X1)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f156,f56])).
% 1.40/0.55  fof(f156,plain,(
% 1.40/0.55    ( ! [X1] : (k2_funct_1(X1) = sK2 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X1,sK0,sK0) | ~v1_funct_1(X1)) )),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f155])).
% 1.40/0.55  fof(f155,plain,(
% 1.40/0.55    ( ! [X1] : (k2_funct_1(X1) = sK2 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X1,sK0,sK0) | ~v1_funct_1(X1)) )),
% 1.40/0.55    inference(resolution,[],[f92,f54])).
% 1.40/0.55  % (6890)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    v1_funct_2(sK2,sK0,sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  % (6883)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.40/0.55  fof(f92,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f91,f90])).
% 1.40/0.55  fof(f90,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.40/0.55    inference(forward_demodulation,[],[f79,f62])).
% 1.40/0.55  fof(f79,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f39])).
% 1.40/0.55  % (6890)Refutation not found, incomplete strategy% (6890)------------------------------
% 1.40/0.55  % (6890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (6890)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (6890)Memory used [KB]: 1663
% 1.40/0.55  % (6890)Time elapsed: 0.002 s
% 1.40/0.55  % (6890)------------------------------
% 1.40/0.55  % (6890)------------------------------
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.40/0.55    inference(flattening,[],[f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.40/0.55    inference(ennf_transformation,[],[f16])).
% 1.40/0.55  fof(f16,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.40/0.55  fof(f91,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.40/0.55    inference(forward_demodulation,[],[f81,f62])).
% 1.40/0.55  fof(f81,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f41])).
% 1.40/0.55  fof(f41,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.40/0.55    inference(flattening,[],[f40])).
% 1.40/0.55  fof(f40,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.40/0.55    inference(ennf_transformation,[],[f17])).
% 1.40/0.55  fof(f17,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.40/0.55  fof(f138,plain,(
% 1.40/0.55    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 1.40/0.55    inference(backward_demodulation,[],[f58,f137])).
% 1.40/0.55  fof(f137,plain,(
% 1.40/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f136,f49])).
% 1.40/0.55  fof(f136,plain,(
% 1.40/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f135,f51])).
% 1.40/0.55  fof(f135,plain,(
% 1.40/0.55    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f133,f52])).
% 1.40/0.55  fof(f133,plain,(
% 1.40/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.40/0.55    inference(resolution,[],[f72,f50])).
% 1.40/0.55  fof(f72,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f32])).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.40/0.55    inference(flattening,[],[f31])).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f14])).
% 1.40/0.55  fof(f14,axiom,(
% 1.40/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.40/0.55  fof(f58,plain,(
% 1.40/0.55    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f237,plain,(
% 1.40/0.55    k1_xboole_0 != sK0 | k1_xboole_0 = sK2),
% 1.40/0.55    inference(superposition,[],[f122,f169])).
% 1.40/0.55  fof(f169,plain,(
% 1.40/0.55    sK0 = k2_relat_1(sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f168,f97])).
% 1.40/0.55  fof(f97,plain,(
% 1.40/0.55    v1_relat_1(sK2)),
% 1.40/0.55    inference(resolution,[],[f73,f56])).
% 1.40/0.55  fof(f168,plain,(
% 1.40/0.55    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f167,f106])).
% 1.40/0.55  fof(f106,plain,(
% 1.40/0.55    v5_relat_1(sK2,sK0)),
% 1.40/0.55    inference(resolution,[],[f75,f56])).
% 1.40/0.55  fof(f167,plain,(
% 1.40/0.55    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.40/0.55    inference(resolution,[],[f130,f70])).
% 1.40/0.55  fof(f130,plain,(
% 1.40/0.55    v2_funct_2(sK2,sK0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f129,f56])).
% 1.40/0.55  fof(f129,plain,(
% 1.40/0.55    v2_funct_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.55    inference(subsumption_resolution,[],[f126,f53])).
% 1.40/0.55  fof(f126,plain,(
% 1.40/0.55    v2_funct_2(sK2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.55    inference(resolution,[],[f78,f55])).
% 1.40/0.55  fof(f55,plain,(
% 1.40/0.55    v3_funct_2(sK2,sK0,sK0)),
% 1.40/0.55    inference(cnf_transformation,[],[f46])).
% 1.40/0.55  fof(f122,plain,(
% 1.40/0.55    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.40/0.55    inference(resolution,[],[f97,f68])).
% 1.40/0.55  fof(f68,plain,(
% 1.40/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(flattening,[],[f25])).
% 1.40/0.55  % (6889)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.55  % (6882)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.55  % (6873)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.55  % (6888)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.40/0.55  fof(f317,plain,(
% 1.40/0.55    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 1.40/0.55    inference(backward_demodulation,[],[f298,f316])).
% 1.40/0.55  fof(f316,plain,(
% 1.40/0.55    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f315,f59])).
% 1.40/0.55  fof(f315,plain,(
% 1.40/0.55    k1_xboole_0 != k6_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f314,f60])).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.55    inference(cnf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.40/0.55  % (6887)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.55  fof(f314,plain,(
% 1.40/0.55    k1_xboole_0 != k6_relat_1(k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f313,f181])).
% 1.40/0.55  fof(f181,plain,(
% 1.40/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f180,f59])).
% 1.40/0.55  fof(f180,plain,(
% 1.40/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k6_relat_1(k1_xboole_0))),
% 1.40/0.55    inference(forward_demodulation,[],[f179,f61])).
% 1.40/0.55  fof(f61,plain,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.40/0.55    inference(cnf_transformation,[],[f1])).
% 1.40/0.55  fof(f179,plain,(
% 1.40/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k6_relat_1(k2_relat_1(k1_xboole_0)))),
% 1.40/0.55    inference(resolution,[],[f94,f66])).
% 1.40/0.55  % (6874)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.56  % (6873)Refutation not found, incomplete strategy% (6873)------------------------------
% 1.40/0.56  % (6873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (6873)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (6873)Memory used [KB]: 10746
% 1.40/0.56  % (6873)Time elapsed: 0.150 s
% 1.40/0.56  % (6873)------------------------------
% 1.40/0.56  % (6873)------------------------------
% 1.40/0.56  % (6881)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.56  % (6879)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.56  % (6875)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.56  % (6887)Refutation not found, incomplete strategy% (6887)------------------------------
% 1.40/0.56  % (6887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (6887)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (6887)Memory used [KB]: 6396
% 1.40/0.56  % (6887)Time elapsed: 0.152 s
% 1.40/0.56  % (6887)------------------------------
% 1.40/0.56  % (6887)------------------------------
% 1.40/0.56  % (6875)Refutation not found, incomplete strategy% (6875)------------------------------
% 1.40/0.56  % (6875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (6875)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  % (6877)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.56  
% 1.40/0.56  % (6875)Memory used [KB]: 1791
% 1.40/0.56  % (6875)Time elapsed: 0.150 s
% 1.40/0.56  % (6875)------------------------------
% 1.40/0.56  % (6875)------------------------------
% 1.40/0.56  % (6870)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.56  % (6885)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.56  fof(f66,plain,(
% 1.40/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f24])).
% 1.40/0.56  fof(f24,plain,(
% 1.40/0.56    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f3])).
% 1.40/0.56  fof(f3,axiom,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.40/0.56  fof(f94,plain,(
% 1.40/0.56    v1_relat_1(k1_xboole_0)),
% 1.40/0.56    inference(superposition,[],[f63,f59])).
% 1.40/0.56  fof(f63,plain,(
% 1.40/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f5])).
% 1.40/0.56  fof(f5,axiom,(
% 1.40/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.40/0.56  fof(f313,plain,(
% 1.40/0.56    k6_relat_1(k1_relat_1(k1_xboole_0)) != k5_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.40/0.56    inference(forward_demodulation,[],[f312,f274])).
% 1.40/0.56  fof(f274,plain,(
% 1.40/0.56    k1_xboole_0 = sK1),
% 1.40/0.56    inference(trivial_inequality_removal,[],[f271])).
% 1.40/0.56  fof(f271,plain,(
% 1.40/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 1.40/0.56    inference(backward_demodulation,[],[f236,f239])).
% 1.40/0.56  fof(f236,plain,(
% 1.40/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.40/0.56    inference(superposition,[],[f104,f164])).
% 1.40/0.56  fof(f104,plain,(
% 1.40/0.56    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 = sK1),
% 1.40/0.56    inference(resolution,[],[f68,f96])).
% 1.40/0.56  fof(f312,plain,(
% 1.40/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1)),
% 1.40/0.56    inference(forward_demodulation,[],[f311,f274])).
% 1.40/0.56  fof(f311,plain,(
% 1.40/0.56    sK1 = k2_funct_1(sK1) | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1)),
% 1.40/0.56    inference(subsumption_resolution,[],[f301,f60])).
% 1.40/0.56  fof(f301,plain,(
% 1.40/0.56    k1_xboole_0 != k1_relat_1(k1_xboole_0) | sK1 = k2_funct_1(sK1) | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1)),
% 1.40/0.56    inference(backward_demodulation,[],[f267,f274])).
% 1.40/0.56  fof(f267,plain,(
% 1.40/0.56    k1_xboole_0 != k1_relat_1(sK1) | sK1 = k2_funct_1(sK1) | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1)),
% 1.40/0.56    inference(backward_demodulation,[],[f186,f239])).
% 1.40/0.56  fof(f186,plain,(
% 1.40/0.56    sK0 != k1_relat_1(sK1) | sK1 = k2_funct_1(sK1) | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1)),
% 1.40/0.56    inference(forward_demodulation,[],[f185,f164])).
% 1.40/0.56  fof(f185,plain,(
% 1.40/0.56    k2_relat_1(sK1) != k1_relat_1(sK1) | sK1 = k2_funct_1(sK1) | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1)),
% 1.40/0.56    inference(subsumption_resolution,[],[f184,f96])).
% 1.40/0.56  fof(f184,plain,(
% 1.40/0.56    k2_relat_1(sK1) != k1_relat_1(sK1) | sK1 = k2_funct_1(sK1) | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1) | ~v1_relat_1(sK1)),
% 1.40/0.56    inference(subsumption_resolution,[],[f182,f119])).
% 1.40/0.56  fof(f119,plain,(
% 1.40/0.56    v2_funct_1(sK1)),
% 1.40/0.56    inference(subsumption_resolution,[],[f118,f52])).
% 1.40/0.56  fof(f118,plain,(
% 1.40/0.56    v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.56    inference(subsumption_resolution,[],[f116,f49])).
% 1.40/0.56  fof(f116,plain,(
% 1.40/0.56    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.56    inference(resolution,[],[f77,f51])).
% 1.40/0.56  fof(f77,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f37])).
% 1.40/0.56  fof(f182,plain,(
% 1.40/0.56    k2_relat_1(sK1) != k1_relat_1(sK1) | ~v2_funct_1(sK1) | sK1 = k2_funct_1(sK1) | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK1) | ~v1_relat_1(sK1)),
% 1.40/0.56    inference(resolution,[],[f144,f49])).
% 1.40/0.56  fof(f144,plain,(
% 1.40/0.56    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(sK1) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,sK1) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(subsumption_resolution,[],[f142,f96])).
% 1.40/0.56  fof(f142,plain,(
% 1.40/0.56    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,sK1) | k2_relat_1(X0) != k1_relat_1(sK1) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK1 | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(resolution,[],[f69,f49])).
% 1.40/0.56  fof(f69,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | k2_funct_1(X0) = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f28])).
% 1.40/0.56  % (6879)Refutation not found, incomplete strategy% (6879)------------------------------
% 1.40/0.56  % (6879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (6879)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (6879)Memory used [KB]: 1791
% 1.40/0.56  % (6879)Time elapsed: 0.151 s
% 1.40/0.56  % (6879)------------------------------
% 1.40/0.56  % (6879)------------------------------
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(flattening,[],[f27])).
% 1.40/0.56  fof(f27,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f6])).
% 1.40/0.56  fof(f6,axiom,(
% 1.40/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 1.40/0.56  fof(f298,plain,(
% 1.40/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))),
% 1.40/0.56    inference(backward_demodulation,[],[f255,f274])).
% 1.40/0.56  fof(f255,plain,(
% 1.40/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 1.40/0.56    inference(backward_demodulation,[],[f138,f239])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (6868)------------------------------
% 1.40/0.56  % (6868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (6868)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (6868)Memory used [KB]: 1918
% 1.40/0.56  % (6877)Refutation not found, incomplete strategy% (6877)------------------------------
% 1.40/0.56  % (6877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (6868)Time elapsed: 0.089 s
% 1.40/0.56  % (6868)------------------------------
% 1.40/0.56  % (6868)------------------------------
% 1.40/0.56  % (6860)Success in time 0.194 s
%------------------------------------------------------------------------------
