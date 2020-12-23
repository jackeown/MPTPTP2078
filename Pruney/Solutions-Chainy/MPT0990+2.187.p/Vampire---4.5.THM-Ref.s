%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:01 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 858 expanded)
%              Number of leaves         :   26 ( 273 expanded)
%              Depth                    :   34
%              Number of atoms          :  932 (8282 expanded)
%              Number of equality atoms :  232 (2794 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f208,f232,f312,f389,f399,f1827,f1881,f2115])).

fof(f2115,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f2114])).

fof(f2114,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2113,f236])).

fof(f236,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f235,f102])).

fof(f102,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f90,f84])).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f90,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f235,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f234,f141])).

fof(f141,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f140,f55])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f52,f51])).

fof(f51,plain,
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

fof(f52,plain,
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f140,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f139,f56])).

fof(f56,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f139,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f138,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f138,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f137,f63])).

fof(f63,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f137,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f131,f65])).

fof(f65,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f131,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f67,f61])).

fof(f61,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f234,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f114,f197])).

fof(f197,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f114,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f110,f55])).

fof(f110,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f2113,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f2112,f183])).

fof(f183,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f121,f160])).

fof(f160,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f159,f58])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f159,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f158,f59])).

fof(f59,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f158,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f157,f60])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f157,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f156,f55])).

fof(f156,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f155,f56])).

fof(f155,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f153,f57])).

fof(f153,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f62,f83])).

fof(f83,plain,(
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
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f121,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f60,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2112,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f2111])).

fof(f2111,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f2110,f147])).

fof(f147,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f116,f61])).

fof(f116,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f57,f88])).

fof(f2110,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2109,f197])).

fof(f2109,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2108,f55])).

fof(f2108,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2107,f216])).

fof(f216,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2107,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2106,f58])).

fof(f2106,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2105,f63])).

fof(f2105,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2103,f66])).

fof(f66,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f2103,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(superposition,[],[f98,f2089])).

fof(f2089,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f311,f2088])).

fof(f2088,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f2087,f291])).

fof(f291,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl4_5
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2087,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1898,f1974])).

fof(f1974,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1973,f102])).

fof(f1973,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1929,f311])).

fof(f1929,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f1928,f216])).

fof(f1928,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f1921,f58])).

fof(f1921,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f291,f70])).

fof(f1898,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f1897,f147])).

fof(f1897,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f1896])).

fof(f1896,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f1895,f183])).

fof(f1895,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1894,f216])).

fof(f1894,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1893,f58])).

fof(f1893,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1892,f197])).

fof(f1892,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f465,f55])).

fof(f465,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(superposition,[],[f98,f454])).

fof(f454,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f287,f388])).

fof(f388,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl4_12
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f287,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f283,f58])).

fof(f283,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f119,f60])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f117,f55])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f57,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f311,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl4_7
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f84])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f1881,plain,
    ( spl4_5
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f1880])).

fof(f1880,plain,
    ( $false
    | spl4_5
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f1879])).

fof(f1879,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_5
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f1878,f102])).

fof(f1878,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0)))
    | spl4_5
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1877,f1812])).

fof(f1812,plain,
    ( v1_relat_1(k6_partfun1(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f1811])).

fof(f1811,plain,
    ( spl4_19
  <=> v1_relat_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1877,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | spl4_5
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1876,f429])).

fof(f429,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f428,f55])).

fof(f428,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f427,f57])).

fof(f427,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f426,f58])).

fof(f426,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f424,f60])).

fof(f424,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f85,f388])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1876,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | spl4_5
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1875,f463])).

fof(f463,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f462,f388])).

fof(f462,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_5 ),
    inference(subsumption_resolution,[],[f461,f58])).

fof(f461,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f460,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f53])).

fof(f460,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f459,f60])).

fof(f459,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f456,f290])).

fof(f290,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f289])).

fof(f456,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f136,f59])).

fof(f136,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,sK1,X2)
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f135,f55])).

fof(f135,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f134,f56])).

fof(f134,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f132,f57])).

fof(f132,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,(
    ! [X2,X3] :
      ( sK1 != sK1
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f78,f61])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f1875,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0)))
    | v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ spl4_19 ),
    inference(duplicate_literal_removal,[],[f1872])).

fof(f1872,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0)))
    | v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ spl4_19 ),
    inference(superposition,[],[f99,f1871])).

fof(f1871,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f1870,f102])).

fof(f1870,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(sK0))),k6_partfun1(sK0))
    | ~ spl4_19 ),
    inference(resolution,[],[f1812,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f89,f84])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f80,f84])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f1827,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f1826])).

fof(f1826,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f1824,f97])).

fof(f97,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1824,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl4_19 ),
    inference(resolution,[],[f1823,f103])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f96,f84])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f1823,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_19 ),
    inference(resolution,[],[f1813,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1813,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f1811])).

fof(f399,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f397,f55])).

fof(f397,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f396,f57])).

fof(f396,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f395,f58])).

fof(f395,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f394,f60])).

fof(f394,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(resolution,[],[f384,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f384,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl4_11
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f389,plain,
    ( ~ spl4_11
    | spl4_12 ),
    inference(avatar_split_clause,[],[f154,f386,f382])).

fof(f154,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f152,f103])).

fof(f152,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f62,f81])).

fof(f81,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f312,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f178,f289,f309])).

fof(f178,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f177,f58])).

fof(f177,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f176,f59])).

fof(f176,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f175,f60])).

fof(f175,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f166,f64])).

fof(f166,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f67,f160])).

fof(f232,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f229,f97])).

fof(f229,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_3 ),
    inference(resolution,[],[f223,f60])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_3 ),
    inference(resolution,[],[f217,f95])).

fof(f217,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f215])).

fof(f208,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f205,f97])).

fof(f205,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f204,f57])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f198,f95])).

fof(f198,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (27936)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (27944)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (27928)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (27930)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (27922)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (27925)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (27923)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (27924)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (27946)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (27949)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (27937)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (27926)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (27941)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (27938)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (27947)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (27931)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (27938)Refutation not found, incomplete strategy% (27938)------------------------------
% 0.21/0.54  % (27938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27938)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27938)Memory used [KB]: 10746
% 0.21/0.54  % (27938)Time elapsed: 0.120 s
% 0.21/0.54  % (27938)------------------------------
% 0.21/0.54  % (27938)------------------------------
% 0.21/0.54  % (27939)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (27950)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (27927)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (27942)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (27948)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (27929)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (27933)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (27943)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (27951)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (27940)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (27934)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (27935)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (27932)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (27945)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.03/0.63  % (27946)Refutation found. Thanks to Tanya!
% 2.03/0.63  % SZS status Theorem for theBenchmark
% 2.14/0.65  % SZS output start Proof for theBenchmark
% 2.14/0.65  fof(f2116,plain,(
% 2.14/0.65    $false),
% 2.14/0.65    inference(avatar_sat_refutation,[],[f208,f232,f312,f389,f399,f1827,f1881,f2115])).
% 2.14/0.65  fof(f2115,plain,(
% 2.14/0.65    ~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f2114])).
% 2.14/0.65  fof(f2114,plain,(
% 2.14/0.65    $false | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2113,f236])).
% 2.14/0.65  fof(f236,plain,(
% 2.14/0.65    sK0 = k1_relat_1(sK2) | ~spl4_1),
% 2.14/0.65    inference(forward_demodulation,[],[f235,f102])).
% 2.14/0.65  fof(f102,plain,(
% 2.14/0.65    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.14/0.65    inference(definition_unfolding,[],[f90,f84])).
% 2.14/0.65  fof(f84,plain,(
% 2.14/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f15])).
% 2.14/0.65  fof(f15,axiom,(
% 2.14/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.14/0.65  fof(f90,plain,(
% 2.14/0.65    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.14/0.65    inference(cnf_transformation,[],[f3])).
% 2.14/0.65  fof(f3,axiom,(
% 2.14/0.65    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.14/0.65  fof(f235,plain,(
% 2.14/0.65    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~spl4_1),
% 2.14/0.65    inference(forward_demodulation,[],[f234,f141])).
% 2.14/0.65  fof(f141,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.14/0.65    inference(subsumption_resolution,[],[f140,f55])).
% 2.14/0.65  fof(f55,plain,(
% 2.14/0.65    v1_funct_1(sK2)),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f53,plain,(
% 2.14/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.14/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f52,f51])).
% 2.14/0.65  fof(f51,plain,(
% 2.14/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.14/0.65    introduced(choice_axiom,[])).
% 2.14/0.65  fof(f52,plain,(
% 2.14/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.14/0.65    introduced(choice_axiom,[])).
% 2.14/0.65  fof(f23,plain,(
% 2.14/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.14/0.65    inference(flattening,[],[f22])).
% 2.14/0.65  fof(f22,plain,(
% 2.14/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.14/0.65    inference(ennf_transformation,[],[f21])).
% 2.14/0.65  fof(f21,negated_conjecture,(
% 2.14/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.14/0.65    inference(negated_conjecture,[],[f20])).
% 2.14/0.65  fof(f20,conjecture,(
% 2.14/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.14/0.65  fof(f140,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.14/0.65    inference(subsumption_resolution,[],[f139,f56])).
% 2.14/0.65  fof(f56,plain,(
% 2.14/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f139,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.14/0.65    inference(subsumption_resolution,[],[f138,f57])).
% 2.14/0.65  fof(f57,plain,(
% 2.14/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f138,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.14/0.65    inference(subsumption_resolution,[],[f137,f63])).
% 2.14/0.65  fof(f63,plain,(
% 2.14/0.65    v2_funct_1(sK2)),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f137,plain,(
% 2.14/0.65    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.14/0.65    inference(subsumption_resolution,[],[f131,f65])).
% 2.14/0.65  fof(f65,plain,(
% 2.14/0.65    k1_xboole_0 != sK1),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f131,plain,(
% 2.14/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.14/0.65    inference(trivial_inequality_removal,[],[f128])).
% 2.14/0.65  fof(f128,plain,(
% 2.14/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.14/0.65    inference(superposition,[],[f67,f61])).
% 2.14/0.65  fof(f61,plain,(
% 2.14/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f67,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f25])).
% 2.14/0.65  fof(f25,plain,(
% 2.14/0.65    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.14/0.65    inference(flattening,[],[f24])).
% 2.14/0.65  fof(f24,plain,(
% 2.14/0.65    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.14/0.65    inference(ennf_transformation,[],[f18])).
% 2.14/0.65  fof(f18,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.14/0.65  fof(f234,plain,(
% 2.14/0.65    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~spl4_1),
% 2.14/0.65    inference(subsumption_resolution,[],[f114,f197])).
% 2.14/0.65  fof(f197,plain,(
% 2.14/0.65    v1_relat_1(sK2) | ~spl4_1),
% 2.14/0.65    inference(avatar_component_clause,[],[f196])).
% 2.14/0.65  fof(f196,plain,(
% 2.14/0.65    spl4_1 <=> v1_relat_1(sK2)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.14/0.65  fof(f114,plain,(
% 2.14/0.65    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 2.14/0.65    inference(subsumption_resolution,[],[f110,f55])).
% 2.14/0.65  fof(f110,plain,(
% 2.14/0.65    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.14/0.65    inference(resolution,[],[f63,f70])).
% 2.14/0.65  fof(f70,plain,(
% 2.14/0.65    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f29])).
% 2.14/0.65  fof(f29,plain,(
% 2.14/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.65    inference(flattening,[],[f28])).
% 2.14/0.65  fof(f28,plain,(
% 2.14/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f8])).
% 2.14/0.65  fof(f8,axiom,(
% 2.14/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 2.14/0.65  fof(f2113,plain,(
% 2.14/0.65    sK0 != k1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(forward_demodulation,[],[f2112,f183])).
% 2.14/0.65  fof(f183,plain,(
% 2.14/0.65    sK0 = k2_relat_1(sK3)),
% 2.14/0.65    inference(forward_demodulation,[],[f121,f160])).
% 2.14/0.65  fof(f160,plain,(
% 2.14/0.65    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f159,f58])).
% 2.14/0.65  fof(f58,plain,(
% 2.14/0.65    v1_funct_1(sK3)),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f159,plain,(
% 2.14/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f158,f59])).
% 2.14/0.65  fof(f59,plain,(
% 2.14/0.65    v1_funct_2(sK3,sK1,sK0)),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f158,plain,(
% 2.14/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f157,f60])).
% 2.14/0.65  fof(f60,plain,(
% 2.14/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f157,plain,(
% 2.14/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f156,f55])).
% 2.14/0.65  fof(f156,plain,(
% 2.14/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f155,f56])).
% 2.14/0.65  fof(f155,plain,(
% 2.14/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f153,f57])).
% 2.14/0.65  fof(f153,plain,(
% 2.14/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(resolution,[],[f62,f83])).
% 2.14/0.65  fof(f83,plain,(
% 2.14/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f41])).
% 2.14/0.65  fof(f41,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.14/0.65    inference(flattening,[],[f40])).
% 2.14/0.65  fof(f40,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.14/0.65    inference(ennf_transformation,[],[f16])).
% 2.14/0.65  fof(f16,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.14/0.65  fof(f62,plain,(
% 2.14/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f121,plain,(
% 2.14/0.65    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 2.14/0.65    inference(resolution,[],[f60,f88])).
% 2.14/0.65  fof(f88,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f46])).
% 2.14/0.65  fof(f46,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.65    inference(ennf_transformation,[],[f10])).
% 2.14/0.65  fof(f10,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.14/0.65  fof(f2112,plain,(
% 2.14/0.65    k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(trivial_inequality_removal,[],[f2111])).
% 2.14/0.65  fof(f2111,plain,(
% 2.14/0.65    k6_partfun1(sK1) != k6_partfun1(sK1) | k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(forward_demodulation,[],[f2110,f147])).
% 2.14/0.65  fof(f147,plain,(
% 2.14/0.65    sK1 = k2_relat_1(sK2)),
% 2.14/0.65    inference(forward_demodulation,[],[f116,f61])).
% 2.14/0.65  fof(f116,plain,(
% 2.14/0.65    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.14/0.65    inference(resolution,[],[f57,f88])).
% 2.14/0.65  fof(f2110,plain,(
% 2.14/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2109,f197])).
% 2.14/0.65  fof(f2109,plain,(
% 2.14/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2108,f55])).
% 2.14/0.65  fof(f2108,plain,(
% 2.14/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2107,f216])).
% 2.14/0.65  fof(f216,plain,(
% 2.14/0.65    v1_relat_1(sK3) | ~spl4_3),
% 2.14/0.65    inference(avatar_component_clause,[],[f215])).
% 2.14/0.65  fof(f215,plain,(
% 2.14/0.65    spl4_3 <=> v1_relat_1(sK3)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.14/0.65  fof(f2107,plain,(
% 2.14/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2106,f58])).
% 2.14/0.65  fof(f2106,plain,(
% 2.14/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2105,f63])).
% 2.14/0.65  fof(f2105,plain,(
% 2.14/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2103,f66])).
% 2.14/0.65  fof(f66,plain,(
% 2.14/0.65    k2_funct_1(sK2) != sK3),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f2103,plain,(
% 2.14/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(superposition,[],[f98,f2089])).
% 2.14/0.65  fof(f2089,plain,(
% 2.14/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(backward_demodulation,[],[f311,f2088])).
% 2.14/0.65  fof(f2088,plain,(
% 2.14/0.65    sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2087,f291])).
% 2.14/0.65  fof(f291,plain,(
% 2.14/0.65    v2_funct_1(sK3) | ~spl4_5),
% 2.14/0.65    inference(avatar_component_clause,[],[f289])).
% 2.14/0.65  fof(f289,plain,(
% 2.14/0.65    spl4_5 <=> v2_funct_1(sK3)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.14/0.65  fof(f2087,plain,(
% 2.14/0.65    sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1898,f1974])).
% 2.14/0.65  fof(f1974,plain,(
% 2.14/0.65    sK1 = k1_relat_1(sK3) | (~spl4_3 | ~spl4_5 | ~spl4_7)),
% 2.14/0.65    inference(forward_demodulation,[],[f1973,f102])).
% 2.14/0.65  fof(f1973,plain,(
% 2.14/0.65    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) | (~spl4_3 | ~spl4_5 | ~spl4_7)),
% 2.14/0.65    inference(forward_demodulation,[],[f1929,f311])).
% 2.14/0.65  fof(f1929,plain,(
% 2.14/0.65    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | (~spl4_3 | ~spl4_5)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1928,f216])).
% 2.14/0.65  fof(f1928,plain,(
% 2.14/0.65    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(sK3) | ~spl4_5),
% 2.14/0.65    inference(subsumption_resolution,[],[f1921,f58])).
% 2.14/0.65  fof(f1921,plain,(
% 2.14/0.65    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_5),
% 2.14/0.65    inference(resolution,[],[f291,f70])).
% 2.14/0.65  fof(f1898,plain,(
% 2.14/0.65    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_12)),
% 2.14/0.65    inference(forward_demodulation,[],[f1897,f147])).
% 2.14/0.65  fof(f1897,plain,(
% 2.14/0.65    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_12)),
% 2.14/0.65    inference(trivial_inequality_removal,[],[f1896])).
% 2.14/0.65  fof(f1896,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_12)),
% 2.14/0.65    inference(forward_demodulation,[],[f1895,f183])).
% 2.14/0.65  fof(f1895,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1894,f216])).
% 2.14/0.65  fof(f1894,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1893,f58])).
% 2.14/0.65  fof(f1893,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_12)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1892,f197])).
% 2.14/0.65  fof(f1892,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_12),
% 2.14/0.65    inference(subsumption_resolution,[],[f465,f55])).
% 2.14/0.65  fof(f465,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_12),
% 2.14/0.65    inference(superposition,[],[f98,f454])).
% 2.14/0.65  fof(f454,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_12),
% 2.14/0.65    inference(forward_demodulation,[],[f287,f388])).
% 2.14/0.65  fof(f388,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_12),
% 2.14/0.65    inference(avatar_component_clause,[],[f386])).
% 2.14/0.65  fof(f386,plain,(
% 2.14/0.65    spl4_12 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.14/0.65  fof(f287,plain,(
% 2.14/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f283,f58])).
% 2.14/0.65  fof(f283,plain,(
% 2.14/0.65    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.14/0.65    inference(resolution,[],[f119,f60])).
% 2.14/0.65  fof(f119,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 2.14/0.65    inference(subsumption_resolution,[],[f117,f55])).
% 2.14/0.65  fof(f117,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 2.14/0.65    inference(resolution,[],[f57,f87])).
% 2.14/0.65  fof(f87,plain,(
% 2.14/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f45])).
% 2.14/0.65  fof(f45,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.14/0.65    inference(flattening,[],[f44])).
% 2.14/0.65  fof(f44,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.14/0.65    inference(ennf_transformation,[],[f14])).
% 2.14/0.65  fof(f14,axiom,(
% 2.14/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.14/0.65  fof(f311,plain,(
% 2.14/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_7),
% 2.14/0.65    inference(avatar_component_clause,[],[f309])).
% 2.14/0.65  fof(f309,plain,(
% 2.14/0.65    spl4_7 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.14/0.65  fof(f98,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.65    inference(definition_unfolding,[],[f69,f84])).
% 2.14/0.65  fof(f69,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f27])).
% 2.14/0.65  fof(f27,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.65    inference(flattening,[],[f26])).
% 2.14/0.65  fof(f26,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f9])).
% 2.14/0.65  fof(f9,axiom,(
% 2.14/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 2.14/0.65  fof(f1881,plain,(
% 2.14/0.65    spl4_5 | ~spl4_12 | ~spl4_19),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f1880])).
% 2.14/0.65  fof(f1880,plain,(
% 2.14/0.65    $false | (spl4_5 | ~spl4_12 | ~spl4_19)),
% 2.14/0.65    inference(trivial_inequality_removal,[],[f1879])).
% 2.14/0.65  fof(f1879,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_5 | ~spl4_12 | ~spl4_19)),
% 2.14/0.65    inference(forward_demodulation,[],[f1878,f102])).
% 2.14/0.65  fof(f1878,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0))) | (spl4_5 | ~spl4_12 | ~spl4_19)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1877,f1812])).
% 2.14/0.65  fof(f1812,plain,(
% 2.14/0.65    v1_relat_1(k6_partfun1(sK0)) | ~spl4_19),
% 2.14/0.65    inference(avatar_component_clause,[],[f1811])).
% 2.14/0.65  fof(f1811,plain,(
% 2.14/0.65    spl4_19 <=> v1_relat_1(k6_partfun1(sK0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.14/0.65  fof(f1877,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(k6_partfun1(sK0)) | (spl4_5 | ~spl4_12 | ~spl4_19)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1876,f429])).
% 2.14/0.65  fof(f429,plain,(
% 2.14/0.65    v1_funct_1(k6_partfun1(sK0)) | ~spl4_12),
% 2.14/0.65    inference(subsumption_resolution,[],[f428,f55])).
% 2.14/0.65  fof(f428,plain,(
% 2.14/0.65    v1_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~spl4_12),
% 2.14/0.65    inference(subsumption_resolution,[],[f427,f57])).
% 2.14/0.65  fof(f427,plain,(
% 2.14/0.65    v1_funct_1(k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_12),
% 2.14/0.65    inference(subsumption_resolution,[],[f426,f58])).
% 2.14/0.65  fof(f426,plain,(
% 2.14/0.65    v1_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_12),
% 2.14/0.65    inference(subsumption_resolution,[],[f424,f60])).
% 2.14/0.65  fof(f424,plain,(
% 2.14/0.65    v1_funct_1(k6_partfun1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_12),
% 2.14/0.65    inference(superposition,[],[f85,f388])).
% 2.14/0.65  fof(f85,plain,(
% 2.14/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f43])).
% 2.14/0.65  fof(f43,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.14/0.65    inference(flattening,[],[f42])).
% 2.14/0.65  fof(f42,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.14/0.65    inference(ennf_transformation,[],[f13])).
% 2.14/0.65  fof(f13,axiom,(
% 2.14/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.14/0.65  fof(f1876,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0))) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0)) | (spl4_5 | ~spl4_12 | ~spl4_19)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1875,f463])).
% 2.14/0.65  fof(f463,plain,(
% 2.14/0.65    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_5 | ~spl4_12)),
% 2.14/0.65    inference(forward_demodulation,[],[f462,f388])).
% 2.14/0.65  fof(f462,plain,(
% 2.14/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl4_5),
% 2.14/0.65    inference(subsumption_resolution,[],[f461,f58])).
% 2.14/0.65  fof(f461,plain,(
% 2.14/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~v1_funct_1(sK3) | spl4_5),
% 2.14/0.65    inference(subsumption_resolution,[],[f460,f64])).
% 2.14/0.65  fof(f64,plain,(
% 2.14/0.65    k1_xboole_0 != sK0),
% 2.14/0.65    inference(cnf_transformation,[],[f53])).
% 2.14/0.65  fof(f460,plain,(
% 2.14/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_5),
% 2.14/0.65    inference(subsumption_resolution,[],[f459,f60])).
% 2.14/0.65  fof(f459,plain,(
% 2.14/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_5),
% 2.14/0.65    inference(subsumption_resolution,[],[f456,f290])).
% 2.14/0.65  fof(f290,plain,(
% 2.14/0.65    ~v2_funct_1(sK3) | spl4_5),
% 2.14/0.65    inference(avatar_component_clause,[],[f289])).
% 2.14/0.65  fof(f456,plain,(
% 2.14/0.65    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(resolution,[],[f136,f59])).
% 2.14/0.65  fof(f136,plain,(
% 2.14/0.65    ( ! [X2,X3] : (~v1_funct_2(X3,sK1,X2) | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 2.14/0.65    inference(subsumption_resolution,[],[f135,f55])).
% 2.14/0.65  fof(f135,plain,(
% 2.14/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_1(sK2)) )),
% 2.14/0.65    inference(subsumption_resolution,[],[f134,f56])).
% 2.14/0.65  fof(f134,plain,(
% 2.14/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.14/0.65    inference(subsumption_resolution,[],[f132,f57])).
% 2.14/0.65  fof(f132,plain,(
% 2.14/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.14/0.65    inference(trivial_inequality_removal,[],[f127])).
% 2.14/0.65  fof(f127,plain,(
% 2.14/0.65    ( ! [X2,X3] : (sK1 != sK1 | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.14/0.65    inference(superposition,[],[f78,f61])).
% 2.14/0.65  fof(f78,plain,(
% 2.14/0.65    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f35])).
% 2.14/0.65  fof(f35,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.14/0.65    inference(flattening,[],[f34])).
% 2.14/0.65  fof(f34,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.14/0.65    inference(ennf_transformation,[],[f17])).
% 2.14/0.65  fof(f17,axiom,(
% 2.14/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 2.14/0.65  fof(f1875,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0))) | v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0)) | ~spl4_19),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f1872])).
% 2.14/0.65  fof(f1872,plain,(
% 2.14/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(k6_partfun1(sK0))) | v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0)) | ~spl4_19),
% 2.14/0.65    inference(superposition,[],[f99,f1871])).
% 2.14/0.65  fof(f1871,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl4_19),
% 2.14/0.65    inference(forward_demodulation,[],[f1870,f102])).
% 2.14/0.65  fof(f1870,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(sK0))),k6_partfun1(sK0)) | ~spl4_19),
% 2.14/0.65    inference(resolution,[],[f1812,f100])).
% 2.14/0.65  fof(f100,plain,(
% 2.14/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 2.14/0.65    inference(definition_unfolding,[],[f89,f84])).
% 2.14/0.65  fof(f89,plain,(
% 2.14/0.65    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f47])).
% 2.14/0.65  fof(f47,plain,(
% 2.14/0.65    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f4])).
% 2.14/0.65  fof(f4,axiom,(
% 2.14/0.65    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 2.14/0.65  fof(f99,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.65    inference(definition_unfolding,[],[f80,f84])).
% 2.14/0.65  fof(f80,plain,(
% 2.14/0.65    ( ! [X0,X1] : (v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f37])).
% 2.14/0.65  fof(f37,plain,(
% 2.14/0.65    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.65    inference(flattening,[],[f36])).
% 2.14/0.65  fof(f36,plain,(
% 2.14/0.65    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f6])).
% 2.14/0.65  fof(f6,axiom,(
% 2.14/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 2.14/0.65  fof(f1827,plain,(
% 2.14/0.65    spl4_19),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f1826])).
% 2.14/0.65  fof(f1826,plain,(
% 2.14/0.65    $false | spl4_19),
% 2.14/0.65    inference(subsumption_resolution,[],[f1824,f97])).
% 2.14/0.65  fof(f97,plain,(
% 2.14/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f2])).
% 2.14/0.65  fof(f2,axiom,(
% 2.14/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.14/0.65  fof(f1824,plain,(
% 2.14/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl4_19),
% 2.14/0.65    inference(resolution,[],[f1823,f103])).
% 2.14/0.65  fof(f103,plain,(
% 2.14/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.14/0.65    inference(definition_unfolding,[],[f96,f84])).
% 2.14/0.65  fof(f96,plain,(
% 2.14/0.65    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f12])).
% 2.14/0.65  fof(f12,axiom,(
% 2.14/0.65    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.14/0.65  fof(f1823,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_19),
% 2.14/0.65    inference(resolution,[],[f1813,f95])).
% 2.14/0.65  fof(f95,plain,(
% 2.14/0.65    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f50])).
% 2.14/0.65  fof(f50,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f1])).
% 2.14/0.65  fof(f1,axiom,(
% 2.14/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.14/0.65  fof(f1813,plain,(
% 2.14/0.65    ~v1_relat_1(k6_partfun1(sK0)) | spl4_19),
% 2.14/0.65    inference(avatar_component_clause,[],[f1811])).
% 2.14/0.65  fof(f399,plain,(
% 2.14/0.65    spl4_11),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f398])).
% 2.14/0.65  fof(f398,plain,(
% 2.14/0.65    $false | spl4_11),
% 2.14/0.65    inference(subsumption_resolution,[],[f397,f55])).
% 2.14/0.65  fof(f397,plain,(
% 2.14/0.65    ~v1_funct_1(sK2) | spl4_11),
% 2.14/0.65    inference(subsumption_resolution,[],[f396,f57])).
% 2.14/0.65  fof(f396,plain,(
% 2.14/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_11),
% 2.14/0.65    inference(subsumption_resolution,[],[f395,f58])).
% 2.14/0.65  fof(f395,plain,(
% 2.14/0.65    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_11),
% 2.14/0.65    inference(subsumption_resolution,[],[f394,f60])).
% 2.14/0.65  fof(f394,plain,(
% 2.14/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_11),
% 2.14/0.65    inference(resolution,[],[f384,f86])).
% 2.14/0.65  fof(f86,plain,(
% 2.14/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f43])).
% 2.14/0.65  fof(f384,plain,(
% 2.14/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_11),
% 2.14/0.65    inference(avatar_component_clause,[],[f382])).
% 2.14/0.65  fof(f382,plain,(
% 2.14/0.65    spl4_11 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.14/0.65  fof(f389,plain,(
% 2.14/0.65    ~spl4_11 | spl4_12),
% 2.14/0.65    inference(avatar_split_clause,[],[f154,f386,f382])).
% 2.14/0.65  fof(f154,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.14/0.65    inference(subsumption_resolution,[],[f152,f103])).
% 2.14/0.65  fof(f152,plain,(
% 2.14/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.14/0.65    inference(resolution,[],[f62,f81])).
% 2.14/0.65  fof(f81,plain,(
% 2.14/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f54])).
% 2.14/0.65  fof(f54,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.65    inference(nnf_transformation,[],[f39])).
% 2.14/0.65  fof(f39,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.65    inference(flattening,[],[f38])).
% 2.14/0.65  fof(f38,plain,(
% 2.14/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.14/0.65    inference(ennf_transformation,[],[f11])).
% 2.14/0.65  fof(f11,axiom,(
% 2.14/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.14/0.65  fof(f312,plain,(
% 2.14/0.65    spl4_7 | ~spl4_5),
% 2.14/0.65    inference(avatar_split_clause,[],[f178,f289,f309])).
% 2.14/0.65  fof(f178,plain,(
% 2.14/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.14/0.65    inference(subsumption_resolution,[],[f177,f58])).
% 2.14/0.65  fof(f177,plain,(
% 2.14/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f176,f59])).
% 2.14/0.65  fof(f176,plain,(
% 2.14/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f175,f60])).
% 2.14/0.65  fof(f175,plain,(
% 2.14/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(subsumption_resolution,[],[f166,f64])).
% 2.14/0.65  fof(f166,plain,(
% 2.14/0.65    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(trivial_inequality_removal,[],[f163])).
% 2.14/0.65  fof(f163,plain,(
% 2.14/0.65    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.14/0.65    inference(superposition,[],[f67,f160])).
% 2.14/0.65  fof(f232,plain,(
% 2.14/0.65    spl4_3),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f231])).
% 2.14/0.65  fof(f231,plain,(
% 2.14/0.65    $false | spl4_3),
% 2.14/0.65    inference(subsumption_resolution,[],[f229,f97])).
% 2.14/0.65  fof(f229,plain,(
% 2.14/0.65    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_3),
% 2.14/0.65    inference(resolution,[],[f223,f60])).
% 2.14/0.65  fof(f223,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_3),
% 2.14/0.65    inference(resolution,[],[f217,f95])).
% 2.14/0.65  fof(f217,plain,(
% 2.14/0.65    ~v1_relat_1(sK3) | spl4_3),
% 2.14/0.65    inference(avatar_component_clause,[],[f215])).
% 2.14/0.65  fof(f208,plain,(
% 2.14/0.65    spl4_1),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f207])).
% 2.14/0.65  fof(f207,plain,(
% 2.14/0.65    $false | spl4_1),
% 2.14/0.65    inference(subsumption_resolution,[],[f205,f97])).
% 2.14/0.65  fof(f205,plain,(
% 2.14/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 2.14/0.65    inference(resolution,[],[f204,f57])).
% 2.14/0.65  fof(f204,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 2.14/0.65    inference(resolution,[],[f198,f95])).
% 2.14/0.65  fof(f198,plain,(
% 2.14/0.65    ~v1_relat_1(sK2) | spl4_1),
% 2.14/0.65    inference(avatar_component_clause,[],[f196])).
% 2.14/0.65  % SZS output end Proof for theBenchmark
% 2.14/0.65  % (27946)------------------------------
% 2.14/0.65  % (27946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.65  % (27946)Termination reason: Refutation
% 2.14/0.65  
% 2.14/0.65  % (27946)Memory used [KB]: 11641
% 2.14/0.65  % (27946)Time elapsed: 0.215 s
% 2.14/0.65  % (27946)------------------------------
% 2.14/0.65  % (27946)------------------------------
% 2.14/0.65  % (27921)Success in time 0.293 s
%------------------------------------------------------------------------------
