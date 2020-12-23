%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:00 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  265 (2159 expanded)
%              Number of leaves         :   32 ( 687 expanded)
%              Depth                    :   38
%              Number of atoms          : 1116 (21095 expanded)
%              Number of equality atoms :  252 (7158 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f928,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f196,f201,f223,f229,f319,f375,f402,f472,f482,f644,f676,f812,f887,f927])).

fof(f927,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f926])).

fof(f926,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f925,f273])).

fof(f273,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f268,f102])).

fof(f102,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f96,f84])).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f96,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f268,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f102,f267])).

fof(f267,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f266,f138])).

fof(f138,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f137,f55])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f52,f51])).

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

fof(f137,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f56])).

fof(f56,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f136,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f135,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f135,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f134,f63])).

fof(f63,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f134,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f128,f65])).

fof(f65,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f128,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f266,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f265,f55])).

fof(f265,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f264,f195])).

fof(f195,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_2
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f264,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f263,f234])).

fof(f234,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f148,f190])).

fof(f190,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f146,f55])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f91,f144])).

fof(f144,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f113,f61])).

fof(f113,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f263,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f262,f63])).

fof(f262,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f256,f65])).

fof(f256,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f253])).

fof(f253,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(superposition,[],[f67,f248])).

fof(f248,plain,
    ( sK1 = k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f244,f144])).

fof(f244,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f234,f88])).

fof(f925,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f924,f179])).

fof(f179,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f118,f156])).

fof(f156,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f155,f58])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f155,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f154,f59])).

fof(f59,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f154,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f153,f60])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f153,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f152,f55])).

fof(f152,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f151,f56])).

fof(f151,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f150,f57])).

fof(f150,plain,
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
    inference(cnf_transformation,[],[f40])).

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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f118,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f60,f88])).

fof(f924,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(trivial_inequality_removal,[],[f923])).

fof(f923,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f922,f144])).

fof(f922,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f921,f190])).

fof(f921,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f920,f55])).

fof(f920,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f919,f217])).

fof(f217,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f919,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f918,f58])).

fof(f918,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f917,f63])).

fof(f917,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f915,f66])).

fof(f66,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f915,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(superposition,[],[f98,f890])).

fof(f890,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f314,f807])).

fof(f807,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f805])).

fof(f805,plain,
    ( spl4_13
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f314,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl4_5
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

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
    inference(definition_unfolding,[],[f70,f84])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f887,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f886])).

fof(f886,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_14 ),
    inference(subsumption_resolution,[],[f885,f811])).

fof(f811,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl4_14
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f885,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f878,f101])).

fof(f101,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f97,f84])).

fof(f97,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f878,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f101,f873])).

fof(f873,plain,
    ( k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f872,f314])).

fof(f872,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f717,f317])).

fof(f317,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl4_6
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f717,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f716,f58])).

fof(f716,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f715,f222])).

fof(f222,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_4
  <=> v1_funct_2(sK3,k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f715,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f714,f328])).

fof(f328,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f183,f217])).

fof(f183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f181,f58])).

fof(f181,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f91,f179])).

fof(f714,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f353,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f53])).

fof(f353,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f350])).

fof(f350,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f67,f343])).

fof(f343,plain,
    ( sK0 = k2_relset_1(k1_relat_1(sK3),sK0,sK3)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f336,f179])).

fof(f336,plain,
    ( k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),sK0,sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f328,f88])).

fof(f812,plain,
    ( spl4_13
    | ~ spl4_14
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f793,f372,f316,f216,f189,f809,f805])).

fof(f372,plain,
    ( spl4_9
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f793,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f684,f317])).

fof(f684,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f683,f144])).

fof(f683,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(trivial_inequality_removal,[],[f682])).

fof(f682,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f681,f179])).

fof(f681,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f680,f217])).

fof(f680,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f679,f58])).

fof(f679,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f678,f190])).

fof(f678,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f674,f55])).

fof(f674,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(superposition,[],[f98,f664])).

fof(f664,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f242,f374])).

fof(f374,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f372])).

fof(f242,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f238,f58])).

fof(f238,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f116,f60])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f114,f55])).

fof(f114,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f676,plain,
    ( spl4_6
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f669,f99])).

fof(f99,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f80,f84])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f669,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_6
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f403,f664])).

fof(f403,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_6 ),
    inference(backward_demodulation,[],[f333,f242])).

fof(f333,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f332,f58])).

fof(f332,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f331,f64])).

fof(f331,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f330,f60])).

fof(f330,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f329,f318])).

fof(f318,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f316])).

fof(f329,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f133,f59])).

fof(f133,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,sK1,X2)
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f132,f55])).

fof(f132,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f131,f56])).

fof(f131,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f129,f57])).

fof(f129,plain,(
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
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,(
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
    inference(superposition,[],[f77,f61])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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

fof(f644,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f642,f55])).

fof(f642,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f641,f57])).

fof(f641,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f640,f461])).

fof(f461,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl4_11
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f640,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f639,f577])).

fof(f577,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f576,f457])).

fof(f457,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl4_10
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f576,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f302,f461])).

fof(f302,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f300,f207])).

fof(f207,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f202,f190])).

fof(f202,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f110,f144])).

fof(f110,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f107,f55])).

fof(f107,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f300,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f91,f288])).

fof(f288,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f210,f273])).

fof(f210,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f111,f190])).

fof(f111,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f108,f55])).

fof(f108,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f639,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f634,f370])).

fof(f370,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl4_8
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f634,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(superposition,[],[f86,f589])).

fof(f589,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f588,f138])).

fof(f588,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f581,f461])).

fof(f581,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(resolution,[],[f577,f116])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f482,plain,
    ( ~ spl4_1
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl4_1
    | spl4_11 ),
    inference(subsumption_resolution,[],[f480,f190])).

fof(f480,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f479,f55])).

fof(f479,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_11 ),
    inference(resolution,[],[f462,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f462,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f460])).

fof(f472,plain,
    ( ~ spl4_1
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | ~ spl4_1
    | spl4_10 ),
    inference(subsumption_resolution,[],[f470,f190])).

fof(f470,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f468,f55])).

fof(f468,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_10 ),
    inference(resolution,[],[f458,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f458,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f456])).

fof(f402,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f400,f55])).

fof(f400,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f399,f57])).

fof(f399,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f398,f58])).

fof(f398,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f397,f60])).

fof(f397,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f366,f86])).

fof(f366,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl4_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f375,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f149,f372,f368,f364])).

fof(f149,plain,
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f319,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f174,f316,f312])).

fof(f174,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f173,f58])).

fof(f173,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f172,f59])).

fof(f172,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f171,f60])).

fof(f171,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f162,f64])).

fof(f162,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f67,f156])).

fof(f229,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f226,f93])).

fof(f93,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f226,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_3 ),
    inference(resolution,[],[f224,f60])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_3 ),
    inference(resolution,[],[f218,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f218,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f216])).

fof(f223,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f182,f220,f216])).

fof(f182,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f180,f58])).

fof(f180,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f90,f179])).

fof(f90,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f201,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f198,f93])).

fof(f198,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f197,f57])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f191,f92])).

fof(f191,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f196,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f147,f193,f189])).

fof(f147,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f145,f55])).

fof(f145,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f90,f144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (16008)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (16037)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.56  % (16021)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.59/0.57  % (16020)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.59/0.57  % (16013)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.59/0.57  % (16027)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.59/0.57  % (16017)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.59/0.57  % (16009)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.59/0.57  % (16028)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.59/0.57  % (16035)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.58  % (16024)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.59/0.58  % (16015)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.59/0.58  % (16032)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.59/0.58  % (16024)Refutation not found, incomplete strategy% (16024)------------------------------
% 1.59/0.58  % (16024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (16024)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (16024)Memory used [KB]: 10746
% 1.59/0.58  % (16024)Time elapsed: 0.167 s
% 1.59/0.58  % (16024)------------------------------
% 1.59/0.58  % (16024)------------------------------
% 1.59/0.58  % (16011)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.59/0.58  % (16034)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.59/0.59  % (16030)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.59/0.59  % (16016)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.59/0.59  % (16026)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.59/0.59  % (16036)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.59/0.59  % (16012)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.59/0.59  % (16010)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.59/0.59  % (16018)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.59  % (16022)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.59/0.60  % (16033)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.60  % (16019)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.59/0.60  % (16014)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.61  % (16025)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.59/0.61  % (16029)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.59/0.61  % (16031)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.59/0.62  % (16023)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.17/0.65  % (16032)Refutation found. Thanks to Tanya!
% 2.17/0.65  % SZS status Theorem for theBenchmark
% 2.17/0.65  % SZS output start Proof for theBenchmark
% 2.17/0.65  fof(f928,plain,(
% 2.17/0.65    $false),
% 2.17/0.65    inference(avatar_sat_refutation,[],[f196,f201,f223,f229,f319,f375,f402,f472,f482,f644,f676,f812,f887,f927])).
% 2.17/0.65  fof(f927,plain,(
% 2.17/0.65    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_13),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f926])).
% 2.17/0.65  fof(f926,plain,(
% 2.17/0.65    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(subsumption_resolution,[],[f925,f273])).
% 2.17/0.65  fof(f273,plain,(
% 2.17/0.65    sK0 = k1_relat_1(sK2) | (~spl4_1 | ~spl4_2)),
% 2.17/0.65    inference(forward_demodulation,[],[f268,f102])).
% 2.17/0.65  fof(f102,plain,(
% 2.17/0.65    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.17/0.65    inference(definition_unfolding,[],[f96,f84])).
% 2.17/0.65  fof(f84,plain,(
% 2.17/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f16])).
% 2.17/0.65  fof(f16,axiom,(
% 2.17/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.17/0.65  fof(f96,plain,(
% 2.17/0.65    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.17/0.65    inference(cnf_transformation,[],[f5])).
% 2.17/0.65  fof(f5,axiom,(
% 2.17/0.65    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.17/0.65  fof(f268,plain,(
% 2.17/0.65    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | (~spl4_1 | ~spl4_2)),
% 2.17/0.65    inference(superposition,[],[f102,f267])).
% 2.17/0.65  fof(f267,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.17/0.65    inference(forward_demodulation,[],[f266,f138])).
% 2.17/0.65  fof(f138,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.17/0.65    inference(subsumption_resolution,[],[f137,f55])).
% 2.17/0.65  fof(f55,plain,(
% 2.17/0.65    v1_funct_1(sK2)),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f53,plain,(
% 2.17/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.17/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f52,f51])).
% 2.17/0.65  fof(f51,plain,(
% 2.17/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.17/0.65    introduced(choice_axiom,[])).
% 2.17/0.65  fof(f52,plain,(
% 2.17/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.17/0.65    introduced(choice_axiom,[])).
% 2.17/0.65  fof(f24,plain,(
% 2.17/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.17/0.65    inference(flattening,[],[f23])).
% 2.17/0.65  fof(f23,plain,(
% 2.17/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.17/0.65    inference(ennf_transformation,[],[f22])).
% 2.17/0.65  fof(f22,negated_conjecture,(
% 2.17/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.17/0.65    inference(negated_conjecture,[],[f21])).
% 2.17/0.65  fof(f21,conjecture,(
% 2.17/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.17/0.65  fof(f137,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f136,f56])).
% 2.17/0.65  fof(f56,plain,(
% 2.17/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f136,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f135,f57])).
% 2.17/0.65  fof(f57,plain,(
% 2.17/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f135,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f134,f63])).
% 2.17/0.65  fof(f63,plain,(
% 2.17/0.65    v2_funct_1(sK2)),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f134,plain,(
% 2.17/0.65    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f128,f65])).
% 2.17/0.65  fof(f65,plain,(
% 2.17/0.65    k1_xboole_0 != sK1),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f128,plain,(
% 2.17/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f125])).
% 2.17/0.65  fof(f125,plain,(
% 2.17/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.17/0.65    inference(superposition,[],[f67,f61])).
% 2.17/0.65  fof(f61,plain,(
% 2.17/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f67,plain,(
% 2.17/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f26])).
% 2.17/0.65  fof(f26,plain,(
% 2.17/0.65    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.17/0.65    inference(flattening,[],[f25])).
% 2.17/0.65  fof(f25,plain,(
% 2.17/0.65    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.17/0.65    inference(ennf_transformation,[],[f19])).
% 2.17/0.65  fof(f19,axiom,(
% 2.17/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.17/0.65  fof(f266,plain,(
% 2.17/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f265,f55])).
% 2.17/0.65  fof(f265,plain,(
% 2.17/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f264,f195])).
% 2.17/0.65  fof(f195,plain,(
% 2.17/0.65    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~spl4_2),
% 2.17/0.65    inference(avatar_component_clause,[],[f193])).
% 2.17/0.65  fof(f193,plain,(
% 2.17/0.65    spl4_2 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.17/0.65  fof(f264,plain,(
% 2.17/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~spl4_1),
% 2.17/0.65    inference(subsumption_resolution,[],[f263,f234])).
% 2.17/0.65  fof(f234,plain,(
% 2.17/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl4_1),
% 2.17/0.65    inference(subsumption_resolution,[],[f148,f190])).
% 2.17/0.65  fof(f190,plain,(
% 2.17/0.65    v1_relat_1(sK2) | ~spl4_1),
% 2.17/0.65    inference(avatar_component_clause,[],[f189])).
% 2.17/0.65  fof(f189,plain,(
% 2.17/0.65    spl4_1 <=> v1_relat_1(sK2)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.17/0.65  fof(f148,plain,(
% 2.17/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f146,f55])).
% 2.17/0.65  fof(f146,plain,(
% 2.17/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(superposition,[],[f91,f144])).
% 2.17/0.65  fof(f144,plain,(
% 2.17/0.65    sK1 = k2_relat_1(sK2)),
% 2.17/0.65    inference(forward_demodulation,[],[f113,f61])).
% 2.17/0.65  fof(f113,plain,(
% 2.17/0.65    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.17/0.65    inference(resolution,[],[f57,f88])).
% 2.17/0.65  fof(f88,plain,(
% 2.17/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f45])).
% 2.17/0.65  fof(f45,plain,(
% 2.17/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.65    inference(ennf_transformation,[],[f11])).
% 2.17/0.65  fof(f11,axiom,(
% 2.17/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.17/0.65  fof(f91,plain,(
% 2.17/0.65    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f47])).
% 2.17/0.65  fof(f47,plain,(
% 2.17/0.65    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.65    inference(flattening,[],[f46])).
% 2.17/0.65  fof(f46,plain,(
% 2.17/0.65    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.17/0.65    inference(ennf_transformation,[],[f20])).
% 2.17/0.65  fof(f20,axiom,(
% 2.17/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 2.17/0.65  fof(f263,plain,(
% 2.17/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~spl4_1),
% 2.17/0.65    inference(subsumption_resolution,[],[f262,f63])).
% 2.17/0.65  fof(f262,plain,(
% 2.17/0.65    ~v2_funct_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~spl4_1),
% 2.17/0.65    inference(subsumption_resolution,[],[f256,f65])).
% 2.17/0.65  fof(f256,plain,(
% 2.17/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~spl4_1),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f253])).
% 2.17/0.65  fof(f253,plain,(
% 2.17/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~spl4_1),
% 2.17/0.65    inference(superposition,[],[f67,f248])).
% 2.17/0.65  fof(f248,plain,(
% 2.17/0.65    sK1 = k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~spl4_1),
% 2.17/0.65    inference(forward_demodulation,[],[f244,f144])).
% 2.17/0.65  fof(f244,plain,(
% 2.17/0.65    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~spl4_1),
% 2.17/0.65    inference(resolution,[],[f234,f88])).
% 2.17/0.65  fof(f925,plain,(
% 2.17/0.65    sK0 != k1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(forward_demodulation,[],[f924,f179])).
% 2.17/0.65  fof(f179,plain,(
% 2.17/0.65    sK0 = k2_relat_1(sK3)),
% 2.17/0.65    inference(forward_demodulation,[],[f118,f156])).
% 2.17/0.65  fof(f156,plain,(
% 2.17/0.65    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f155,f58])).
% 2.17/0.65  fof(f58,plain,(
% 2.17/0.65    v1_funct_1(sK3)),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f155,plain,(
% 2.17/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f154,f59])).
% 2.17/0.65  fof(f59,plain,(
% 2.17/0.65    v1_funct_2(sK3,sK1,sK0)),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f154,plain,(
% 2.17/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f153,f60])).
% 2.17/0.65  fof(f60,plain,(
% 2.17/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f153,plain,(
% 2.17/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f152,f55])).
% 2.17/0.65  fof(f152,plain,(
% 2.17/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f151,f56])).
% 2.17/0.65  fof(f151,plain,(
% 2.17/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f150,f57])).
% 2.17/0.65  fof(f150,plain,(
% 2.17/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(resolution,[],[f62,f83])).
% 2.17/0.65  fof(f83,plain,(
% 2.17/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f40])).
% 2.17/0.65  fof(f40,plain,(
% 2.17/0.65    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.17/0.65    inference(flattening,[],[f39])).
% 2.17/0.65  fof(f39,plain,(
% 2.17/0.65    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.17/0.65    inference(ennf_transformation,[],[f17])).
% 2.17/0.65  fof(f17,axiom,(
% 2.17/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.17/0.65  fof(f62,plain,(
% 2.17/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f118,plain,(
% 2.17/0.65    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 2.17/0.65    inference(resolution,[],[f60,f88])).
% 2.17/0.65  fof(f924,plain,(
% 2.17/0.65    k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f923])).
% 2.17/0.65  fof(f923,plain,(
% 2.17/0.65    k6_partfun1(sK1) != k6_partfun1(sK1) | k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(forward_demodulation,[],[f922,f144])).
% 2.17/0.65  fof(f922,plain,(
% 2.17/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(subsumption_resolution,[],[f921,f190])).
% 2.17/0.65  fof(f921,plain,(
% 2.17/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(subsumption_resolution,[],[f920,f55])).
% 2.17/0.65  fof(f920,plain,(
% 2.17/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(subsumption_resolution,[],[f919,f217])).
% 2.17/0.65  fof(f217,plain,(
% 2.17/0.65    v1_relat_1(sK3) | ~spl4_3),
% 2.17/0.65    inference(avatar_component_clause,[],[f216])).
% 2.17/0.65  fof(f216,plain,(
% 2.17/0.65    spl4_3 <=> v1_relat_1(sK3)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.17/0.65  fof(f919,plain,(
% 2.17/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(subsumption_resolution,[],[f918,f58])).
% 2.17/0.65  fof(f918,plain,(
% 2.17/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(subsumption_resolution,[],[f917,f63])).
% 2.17/0.65  fof(f917,plain,(
% 2.17/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(subsumption_resolution,[],[f915,f66])).
% 2.17/0.65  fof(f66,plain,(
% 2.17/0.65    k2_funct_1(sK2) != sK3),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f915,plain,(
% 2.17/0.65    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(superposition,[],[f98,f890])).
% 2.17/0.65  fof(f890,plain,(
% 2.17/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | (~spl4_5 | ~spl4_13)),
% 2.17/0.65    inference(backward_demodulation,[],[f314,f807])).
% 2.17/0.65  fof(f807,plain,(
% 2.17/0.65    sK2 = k2_funct_1(sK3) | ~spl4_13),
% 2.17/0.65    inference(avatar_component_clause,[],[f805])).
% 2.17/0.65  fof(f805,plain,(
% 2.17/0.65    spl4_13 <=> sK2 = k2_funct_1(sK3)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.17/0.65  fof(f314,plain,(
% 2.17/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_5),
% 2.17/0.65    inference(avatar_component_clause,[],[f312])).
% 2.17/0.65  fof(f312,plain,(
% 2.17/0.65    spl4_5 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.17/0.65  fof(f98,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(definition_unfolding,[],[f70,f84])).
% 2.17/0.65  fof(f70,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f30])).
% 2.17/0.65  fof(f30,plain,(
% 2.17/0.65    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.65    inference(flattening,[],[f29])).
% 2.17/0.65  fof(f29,plain,(
% 2.17/0.65    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.17/0.65    inference(ennf_transformation,[],[f10])).
% 2.17/0.65  fof(f10,axiom,(
% 2.17/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 2.17/0.65  fof(f887,plain,(
% 2.17/0.65    ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_14),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f886])).
% 2.17/0.65  fof(f886,plain,(
% 2.17/0.65    $false | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_14)),
% 2.17/0.65    inference(subsumption_resolution,[],[f885,f811])).
% 2.17/0.65  fof(f811,plain,(
% 2.17/0.65    sK1 != k1_relat_1(sK3) | spl4_14),
% 2.17/0.65    inference(avatar_component_clause,[],[f809])).
% 2.17/0.65  fof(f809,plain,(
% 2.17/0.65    spl4_14 <=> sK1 = k1_relat_1(sK3)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.17/0.65  fof(f885,plain,(
% 2.17/0.65    sK1 = k1_relat_1(sK3) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 2.17/0.65    inference(forward_demodulation,[],[f878,f101])).
% 2.17/0.65  fof(f101,plain,(
% 2.17/0.65    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.17/0.65    inference(definition_unfolding,[],[f97,f84])).
% 2.17/0.65  fof(f97,plain,(
% 2.17/0.65    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.17/0.65    inference(cnf_transformation,[],[f5])).
% 2.17/0.65  fof(f878,plain,(
% 2.17/0.65    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 2.17/0.65    inference(superposition,[],[f101,f873])).
% 2.17/0.65  fof(f873,plain,(
% 2.17/0.65    k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 2.17/0.65    inference(forward_demodulation,[],[f872,f314])).
% 2.17/0.65  fof(f872,plain,(
% 2.17/0.65    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | (~spl4_3 | ~spl4_4 | ~spl4_6)),
% 2.17/0.65    inference(subsumption_resolution,[],[f717,f317])).
% 2.17/0.65  fof(f317,plain,(
% 2.17/0.65    v2_funct_1(sK3) | ~spl4_6),
% 2.17/0.65    inference(avatar_component_clause,[],[f316])).
% 2.17/0.65  fof(f316,plain,(
% 2.17/0.65    spl4_6 <=> v2_funct_1(sK3)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.17/0.65  fof(f717,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | (~spl4_3 | ~spl4_4)),
% 2.17/0.65    inference(subsumption_resolution,[],[f716,f58])).
% 2.17/0.65  fof(f716,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl4_3 | ~spl4_4)),
% 2.17/0.65    inference(subsumption_resolution,[],[f715,f222])).
% 2.17/0.65  fof(f222,plain,(
% 2.17/0.65    v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~spl4_4),
% 2.17/0.65    inference(avatar_component_clause,[],[f220])).
% 2.17/0.65  fof(f220,plain,(
% 2.17/0.65    spl4_4 <=> v1_funct_2(sK3,k1_relat_1(sK3),sK0)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.17/0.65  fof(f715,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~spl4_3),
% 2.17/0.65    inference(subsumption_resolution,[],[f714,f328])).
% 2.17/0.65  fof(f328,plain,(
% 2.17/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~spl4_3),
% 2.17/0.65    inference(subsumption_resolution,[],[f183,f217])).
% 2.17/0.65  fof(f183,plain,(
% 2.17/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~v1_relat_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f181,f58])).
% 2.17/0.65  fof(f181,plain,(
% 2.17/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.17/0.65    inference(superposition,[],[f91,f179])).
% 2.17/0.65  fof(f714,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~spl4_3),
% 2.17/0.65    inference(subsumption_resolution,[],[f353,f64])).
% 2.17/0.65  fof(f64,plain,(
% 2.17/0.65    k1_xboole_0 != sK0),
% 2.17/0.65    inference(cnf_transformation,[],[f53])).
% 2.17/0.65  fof(f353,plain,(
% 2.17/0.65    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~spl4_3),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f350])).
% 2.17/0.65  fof(f350,plain,(
% 2.17/0.65    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~spl4_3),
% 2.17/0.65    inference(superposition,[],[f67,f343])).
% 2.17/0.65  fof(f343,plain,(
% 2.17/0.65    sK0 = k2_relset_1(k1_relat_1(sK3),sK0,sK3) | ~spl4_3),
% 2.17/0.65    inference(forward_demodulation,[],[f336,f179])).
% 2.17/0.65  fof(f336,plain,(
% 2.17/0.65    k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),sK0,sK3) | ~spl4_3),
% 2.17/0.65    inference(resolution,[],[f328,f88])).
% 2.17/0.65  fof(f812,plain,(
% 2.17/0.65    spl4_13 | ~spl4_14 | ~spl4_1 | ~spl4_3 | ~spl4_6 | ~spl4_9),
% 2.17/0.65    inference(avatar_split_clause,[],[f793,f372,f316,f216,f189,f809,f805])).
% 2.17/0.65  fof(f372,plain,(
% 2.17/0.65    spl4_9 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.17/0.65  fof(f793,plain,(
% 2.17/0.65    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_6 | ~spl4_9)),
% 2.17/0.65    inference(subsumption_resolution,[],[f684,f317])).
% 2.17/0.65  fof(f684,plain,(
% 2.17/0.65    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_9)),
% 2.17/0.65    inference(forward_demodulation,[],[f683,f144])).
% 2.17/0.65  fof(f683,plain,(
% 2.17/0.65    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_9)),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f682])).
% 2.17/0.65  fof(f682,plain,(
% 2.17/0.65    k6_partfun1(sK0) != k6_partfun1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_9)),
% 2.17/0.65    inference(forward_demodulation,[],[f681,f179])).
% 2.17/0.65  fof(f681,plain,(
% 2.17/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_9)),
% 2.17/0.65    inference(subsumption_resolution,[],[f680,f217])).
% 2.17/0.65  fof(f680,plain,(
% 2.17/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_9)),
% 2.17/0.65    inference(subsumption_resolution,[],[f679,f58])).
% 2.17/0.65  fof(f679,plain,(
% 2.17/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_9)),
% 2.17/0.65    inference(subsumption_resolution,[],[f678,f190])).
% 2.17/0.65  fof(f678,plain,(
% 2.17/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_9),
% 2.17/0.65    inference(subsumption_resolution,[],[f674,f55])).
% 2.17/0.65  fof(f674,plain,(
% 2.17/0.65    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_9),
% 2.17/0.65    inference(superposition,[],[f98,f664])).
% 2.17/0.65  fof(f664,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_9),
% 2.17/0.65    inference(backward_demodulation,[],[f242,f374])).
% 2.17/0.65  fof(f374,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_9),
% 2.17/0.65    inference(avatar_component_clause,[],[f372])).
% 2.17/0.65  fof(f242,plain,(
% 2.17/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f238,f58])).
% 2.17/0.65  fof(f238,plain,(
% 2.17/0.65    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.17/0.65    inference(resolution,[],[f116,f60])).
% 2.17/0.65  fof(f116,plain,(
% 2.17/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 2.17/0.65    inference(subsumption_resolution,[],[f114,f55])).
% 2.17/0.65  fof(f114,plain,(
% 2.17/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 2.17/0.65    inference(resolution,[],[f57,f87])).
% 2.17/0.65  fof(f87,plain,(
% 2.17/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f44])).
% 2.17/0.65  fof(f44,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.17/0.65    inference(flattening,[],[f43])).
% 2.17/0.65  fof(f43,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.17/0.65    inference(ennf_transformation,[],[f15])).
% 2.17/0.65  fof(f15,axiom,(
% 2.17/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.17/0.65  fof(f676,plain,(
% 2.17/0.65    spl4_6 | ~spl4_9),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f675])).
% 2.17/0.65  fof(f675,plain,(
% 2.17/0.65    $false | (spl4_6 | ~spl4_9)),
% 2.17/0.65    inference(subsumption_resolution,[],[f669,f99])).
% 2.17/0.65  fof(f99,plain,(
% 2.17/0.65    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.17/0.65    inference(definition_unfolding,[],[f80,f84])).
% 2.17/0.65  fof(f80,plain,(
% 2.17/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.17/0.65    inference(cnf_transformation,[],[f7])).
% 2.17/0.65  fof(f7,axiom,(
% 2.17/0.65    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.17/0.65  fof(f669,plain,(
% 2.17/0.65    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_6 | ~spl4_9)),
% 2.17/0.65    inference(backward_demodulation,[],[f403,f664])).
% 2.17/0.65  fof(f403,plain,(
% 2.17/0.65    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_6),
% 2.17/0.65    inference(backward_demodulation,[],[f333,f242])).
% 2.17/0.65  fof(f333,plain,(
% 2.17/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl4_6),
% 2.17/0.65    inference(subsumption_resolution,[],[f332,f58])).
% 2.17/0.65  fof(f332,plain,(
% 2.17/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~v1_funct_1(sK3) | spl4_6),
% 2.17/0.65    inference(subsumption_resolution,[],[f331,f64])).
% 2.17/0.65  fof(f331,plain,(
% 2.17/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_6),
% 2.17/0.65    inference(subsumption_resolution,[],[f330,f60])).
% 2.17/0.65  fof(f330,plain,(
% 2.17/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_6),
% 2.17/0.65    inference(subsumption_resolution,[],[f329,f318])).
% 2.17/0.65  fof(f318,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | spl4_6),
% 2.17/0.65    inference(avatar_component_clause,[],[f316])).
% 2.17/0.65  fof(f329,plain,(
% 2.17/0.65    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(resolution,[],[f133,f59])).
% 2.17/0.65  fof(f133,plain,(
% 2.17/0.65    ( ! [X2,X3] : (~v1_funct_2(X3,sK1,X2) | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 2.17/0.65    inference(subsumption_resolution,[],[f132,f55])).
% 2.17/0.65  fof(f132,plain,(
% 2.17/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_1(sK2)) )),
% 2.17/0.65    inference(subsumption_resolution,[],[f131,f56])).
% 2.17/0.65  fof(f131,plain,(
% 2.17/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.17/0.65    inference(subsumption_resolution,[],[f129,f57])).
% 2.17/0.65  fof(f129,plain,(
% 2.17/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f124])).
% 2.17/0.65  fof(f124,plain,(
% 2.17/0.65    ( ! [X2,X3] : (sK1 != sK1 | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.17/0.65    inference(superposition,[],[f77,f61])).
% 2.17/0.65  fof(f77,plain,(
% 2.17/0.65    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f36])).
% 2.17/0.65  fof(f36,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.17/0.65    inference(flattening,[],[f35])).
% 2.17/0.65  fof(f35,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.17/0.65    inference(ennf_transformation,[],[f18])).
% 2.17/0.65  fof(f18,axiom,(
% 2.17/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.17/0.65  fof(f644,plain,(
% 2.17/0.65    ~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_10 | ~spl4_11),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f643])).
% 2.17/0.65  fof(f643,plain,(
% 2.17/0.65    $false | (~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f642,f55])).
% 2.17/0.65  fof(f642,plain,(
% 2.17/0.65    ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f641,f57])).
% 2.17/0.65  fof(f641,plain,(
% 2.17/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f640,f461])).
% 2.17/0.65  fof(f461,plain,(
% 2.17/0.65    v1_funct_1(k2_funct_1(sK2)) | ~spl4_11),
% 2.17/0.65    inference(avatar_component_clause,[],[f460])).
% 2.17/0.65  fof(f460,plain,(
% 2.17/0.65    spl4_11 <=> v1_funct_1(k2_funct_1(sK2))),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.17/0.65  fof(f640,plain,(
% 2.17/0.65    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f639,f577])).
% 2.17/0.65  fof(f577,plain,(
% 2.17/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f576,f457])).
% 2.17/0.65  fof(f457,plain,(
% 2.17/0.65    v1_relat_1(k2_funct_1(sK2)) | ~spl4_10),
% 2.17/0.65    inference(avatar_component_clause,[],[f456])).
% 2.17/0.65  fof(f456,plain,(
% 2.17/0.65    spl4_10 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.17/0.65  fof(f576,plain,(
% 2.17/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f302,f461])).
% 2.17/0.65  fof(f302,plain,(
% 2.17/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.17/0.65    inference(forward_demodulation,[],[f300,f207])).
% 2.17/0.65  fof(f207,plain,(
% 2.17/0.65    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 2.17/0.65    inference(subsumption_resolution,[],[f202,f190])).
% 2.17/0.65  fof(f202,plain,(
% 2.17/0.65    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(forward_demodulation,[],[f110,f144])).
% 2.17/0.65  fof(f110,plain,(
% 2.17/0.65    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f107,f55])).
% 2.17/0.65  fof(f107,plain,(
% 2.17/0.65    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(resolution,[],[f63,f71])).
% 2.17/0.65  fof(f71,plain,(
% 2.17/0.65    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f32])).
% 2.17/0.65  fof(f32,plain,(
% 2.17/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.65    inference(flattening,[],[f31])).
% 2.17/0.65  fof(f31,plain,(
% 2.17/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.17/0.65    inference(ennf_transformation,[],[f9])).
% 2.17/0.65  fof(f9,axiom,(
% 2.17/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.17/0.65  fof(f300,plain,(
% 2.17/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.17/0.65    inference(superposition,[],[f91,f288])).
% 2.17/0.65  fof(f288,plain,(
% 2.17/0.65    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 2.17/0.65    inference(backward_demodulation,[],[f210,f273])).
% 2.17/0.65  fof(f210,plain,(
% 2.17/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 2.17/0.65    inference(subsumption_resolution,[],[f111,f190])).
% 2.17/0.65  fof(f111,plain,(
% 2.17/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f108,f55])).
% 2.17/0.65  fof(f108,plain,(
% 2.17/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(resolution,[],[f63,f72])).
% 2.17/0.65  fof(f72,plain,(
% 2.17/0.65    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f32])).
% 2.17/0.65  fof(f639,plain,(
% 2.17/0.65    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f634,f370])).
% 2.17/0.65  fof(f370,plain,(
% 2.17/0.65    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_8),
% 2.17/0.65    inference(avatar_component_clause,[],[f368])).
% 2.17/0.65  fof(f368,plain,(
% 2.17/0.65    spl4_8 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.17/0.65  fof(f634,plain,(
% 2.17/0.65    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(superposition,[],[f86,f589])).
% 2.17/0.65  fof(f589,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(forward_demodulation,[],[f588,f138])).
% 2.17/0.65  fof(f588,plain,(
% 2.17/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f581,f461])).
% 2.17/0.65  fof(f581,plain,(
% 2.17/0.65    ~v1_funct_1(k2_funct_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.17/0.65    inference(resolution,[],[f577,f116])).
% 2.17/0.65  fof(f86,plain,(
% 2.17/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f42])).
% 2.17/0.65  fof(f42,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.17/0.65    inference(flattening,[],[f41])).
% 2.17/0.65  fof(f41,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.17/0.65    inference(ennf_transformation,[],[f13])).
% 2.17/0.65  fof(f13,axiom,(
% 2.17/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.17/0.65  fof(f482,plain,(
% 2.17/0.65    ~spl4_1 | spl4_11),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f481])).
% 2.17/0.65  fof(f481,plain,(
% 2.17/0.65    $false | (~spl4_1 | spl4_11)),
% 2.17/0.65    inference(subsumption_resolution,[],[f480,f190])).
% 2.17/0.65  fof(f480,plain,(
% 2.17/0.65    ~v1_relat_1(sK2) | spl4_11),
% 2.17/0.65    inference(subsumption_resolution,[],[f479,f55])).
% 2.17/0.65  fof(f479,plain,(
% 2.17/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_11),
% 2.17/0.65    inference(resolution,[],[f462,f74])).
% 2.17/0.65  fof(f74,plain,(
% 2.17/0.65    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f34])).
% 2.17/0.65  fof(f34,plain,(
% 2.17/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.65    inference(flattening,[],[f33])).
% 2.17/0.65  fof(f33,plain,(
% 2.17/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.17/0.65    inference(ennf_transformation,[],[f6])).
% 2.17/0.65  fof(f6,axiom,(
% 2.17/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.17/0.65  fof(f462,plain,(
% 2.17/0.65    ~v1_funct_1(k2_funct_1(sK2)) | spl4_11),
% 2.17/0.65    inference(avatar_component_clause,[],[f460])).
% 2.17/0.65  fof(f472,plain,(
% 2.17/0.65    ~spl4_1 | spl4_10),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f471])).
% 2.17/0.65  fof(f471,plain,(
% 2.17/0.65    $false | (~spl4_1 | spl4_10)),
% 2.17/0.65    inference(subsumption_resolution,[],[f470,f190])).
% 2.17/0.65  fof(f470,plain,(
% 2.17/0.65    ~v1_relat_1(sK2) | spl4_10),
% 2.17/0.65    inference(subsumption_resolution,[],[f468,f55])).
% 2.17/0.65  fof(f468,plain,(
% 2.17/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_10),
% 2.17/0.65    inference(resolution,[],[f458,f73])).
% 2.17/0.65  fof(f73,plain,(
% 2.17/0.65    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f34])).
% 2.17/0.65  fof(f458,plain,(
% 2.17/0.65    ~v1_relat_1(k2_funct_1(sK2)) | spl4_10),
% 2.17/0.65    inference(avatar_component_clause,[],[f456])).
% 2.17/0.65  fof(f402,plain,(
% 2.17/0.65    spl4_7),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f401])).
% 2.17/0.65  fof(f401,plain,(
% 2.17/0.65    $false | spl4_7),
% 2.17/0.65    inference(subsumption_resolution,[],[f400,f55])).
% 2.17/0.65  fof(f400,plain,(
% 2.17/0.65    ~v1_funct_1(sK2) | spl4_7),
% 2.17/0.65    inference(subsumption_resolution,[],[f399,f57])).
% 2.17/0.65  fof(f399,plain,(
% 2.17/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_7),
% 2.17/0.65    inference(subsumption_resolution,[],[f398,f58])).
% 2.17/0.65  fof(f398,plain,(
% 2.17/0.65    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_7),
% 2.17/0.65    inference(subsumption_resolution,[],[f397,f60])).
% 2.17/0.65  fof(f397,plain,(
% 2.17/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_7),
% 2.17/0.65    inference(resolution,[],[f366,f86])).
% 2.17/0.65  fof(f366,plain,(
% 2.17/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_7),
% 2.17/0.65    inference(avatar_component_clause,[],[f364])).
% 2.17/0.65  fof(f364,plain,(
% 2.17/0.65    spl4_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.17/0.65  fof(f375,plain,(
% 2.17/0.65    ~spl4_7 | ~spl4_8 | spl4_9),
% 2.17/0.65    inference(avatar_split_clause,[],[f149,f372,f368,f364])).
% 2.17/0.65  fof(f149,plain,(
% 2.17/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.17/0.65    inference(resolution,[],[f62,f81])).
% 2.17/0.65  fof(f81,plain,(
% 2.17/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.65    inference(cnf_transformation,[],[f54])).
% 2.17/0.65  fof(f54,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.65    inference(nnf_transformation,[],[f38])).
% 2.17/0.65  fof(f38,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.65    inference(flattening,[],[f37])).
% 2.17/0.65  fof(f37,plain,(
% 2.17/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.17/0.65    inference(ennf_transformation,[],[f12])).
% 2.17/0.65  fof(f12,axiom,(
% 2.17/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.17/0.65  fof(f319,plain,(
% 2.17/0.65    spl4_5 | ~spl4_6),
% 2.17/0.65    inference(avatar_split_clause,[],[f174,f316,f312])).
% 2.17/0.65  fof(f174,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.17/0.65    inference(subsumption_resolution,[],[f173,f58])).
% 2.17/0.65  fof(f173,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f172,f59])).
% 2.17/0.65  fof(f172,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f171,f60])).
% 2.17/0.65  fof(f171,plain,(
% 2.17/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f162,f64])).
% 2.17/0.65  fof(f162,plain,(
% 2.17/0.65    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f159])).
% 2.17/0.65  fof(f159,plain,(
% 2.17/0.65    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.17/0.65    inference(superposition,[],[f67,f156])).
% 2.17/0.65  fof(f229,plain,(
% 2.17/0.65    spl4_3),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f228])).
% 2.17/0.65  fof(f228,plain,(
% 2.17/0.65    $false | spl4_3),
% 2.17/0.65    inference(subsumption_resolution,[],[f226,f93])).
% 2.17/0.65  fof(f93,plain,(
% 2.17/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.17/0.65    inference(cnf_transformation,[],[f2])).
% 2.17/0.65  fof(f2,axiom,(
% 2.17/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.17/0.65  fof(f226,plain,(
% 2.17/0.65    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_3),
% 2.17/0.65    inference(resolution,[],[f224,f60])).
% 2.17/0.65  fof(f224,plain,(
% 2.17/0.65    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_3),
% 2.17/0.65    inference(resolution,[],[f218,f92])).
% 2.17/0.65  fof(f92,plain,(
% 2.17/0.65    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f48])).
% 2.17/0.65  fof(f48,plain,(
% 2.17/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.17/0.65    inference(ennf_transformation,[],[f1])).
% 2.17/0.65  fof(f1,axiom,(
% 2.17/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.17/0.65  fof(f218,plain,(
% 2.17/0.65    ~v1_relat_1(sK3) | spl4_3),
% 2.17/0.65    inference(avatar_component_clause,[],[f216])).
% 2.17/0.65  fof(f223,plain,(
% 2.17/0.65    ~spl4_3 | spl4_4),
% 2.17/0.65    inference(avatar_split_clause,[],[f182,f220,f216])).
% 2.17/0.65  fof(f182,plain,(
% 2.17/0.65    v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 2.17/0.65    inference(subsumption_resolution,[],[f180,f58])).
% 2.17/0.65  fof(f180,plain,(
% 2.17/0.65    v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.17/0.65    inference(superposition,[],[f90,f179])).
% 2.17/0.65  fof(f90,plain,(
% 2.17/0.65    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f47])).
% 2.17/0.65  fof(f201,plain,(
% 2.17/0.65    spl4_1),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f200])).
% 2.17/0.65  fof(f200,plain,(
% 2.17/0.65    $false | spl4_1),
% 2.17/0.65    inference(subsumption_resolution,[],[f198,f93])).
% 2.17/0.65  fof(f198,plain,(
% 2.17/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 2.17/0.65    inference(resolution,[],[f197,f57])).
% 2.17/0.65  fof(f197,plain,(
% 2.17/0.65    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 2.17/0.65    inference(resolution,[],[f191,f92])).
% 2.17/0.65  fof(f191,plain,(
% 2.17/0.65    ~v1_relat_1(sK2) | spl4_1),
% 2.17/0.65    inference(avatar_component_clause,[],[f189])).
% 2.17/0.65  fof(f196,plain,(
% 2.17/0.65    ~spl4_1 | spl4_2),
% 2.17/0.65    inference(avatar_split_clause,[],[f147,f193,f189])).
% 2.17/0.65  fof(f147,plain,(
% 2.17/0.65    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f145,f55])).
% 2.17/0.65  fof(f145,plain,(
% 2.17/0.65    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.17/0.65    inference(superposition,[],[f90,f144])).
% 2.17/0.65  % SZS output end Proof for theBenchmark
% 2.17/0.65  % (16032)------------------------------
% 2.17/0.65  % (16032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.65  % (16032)Termination reason: Refutation
% 2.17/0.65  
% 2.17/0.65  % (16032)Memory used [KB]: 11129
% 2.17/0.65  % (16032)Time elapsed: 0.225 s
% 2.17/0.65  % (16032)------------------------------
% 2.17/0.65  % (16032)------------------------------
% 2.17/0.66  % (16007)Success in time 0.298 s
%------------------------------------------------------------------------------
