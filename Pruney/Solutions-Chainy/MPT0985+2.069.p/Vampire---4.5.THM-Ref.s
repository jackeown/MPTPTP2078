%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 454 expanded)
%              Number of leaves         :   42 ( 180 expanded)
%              Depth                    :   13
%              Number of atoms          :  706 (1429 expanded)
%              Number of equality atoms :  129 ( 318 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f99,f105,f110,f123,f132,f139,f144,f154,f162,f177,f182,f212,f226,f271,f279,f284,f294,f340,f347,f384,f401,f419,f439,f517,f560,f660,f665,f679,f681,f694,f710])).

fof(f710,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f694,plain,
    ( spl7_8
    | ~ spl7_20
    | ~ spl7_33
    | ~ spl7_59 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | spl7_8
    | ~ spl7_20
    | ~ spl7_33
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f678,f654])).

fof(f654,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f652])).

fof(f652,plain,
    ( spl7_59
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f678,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl7_8
    | ~ spl7_20
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f677,f396])).

fof(f396,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl7_33
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f677,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl7_8
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f676,f72])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f676,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_8
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f127,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl7_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f127,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f681,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20
    | ~ spl7_33
    | spl7_59 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20
    | ~ spl7_33
    | spl7_59 ),
    inference(subsumption_resolution,[],[f671,f653])).

fof(f653,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl7_59 ),
    inference(avatar_component_clause,[],[f652])).

fof(f671,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f392,f396])).

fof(f392,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f391,f72])).

fof(f391,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f349,f211])).

fof(f349,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f343,f161])).

fof(f161,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl7_12
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f343,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f342,f176])).

fof(f176,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_15
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f342,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f147,f170])).

fof(f170,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_14
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f147,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl7_6 ),
    inference(resolution,[],[f118,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f118,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_6
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f679,plain,
    ( ~ spl7_59
    | spl7_31
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f675,f394,f366,f652])).

fof(f366,plain,
    ( spl7_31
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f675,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl7_31
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f367,f396])).

fof(f367,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f366])).

fof(f665,plain,
    ( ~ spl7_39
    | spl7_47
    | ~ spl7_59 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | ~ spl7_39
    | spl7_47
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f563,f654])).

fof(f563,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_39
    | spl7_47 ),
    inference(forward_demodulation,[],[f562,f72])).

fof(f562,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl7_39
    | spl7_47 ),
    inference(subsumption_resolution,[],[f561,f447])).

fof(f447,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl7_39
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f561,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_47 ),
    inference(superposition,[],[f559,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f559,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl7_47 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl7_47
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f660,plain,
    ( spl7_60
    | ~ spl7_32
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f510,f394,f381,f657])).

fof(f657,plain,
    ( spl7_60
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f381,plain,
    ( spl7_32
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f510,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl7_32
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f492,f39])).

fof(f39,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f492,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl7_32
    | ~ spl7_33 ),
    inference(superposition,[],[f383,f396])).

fof(f383,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f381])).

fof(f560,plain,
    ( ~ spl7_47
    | spl7_28
    | ~ spl7_31
    | ~ spl7_33
    | spl7_36 ),
    inference(avatar_split_clause,[],[f555,f416,f394,f366,f281,f557])).

fof(f281,plain,
    ( spl7_28
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f416,plain,
    ( spl7_36
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f555,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl7_28
    | ~ spl7_31
    | ~ spl7_33
    | spl7_36 ),
    inference(forward_demodulation,[],[f554,f396])).

fof(f554,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl7_28
    | ~ spl7_31
    | spl7_36 ),
    inference(subsumption_resolution,[],[f553,f418])).

fof(f418,plain,
    ( k1_xboole_0 != sK0
    | spl7_36 ),
    inference(avatar_component_clause,[],[f416])).

fof(f553,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl7_28
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f286,f368])).

fof(f368,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f366])).

fof(f286,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl7_28 ),
    inference(forward_demodulation,[],[f285,f72])).

fof(f285,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_28 ),
    inference(resolution,[],[f283,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f283,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl7_28 ),
    inference(avatar_component_clause,[],[f281])).

fof(f517,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f439,plain,
    ( ~ spl7_26
    | ~ spl7_27
    | spl7_33
    | spl7_36 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl7_26
    | ~ spl7_27
    | spl7_33
    | spl7_36 ),
    inference(subsumption_resolution,[],[f437,f395])).

fof(f395,plain,
    ( k1_xboole_0 != sK2
    | spl7_33 ),
    inference(avatar_component_clause,[],[f394])).

fof(f437,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_26
    | ~ spl7_27
    | spl7_36 ),
    inference(subsumption_resolution,[],[f436,f418])).

fof(f436,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f274,f278])).

fof(f278,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl7_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f274,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f272,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f272,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_26 ),
    inference(resolution,[],[f270,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f270,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl7_26
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f419,plain,
    ( ~ spl7_36
    | spl7_21
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f409,f398,f223,f416])).

fof(f223,plain,
    ( spl7_21
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f398,plain,
    ( spl7_34
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f409,plain,
    ( k1_xboole_0 != sK0
    | spl7_21
    | ~ spl7_34 ),
    inference(superposition,[],[f224,f400])).

fof(f400,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f398])).

fof(f224,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f401,plain,
    ( spl7_33
    | spl7_34
    | ~ spl7_27
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f375,f291,f276,f398,f394])).

fof(f291,plain,
    ( spl7_29
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f375,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_27
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f374,f278])).

fof(f374,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_29 ),
    inference(forward_demodulation,[],[f372,f71])).

fof(f372,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl7_29 ),
    inference(resolution,[],[f293,f75])).

fof(f293,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f291])).

fof(f384,plain,
    ( spl7_32
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f379,f209,f174,f169,f159,f116,f381])).

fof(f379,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f350,f211])).

fof(f350,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f336,f161])).

fof(f336,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f335,f176])).

fof(f335,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f146,f170])).

fof(f146,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl7_6 ),
    inference(resolution,[],[f118,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f347,plain,
    ( ~ spl7_6
    | spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl7_6
    | spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f345,f127])).

fof(f345,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f344,f161])).

fof(f344,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f343,f225])).

fof(f225,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f340,plain,
    ( ~ spl7_6
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl7_6
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f338,f131])).

fof(f131,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f338,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f337,f161])).

fof(f337,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f336,f225])).

fof(f294,plain,
    ( spl7_29
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f245,f209,f151,f291])).

fof(f151,plain,
    ( spl7_11
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f245,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(superposition,[],[f153,f211])).

fof(f153,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f284,plain,
    ( ~ spl7_28
    | spl7_9
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f243,f209,f129,f281])).

fof(f243,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl7_9
    | ~ spl7_20 ),
    inference(superposition,[],[f131,f211])).

fof(f279,plain,
    ( spl7_27
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f247,f209,f102,f276])).

fof(f102,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f247,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f240,f71])).

fof(f240,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(superposition,[],[f104,f211])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f271,plain,
    ( spl7_26
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f239,f209,f96,f268])).

fof(f96,plain,
    ( spl7_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f239,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(superposition,[],[f98,f211])).

fof(f98,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f226,plain,
    ( spl7_21
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f215,f205,f102,f223])).

fof(f205,plain,
    ( spl7_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f215,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f213,f104])).

fof(f213,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_19 ),
    inference(superposition,[],[f207,f61])).

fof(f207,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f205])).

fof(f212,plain,
    ( spl7_19
    | spl7_20
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f194,f102,f96,f209,f205])).

fof(f194,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f100,f104])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(resolution,[],[f98,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f182,plain,
    ( ~ spl7_1
    | ~ spl7_7
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_7
    | spl7_14 ),
    inference(subsumption_resolution,[],[f180,f121])).

fof(f121,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f180,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_1
    | spl7_14 ),
    inference(subsumption_resolution,[],[f178,f81])).

fof(f81,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f178,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_14 ),
    inference(resolution,[],[f171,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f171,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f177,plain,
    ( spl7_15
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f163,f120,f84,f79,f174])).

fof(f84,plain,
    ( spl7_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f163,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f94,f121])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f92,f81])).

fof(f92,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f86,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f162,plain,
    ( spl7_12
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f157,f136,f120,f84,f79,f159])).

fof(f136,plain,
    ( spl7_10
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f157,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f156,f138])).

fof(f138,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f156,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f93,f121])).

fof(f93,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f91,f81])).

fof(f91,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f154,plain,
    ( spl7_11
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f149,f136,f120,f79,f151])).

fof(f149,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f148,f138])).

fof(f148,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f89,f121])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl7_1 ),
    inference(resolution,[],[f81,f42])).

fof(f144,plain,
    ( ~ spl7_4
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl7_4
    | spl7_7 ),
    inference(resolution,[],[f133,f104])).

fof(f133,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_7 ),
    inference(resolution,[],[f122,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f122,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f139,plain,
    ( spl7_10
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f113,f107,f102,f136])).

fof(f107,plain,
    ( spl7_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f113,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f111,f104])).

fof(f111,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_5 ),
    inference(superposition,[],[f109,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f109,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f132,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f32,f116,f129,f125])).

fof(f32,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f123,plain,
    ( spl7_6
    | ~ spl7_7
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f88,f79,f120,f116])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_1 ),
    inference(resolution,[],[f81,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f110,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f37,f107])).

fof(f37,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f105,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f35,f102])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f34,f96])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:26:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (29558)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (29550)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (29558)Refutation not found, incomplete strategy% (29558)------------------------------
% 0.21/0.46  % (29558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (29558)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (29558)Memory used [KB]: 10618
% 0.21/0.46  % (29558)Time elapsed: 0.052 s
% 0.21/0.46  % (29558)------------------------------
% 0.21/0.46  % (29558)------------------------------
% 0.21/0.46  % (29538)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (29545)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (29547)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (29541)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (29539)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (29546)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (29548)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (29552)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (29542)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (29539)Refutation not found, incomplete strategy% (29539)------------------------------
% 0.21/0.50  % (29539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29539)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29539)Memory used [KB]: 10618
% 0.21/0.50  % (29539)Time elapsed: 0.059 s
% 0.21/0.50  % (29539)------------------------------
% 0.21/0.50  % (29539)------------------------------
% 0.21/0.50  % (29557)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (29551)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (29555)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (29540)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (29543)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (29549)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (29544)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (29541)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f711,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f82,f87,f99,f105,f110,f123,f132,f139,f144,f154,f162,f177,f182,f212,f226,f271,f279,f284,f294,f340,f347,f384,f401,f419,f439,f517,f560,f660,f665,f679,f681,f694,f710])).
% 0.21/0.51  fof(f710,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | k1_xboole_0 != sK1 | k1_xboole_0 != sK0 | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f694,plain,(
% 0.21/0.51    spl7_8 | ~spl7_20 | ~spl7_33 | ~spl7_59),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f693])).
% 0.21/0.51  fof(f693,plain,(
% 0.21/0.51    $false | (spl7_8 | ~spl7_20 | ~spl7_33 | ~spl7_59)),
% 0.21/0.51    inference(subsumption_resolution,[],[f678,f654])).
% 0.21/0.51  fof(f654,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl7_59),
% 0.21/0.51    inference(avatar_component_clause,[],[f652])).
% 0.21/0.51  fof(f652,plain,(
% 0.21/0.51    spl7_59 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 0.21/0.51  fof(f678,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl7_8 | ~spl7_20 | ~spl7_33)),
% 0.21/0.51    inference(forward_demodulation,[],[f677,f396])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl7_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f394])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    spl7_33 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.51  fof(f677,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl7_8 | ~spl7_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f676,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f676,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl7_8 | ~spl7_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f127,f211])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl7_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    spl7_20 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl7_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.51  fof(f681,plain,(
% 0.21/0.51    ~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_20 | ~spl7_33 | spl7_59),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f680])).
% 0.21/0.51  fof(f680,plain,(
% 0.21/0.51    $false | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_20 | ~spl7_33 | spl7_59)),
% 0.21/0.51    inference(subsumption_resolution,[],[f671,f653])).
% 0.21/0.51  fof(f653,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl7_59),
% 0.21/0.51    inference(avatar_component_clause,[],[f652])).
% 0.21/0.51  fof(f671,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_20 | ~spl7_33)),
% 0.21/0.51    inference(forward_demodulation,[],[f392,f396])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f391,f72])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f349,f211])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f343,f161])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl7_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl7_12 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl7_6 | ~spl7_14 | ~spl7_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f342,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl7_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f174])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl7_15 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl7_6 | ~spl7_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f147,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl7_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl7_14 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f118,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK2)) | ~spl7_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl7_6 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.51  fof(f679,plain,(
% 0.21/0.51    ~spl7_59 | spl7_31 | ~spl7_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f675,f394,f366,f652])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    spl7_31 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.51  fof(f675,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl7_31 | ~spl7_33)),
% 0.21/0.51    inference(forward_demodulation,[],[f367,f396])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | spl7_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f366])).
% 0.21/0.51  fof(f665,plain,(
% 0.21/0.51    ~spl7_39 | spl7_47 | ~spl7_59),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f664])).
% 0.21/0.51  fof(f664,plain,(
% 0.21/0.51    $false | (~spl7_39 | spl7_47 | ~spl7_59)),
% 0.21/0.51    inference(subsumption_resolution,[],[f563,f654])).
% 0.21/0.51  fof(f563,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_39 | spl7_47)),
% 0.21/0.51    inference(forward_demodulation,[],[f562,f72])).
% 0.21/0.51  fof(f562,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl7_39 | spl7_47)),
% 0.21/0.51    inference(subsumption_resolution,[],[f561,f447])).
% 0.21/0.51  fof(f447,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl7_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f445])).
% 0.21/0.51  fof(f445,plain,(
% 0.21/0.51    spl7_39 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.51  fof(f561,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl7_47),
% 0.21/0.51    inference(superposition,[],[f559,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f559,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | spl7_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f557])).
% 0.21/0.51  fof(f557,plain,(
% 0.21/0.51    spl7_47 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.21/0.51  fof(f660,plain,(
% 0.21/0.51    spl7_60 | ~spl7_32 | ~spl7_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f510,f394,f381,f657])).
% 0.21/0.51  fof(f657,plain,(
% 0.21/0.51    spl7_60 <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    spl7_32 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.51  fof(f510,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl7_32 | ~spl7_33)),
% 0.21/0.51    inference(forward_demodulation,[],[f492,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.51  fof(f492,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_relat_1(k1_xboole_0)) | (~spl7_32 | ~spl7_33)),
% 0.21/0.51    inference(superposition,[],[f383,f396])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) | ~spl7_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f381])).
% 0.21/0.51  fof(f560,plain,(
% 0.21/0.51    ~spl7_47 | spl7_28 | ~spl7_31 | ~spl7_33 | spl7_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f555,f416,f394,f366,f281,f557])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    spl7_28 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.51  fof(f416,plain,(
% 0.21/0.51    spl7_36 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.51  fof(f555,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (spl7_28 | ~spl7_31 | ~spl7_33 | spl7_36)),
% 0.21/0.51    inference(forward_demodulation,[],[f554,f396])).
% 0.21/0.51  fof(f554,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl7_28 | ~spl7_31 | spl7_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f553,f418])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | spl7_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f416])).
% 0.21/0.51  fof(f553,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl7_28 | ~spl7_31)),
% 0.21/0.51    inference(subsumption_resolution,[],[f286,f368])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl7_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f366])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | spl7_28),
% 0.21/0.51    inference(forward_demodulation,[],[f285,f72])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl7_28),
% 0.21/0.51    inference(resolution,[],[f283,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | spl7_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f281])).
% 0.21/0.51  fof(f517,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | sK1 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f439,plain,(
% 0.21/0.51    ~spl7_26 | ~spl7_27 | spl7_33 | spl7_36),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f438])).
% 0.21/0.51  fof(f438,plain,(
% 0.21/0.51    $false | (~spl7_26 | ~spl7_27 | spl7_33 | spl7_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f437,f395])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | spl7_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f394])).
% 0.21/0.51  fof(f437,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | (~spl7_26 | ~spl7_27 | spl7_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f436,f418])).
% 0.21/0.51  fof(f436,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl7_26 | ~spl7_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f274,f278])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl7_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f276])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    spl7_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_26),
% 0.21/0.51    inference(forward_demodulation,[],[f272,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_26),
% 0.21/0.51    inference(resolution,[],[f270,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    spl7_26 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.51  fof(f419,plain,(
% 0.21/0.51    ~spl7_36 | spl7_21 | ~spl7_34),
% 0.21/0.51    inference(avatar_split_clause,[],[f409,f398,f223,f416])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl7_21 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.51  fof(f398,plain,(
% 0.21/0.51    spl7_34 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | (spl7_21 | ~spl7_34)),
% 0.21/0.51    inference(superposition,[],[f224,f400])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~spl7_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f398])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    sK0 != k1_relat_1(sK2) | spl7_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f223])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    spl7_33 | spl7_34 | ~spl7_27 | ~spl7_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f375,f291,f276,f398,f394])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    spl7_29 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.51  fof(f375,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | (~spl7_27 | ~spl7_29)),
% 0.21/0.51    inference(subsumption_resolution,[],[f374,f278])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl7_29),
% 0.21/0.51    inference(forward_demodulation,[],[f372,f71])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~spl7_29),
% 0.21/0.51    inference(resolution,[],[f293,f75])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl7_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f291])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    spl7_32 | ~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f379,f209,f174,f169,f159,f116,f381])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f350,f211])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f336,f161])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl7_6 | ~spl7_14 | ~spl7_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f335,f176])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl7_6 | ~spl7_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f146,f170])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f118,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ~spl7_6 | spl7_8 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_21),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f346])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    $false | (~spl7_6 | spl7_8 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f345,f127])).
% 0.21/0.51  fof(f345,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f344,f161])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl7_6 | ~spl7_14 | ~spl7_15 | ~spl7_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f343,f225])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | ~spl7_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f223])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    ~spl7_6 | spl7_9 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_21),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f339])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    $false | (~spl7_6 | spl7_9 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f338,f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl7_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl7_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl7_6 | ~spl7_12 | ~spl7_14 | ~spl7_15 | ~spl7_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f337,f161])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl7_6 | ~spl7_14 | ~spl7_15 | ~spl7_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f336,f225])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    spl7_29 | ~spl7_11 | ~spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f245,f209,f151,f291])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl7_11 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl7_11 | ~spl7_20)),
% 0.21/0.51    inference(superposition,[],[f153,f211])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~spl7_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    ~spl7_28 | spl7_9 | ~spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f243,f209,f129,f281])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl7_9 | ~spl7_20)),
% 0.21/0.51    inference(superposition,[],[f131,f211])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    spl7_27 | ~spl7_4 | ~spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f247,f209,f102,f276])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_4 | ~spl7_20)),
% 0.21/0.51    inference(forward_demodulation,[],[f240,f71])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_4 | ~spl7_20)),
% 0.21/0.51    inference(superposition,[],[f104,f211])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f102])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    spl7_26 | ~spl7_3 | ~spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f239,f209,f96,f268])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl7_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl7_3 | ~spl7_20)),
% 0.21/0.51    inference(superposition,[],[f98,f211])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl7_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    spl7_21 | ~spl7_4 | ~spl7_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f215,f205,f102,f223])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    spl7_19 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | (~spl7_4 | ~spl7_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f213,f104])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_19),
% 0.21/0.51    inference(superposition,[],[f207,f61])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f205])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    spl7_19 | spl7_20 | ~spl7_3 | ~spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f194,f102,f96,f209,f205])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl7_3 | ~spl7_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f104])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.21/0.51    inference(resolution,[],[f98,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ~spl7_1 | ~spl7_7 | spl7_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    $false | (~spl7_1 | ~spl7_7 | spl7_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f180,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl7_7 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | (~spl7_1 | spl7_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f178,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    v1_funct_1(sK2) | ~spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl7_1 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_14),
% 0.21/0.51    inference(resolution,[],[f171,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | spl7_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl7_15 | ~spl7_1 | ~spl7_2 | ~spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f163,f120,f84,f79,f174])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl7_2 <=> v2_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f94,f121])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f81])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl7_2),
% 0.21/0.51    inference(resolution,[],[f86,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    v2_funct_1(sK2) | ~spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    spl7_12 | ~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f157,f136,f120,f84,f79,f159])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl7_10 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_10)),
% 0.21/0.51    inference(forward_demodulation,[],[f156,f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | ~spl7_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f136])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f121])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f91,f81])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl7_2),
% 0.21/0.51    inference(resolution,[],[f86,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl7_11 | ~spl7_1 | ~spl7_7 | ~spl7_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f149,f136,f120,f79,f151])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | (~spl7_1 | ~spl7_7 | ~spl7_10)),
% 0.21/0.51    inference(forward_demodulation,[],[f148,f138])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl7_1 | ~spl7_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f89,f121])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl7_1),
% 0.21/0.51    inference(resolution,[],[f81,f42])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~spl7_4 | spl7_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    $false | (~spl7_4 | spl7_7)),
% 0.21/0.51    inference(resolution,[],[f133,f104])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_7),
% 0.21/0.51    inference(resolution,[],[f122,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl7_10 | ~spl7_4 | ~spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f113,f107,f102,f136])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl7_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | (~spl7_4 | ~spl7_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f104])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_5),
% 0.21/0.51    inference(superposition,[],[f109,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl7_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ~spl7_8 | ~spl7_9 | ~spl7_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f116,f129,f125])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl7_6 | ~spl7_7 | ~spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f79,f120,f116])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl7_1),
% 0.21/0.51    inference(resolution,[],[f81,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f107])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f102])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f96])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f84])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f79])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (29541)------------------------------
% 0.21/0.51  % (29541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29541)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (29541)Memory used [KB]: 11001
% 0.21/0.51  % (29541)Time elapsed: 0.087 s
% 0.21/0.51  % (29541)------------------------------
% 0.21/0.51  % (29541)------------------------------
% 0.21/0.52  % (29537)Success in time 0.155 s
%------------------------------------------------------------------------------
