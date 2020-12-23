%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 225 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :    9
%              Number of atoms          :  335 ( 755 expanded)
%              Number of equality atoms :   80 ( 201 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f68,f76,f81,f92,f107,f117,f133,f141,f156,f164,f168,f182,f187,f195])).

fof(f195,plain,
    ( ~ spl3_13
    | ~ spl3_16
    | spl3_28
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl3_13
    | ~ spl3_16
    | spl3_28
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f193,f181])).

fof(f181,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_28
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f193,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_16
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f191,f155])).

fof(f155,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_13
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f191,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_29 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_29 ),
    inference(superposition,[],[f106,f186])).

fof(f186,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl3_29
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f106,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_16
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f187,plain,
    ( spl3_29
    | ~ spl3_12
    | spl3_25
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f173,f166,f162,f87,f185])).

fof(f87,plain,
    ( spl3_12
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f162,plain,
    ( spl3_25
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f166,plain,
    ( spl3_26
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f173,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_12
    | spl3_25
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f167,f171])).

fof(f171,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_12
    | spl3_25 ),
    inference(resolution,[],[f88,f163])).

fof(f163,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f162])).

fof(f88,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f167,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f166])).

fof(f182,plain,
    ( ~ spl3_28
    | ~ spl3_12
    | spl3_25 ),
    inference(avatar_split_clause,[],[f174,f162,f87,f180])).

fof(f174,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_12
    | spl3_25 ),
    inference(backward_demodulation,[],[f163,f171])).

fof(f168,plain,
    ( spl3_26
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f145,f139,f115,f79,f54,f50,f46,f166])).

fof(f46,plain,
    ( spl3_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( spl3_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f115,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) != X0
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f139,plain,
    ( spl3_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f145,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f126,f142])).

fof(f142,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_10
    | ~ spl3_22 ),
    inference(resolution,[],[f140,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f126,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f55,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f124,f47])).

fof(f47,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f123,f51])).

fof(f51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(superposition,[],[f116,f55])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f55,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f164,plain,
    ( ~ spl3_25
    | ~ spl3_10
    | spl3_20
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f144,f139,f131,f79,f162])).

fof(f131,plain,
    ( spl3_20
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f144,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_10
    | spl3_20
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f132,f142])).

fof(f132,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f131])).

fof(f156,plain,
    ( spl3_13
    | ~ spl3_10
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f143,f139,f79,f90])).

fof(f143,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_10
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f140,f142])).

fof(f141,plain,
    ( spl3_22
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f129,f115,f58,f54,f50,f46,f139])).

fof(f58,plain,
    ( spl3_5
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f127,f59])).

fof(f59,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f51,f125])).

fof(f133,plain,
    ( ~ spl3_20
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f128,f115,f54,f50,f46,f131])).

fof(f128,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f47,f125])).

fof(f117,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f26,f115])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f107,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f38,f105])).

fof(f38,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f31,f29])).

fof(f29,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f92,plain,
    ( spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f40,f90,f87])).

fof(f40,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f34,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,
    ( spl3_10
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f77,f74,f66,f79])).

fof(f66,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(resolution,[],[f75,f67])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f18,f74])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f68,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f16,f66])).

fof(f16,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f60,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f56,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f54])).

fof(f15,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f50])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f36,f46])).

fof(f36,plain,(
    ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f35,f14])).

fof(f35,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f12,f13])).

fof(f13,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (31539)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (31531)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (31539)Refutation not found, incomplete strategy% (31539)------------------------------
% 0.20/0.48  % (31539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31539)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31539)Memory used [KB]: 6140
% 0.20/0.48  % (31539)Time elapsed: 0.051 s
% 0.20/0.48  % (31539)------------------------------
% 0.20/0.48  % (31539)------------------------------
% 0.20/0.48  % (31527)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (31527)Refutation not found, incomplete strategy% (31527)------------------------------
% 0.20/0.48  % (31527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31527)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31527)Memory used [KB]: 10618
% 0.20/0.48  % (31527)Time elapsed: 0.058 s
% 0.20/0.48  % (31527)------------------------------
% 0.20/0.48  % (31527)------------------------------
% 0.20/0.48  % (31530)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (31533)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (31537)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (31533)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f68,f76,f81,f92,f107,f117,f133,f141,f156,f164,f168,f182,f187,f195])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~spl3_13 | ~spl3_16 | spl3_28 | ~spl3_29),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    $false | (~spl3_13 | ~spl3_16 | spl3_28 | ~spl3_29)),
% 0.20/0.49    inference(subsumption_resolution,[],[f193,f181])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl3_28),
% 0.20/0.49    inference(avatar_component_clause,[],[f180])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl3_28 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_13 | ~spl3_16 | ~spl3_29)),
% 0.20/0.49    inference(subsumption_resolution,[],[f191,f155])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl3_13 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_16 | ~spl3_29)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f189])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_16 | ~spl3_29)),
% 0.20/0.49    inference(superposition,[],[f106,f186])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl3_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f185])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    spl3_29 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl3_16 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    spl3_29 | ~spl3_12 | spl3_25 | ~spl3_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f173,f166,f162,f87,f185])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl3_12 <=> ! [X0] : (k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    spl3_25 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    spl3_26 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_12 | spl3_25 | ~spl3_26)),
% 0.20/0.49    inference(backward_demodulation,[],[f167,f171])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | (~spl3_12 | spl3_25)),
% 0.20/0.49    inference(resolution,[],[f88,f163])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | spl3_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f162])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f87])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | ~spl3_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f166])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ~spl3_28 | ~spl3_12 | spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f174,f162,f87,f180])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_12 | spl3_25)),
% 0.20/0.49    inference(backward_demodulation,[],[f163,f171])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    spl3_26 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_18 | ~spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f145,f139,f115,f79,f54,f50,f46,f166])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    spl3_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_4 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl3_10 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl3_18 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl3_22 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_18 | ~spl3_22)),
% 0.20/0.49    inference(backward_demodulation,[],[f126,f142])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | (~spl3_10 | ~spl3_22)),
% 0.20/0.49    inference(resolution,[],[f140,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f79])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f139])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_18)),
% 0.20/0.49    inference(backward_demodulation,[],[f55,f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_18)),
% 0.20/0.49    inference(subsumption_resolution,[],[f124,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,sK0,sK1) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f46])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | v1_funct_2(sK2,sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_18)),
% 0.20/0.49    inference(subsumption_resolution,[],[f123,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f50])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_funct_2(sK2,sK0,sK1) | (~spl3_4 | ~spl3_18)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    sK0 != sK0 | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_funct_2(sK2,sK0,sK1) | (~spl3_4 | ~spl3_18)),
% 0.20/0.49    inference(superposition,[],[f116,f55])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) ) | ~spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f115])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    ~spl3_25 | ~spl3_10 | spl3_20 | ~spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f144,f139,f131,f79,f162])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl3_20 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_10 | spl3_20 | ~spl3_22)),
% 0.20/0.49    inference(backward_demodulation,[],[f132,f142])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,sK0,k1_xboole_0) | spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f131])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    spl3_13 | ~spl3_10 | ~spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f143,f139,f79,f90])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_10 | ~spl3_22)),
% 0.20/0.49    inference(backward_demodulation,[],[f140,f142])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    spl3_22 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f129,f115,f58,f54,f50,f46,f139])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl3_5 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_18)),
% 0.20/0.49    inference(forward_demodulation,[],[f127,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f58])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_18)),
% 0.20/0.49    inference(backward_demodulation,[],[f51,f125])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ~spl3_20 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f128,f115,f54,f50,f46,f131])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,sK0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_18)),
% 0.20/0.49    inference(backward_demodulation,[],[f47,f125])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f115])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl3_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f105])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f31,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl3_12 | ~spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f90,f87])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f34,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl3_10 | ~spl3_7 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f77,f74,f66,f79])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl3_7 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl3_7 | ~spl3_9)),
% 0.20/0.49    inference(resolution,[],[f75,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f18,f74])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f16,f66])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f58])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f15,f54])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f14,f50])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f46])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f35,f14])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f12,f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (31533)------------------------------
% 0.20/0.49  % (31533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31533)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (31533)Memory used [KB]: 10618
% 0.20/0.49  % (31533)Time elapsed: 0.074 s
% 0.20/0.49  % (31533)------------------------------
% 0.20/0.49  % (31533)------------------------------
% 0.20/0.49  % (31523)Success in time 0.132 s
%------------------------------------------------------------------------------
