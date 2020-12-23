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
% DateTime   : Thu Dec  3 13:06:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 306 expanded)
%              Number of leaves         :   33 ( 137 expanded)
%              Depth                    :   10
%              Number of atoms          :  483 (1449 expanded)
%              Number of equality atoms :   46 ( 241 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f334,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f48,f53,f58,f63,f68,f73,f78,f83,f104,f124,f144,f170,f183,f186,f211,f216,f221,f226,f241,f286,f292,f298,f304,f314,f316,f333])).

fof(f333,plain,
    ( ~ spl5_7
    | spl5_31
    | ~ spl5_38
    | ~ spl5_39 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl5_7
    | spl5_31
    | ~ spl5_38
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f326,f246])).

fof(f246,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl5_31
  <=> v1_partfun1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f326,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_38
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f67,f297,f303,f33])).

fof(f33,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f30])).

fof(f30,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f303,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl5_39
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f297,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl5_38
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f67,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f316,plain,
    ( k1_xboole_0 != sK0
    | v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK3,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f314,plain,
    ( ~ spl5_10
    | spl5_30
    | ~ spl5_36
    | ~ spl5_37 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl5_10
    | spl5_30
    | ~ spl5_36
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f311,f291])).

fof(f291,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl5_37
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f311,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_10
    | spl5_30
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f82,f285,f240,f33])).

fof(f240,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl5_30
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f285,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl5_36
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f82,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f304,plain,
    ( spl5_39
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f299,f208,f41,f301])).

fof(f41,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f208,plain,
    ( spl5_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f299,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f210,f42])).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f210,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f298,plain,
    ( spl5_38
    | ~ spl5_2
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f293,f213,f41,f295])).

fof(f213,plain,
    ( spl5_25
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f293,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f215,f42])).

fof(f215,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f213])).

fof(f292,plain,
    ( spl5_37
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f287,f218,f41,f289])).

fof(f218,plain,
    ( spl5_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f287,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f220,f42])).

fof(f220,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f286,plain,
    ( spl5_36
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f281,f223,f41,f283])).

fof(f223,plain,
    ( spl5_27
  <=> v1_funct_2(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f281,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f225,f42])).

fof(f225,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f223])).

fof(f241,plain,
    ( ~ spl5_30
    | ~ spl5_3
    | spl5_16 ),
    inference(avatar_split_clause,[],[f194,f126,f45,f238])).

fof(f45,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f126,plain,
    ( spl5_16
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f194,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ spl5_3
    | spl5_16 ),
    inference(backward_demodulation,[],[f127,f47])).

fof(f47,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f127,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f226,plain,
    ( spl5_27
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f191,f75,f45,f223])).

fof(f75,plain,
    ( spl5_9
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f191,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f77,f47])).

fof(f77,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f221,plain,
    ( spl5_26
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f190,f70,f45,f218])).

fof(f70,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f190,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f72,f47])).

fof(f72,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f216,plain,
    ( spl5_25
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f189,f60,f45,f213])).

fof(f60,plain,
    ( spl5_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f189,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f62,f47])).

fof(f62,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f211,plain,
    ( spl5_24
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f188,f55,f45,f208])).

fof(f55,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f188,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f57,f47])).

fof(f57,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f186,plain,
    ( spl5_16
    | spl5_2
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f185,f80,f75,f70,f41,f126])).

fof(f185,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK2,sK0)
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f184,f82])).

fof(f184,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f117,f77])).

fof(f117,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f183,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f181,f155])).

fof(f155,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_19
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f181,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f82,f67,f89,f52,f57,f72,f128,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_funct_1(X3)
      | X2 = X3
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f128,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f52,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( sK2 != sK3
    | spl5_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_11
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f170,plain,
    ( spl5_19
    | spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f169,f65,f60,f55,f41,f153])).

fof(f169,plain,
    ( v1_partfun1(sK3,sK0)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f168,f67])).

fof(f168,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f167,f62])).

fof(f167,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f57,f34])).

fof(f144,plain,
    ( ~ spl5_15
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f118,f70,f120])).

fof(f120,plain,
    ( spl5_15
  <=> sP4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f118,plain,
    ( ~ sP4(sK1,sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP4(X1,X0) ) ),
    inference(general_splitting,[],[f26,f31_D])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f31_D])).

fof(f31_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f124,plain,
    ( spl5_15
    | ~ spl5_8
    | spl5_13 ),
    inference(avatar_split_clause,[],[f113,f101,f70,f120])).

fof(f101,plain,
    ( spl5_13
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f113,plain,
    ( sP4(sK1,sK0)
    | ~ spl5_8
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f103,f72,f31])).

fof(f103,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f101])).

fof(f104,plain,
    ( ~ spl5_13
    | spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f95,f88,f36,f101])).

fof(f36,plain,
    ( spl5_1
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f95,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl5_1
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f38,f90])).

fof(f90,plain,
    ( sK2 = sK3
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f38,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f83,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f17,f80])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f78,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f18,f75])).

fof(f18,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f19,f70])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f20,f65])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f21,f60])).

fof(f21,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f24,f45,f41])).

fof(f24,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f36])).

fof(f25,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:03:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (7310)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (7315)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.46  % (7310)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f334,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f39,f48,f53,f58,f63,f68,f73,f78,f83,f104,f124,f144,f170,f183,f186,f211,f216,f221,f226,f241,f286,f292,f298,f304,f314,f316,f333])).
% 0.19/0.47  fof(f333,plain,(
% 0.19/0.47    ~spl5_7 | spl5_31 | ~spl5_38 | ~spl5_39),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f332])).
% 0.19/0.47  fof(f332,plain,(
% 0.19/0.47    $false | (~spl5_7 | spl5_31 | ~spl5_38 | ~spl5_39)),
% 0.19/0.47    inference(subsumption_resolution,[],[f326,f246])).
% 0.19/0.47  fof(f246,plain,(
% 0.19/0.47    ~v1_partfun1(sK3,k1_xboole_0) | spl5_31),
% 0.19/0.47    inference(avatar_component_clause,[],[f245])).
% 0.19/0.47  fof(f245,plain,(
% 0.19/0.47    spl5_31 <=> v1_partfun1(sK3,k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.19/0.47  fof(f326,plain,(
% 0.19/0.47    v1_partfun1(sK3,k1_xboole_0) | (~spl5_7 | ~spl5_38 | ~spl5_39)),
% 0.19/0.47    inference(unit_resulting_resolution,[],[f67,f297,f303,f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.47    inference(equality_resolution,[],[f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.47    inference(flattening,[],[f10])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.19/0.47  fof(f303,plain,(
% 0.19/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_39),
% 0.19/0.47    inference(avatar_component_clause,[],[f301])).
% 0.19/0.47  fof(f301,plain,(
% 0.19/0.47    spl5_39 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.19/0.47  fof(f297,plain,(
% 0.19/0.47    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl5_38),
% 0.19/0.47    inference(avatar_component_clause,[],[f295])).
% 0.19/0.47  fof(f295,plain,(
% 0.19/0.47    spl5_38 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    v1_funct_1(sK3) | ~spl5_7),
% 0.19/0.47    inference(avatar_component_clause,[],[f65])).
% 0.19/0.47  fof(f65,plain,(
% 0.19/0.47    spl5_7 <=> v1_funct_1(sK3)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.47  fof(f316,plain,(
% 0.19/0.47    k1_xboole_0 != sK0 | v1_partfun1(sK3,sK0) | ~v1_partfun1(sK3,k1_xboole_0)),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  fof(f314,plain,(
% 0.19/0.47    ~spl5_10 | spl5_30 | ~spl5_36 | ~spl5_37),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f313])).
% 0.19/0.47  fof(f313,plain,(
% 0.19/0.47    $false | (~spl5_10 | spl5_30 | ~spl5_36 | ~spl5_37)),
% 0.19/0.47    inference(subsumption_resolution,[],[f311,f291])).
% 0.19/0.47  fof(f291,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_37),
% 0.19/0.47    inference(avatar_component_clause,[],[f289])).
% 0.19/0.47  fof(f289,plain,(
% 0.19/0.47    spl5_37 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.19/0.47  fof(f311,plain,(
% 0.19/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_10 | spl5_30 | ~spl5_36)),
% 0.19/0.47    inference(unit_resulting_resolution,[],[f82,f285,f240,f33])).
% 0.19/0.47  fof(f240,plain,(
% 0.19/0.47    ~v1_partfun1(sK2,k1_xboole_0) | spl5_30),
% 0.19/0.47    inference(avatar_component_clause,[],[f238])).
% 0.19/0.47  fof(f238,plain,(
% 0.19/0.47    spl5_30 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.19/0.47  fof(f285,plain,(
% 0.19/0.47    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl5_36),
% 0.19/0.47    inference(avatar_component_clause,[],[f283])).
% 0.19/0.47  fof(f283,plain,(
% 0.19/0.47    spl5_36 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    v1_funct_1(sK2) | ~spl5_10),
% 0.19/0.47    inference(avatar_component_clause,[],[f80])).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    spl5_10 <=> v1_funct_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.19/0.47  fof(f304,plain,(
% 0.19/0.47    spl5_39 | ~spl5_2 | ~spl5_24),
% 0.19/0.47    inference(avatar_split_clause,[],[f299,f208,f41,f301])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    spl5_2 <=> k1_xboole_0 = sK1),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.47  fof(f208,plain,(
% 0.19/0.47    spl5_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.19/0.47  fof(f299,plain,(
% 0.19/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_2 | ~spl5_24)),
% 0.19/0.47    inference(forward_demodulation,[],[f210,f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | ~spl5_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f41])).
% 0.19/0.47  fof(f210,plain,(
% 0.19/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_24),
% 0.19/0.47    inference(avatar_component_clause,[],[f208])).
% 0.19/0.47  fof(f298,plain,(
% 0.19/0.47    spl5_38 | ~spl5_2 | ~spl5_25),
% 0.19/0.47    inference(avatar_split_clause,[],[f293,f213,f41,f295])).
% 0.19/0.47  fof(f213,plain,(
% 0.19/0.47    spl5_25 <=> v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.19/0.47  fof(f293,plain,(
% 0.19/0.47    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl5_2 | ~spl5_25)),
% 0.19/0.47    inference(forward_demodulation,[],[f215,f42])).
% 0.19/0.47  fof(f215,plain,(
% 0.19/0.47    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl5_25),
% 0.19/0.47    inference(avatar_component_clause,[],[f213])).
% 0.19/0.47  fof(f292,plain,(
% 0.19/0.47    spl5_37 | ~spl5_2 | ~spl5_26),
% 0.19/0.47    inference(avatar_split_clause,[],[f287,f218,f41,f289])).
% 0.19/0.47  fof(f218,plain,(
% 0.19/0.47    spl5_26 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.19/0.47  fof(f287,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_2 | ~spl5_26)),
% 0.19/0.47    inference(forward_demodulation,[],[f220,f42])).
% 0.19/0.47  fof(f220,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_26),
% 0.19/0.47    inference(avatar_component_clause,[],[f218])).
% 0.19/0.47  fof(f286,plain,(
% 0.19/0.47    spl5_36 | ~spl5_2 | ~spl5_27),
% 0.19/0.47    inference(avatar_split_clause,[],[f281,f223,f41,f283])).
% 0.19/0.47  fof(f223,plain,(
% 0.19/0.47    spl5_27 <=> v1_funct_2(sK2,k1_xboole_0,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.19/0.47  fof(f281,plain,(
% 0.19/0.47    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl5_2 | ~spl5_27)),
% 0.19/0.47    inference(forward_demodulation,[],[f225,f42])).
% 0.19/0.47  fof(f225,plain,(
% 0.19/0.47    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl5_27),
% 0.19/0.47    inference(avatar_component_clause,[],[f223])).
% 0.19/0.47  fof(f241,plain,(
% 0.19/0.47    ~spl5_30 | ~spl5_3 | spl5_16),
% 0.19/0.47    inference(avatar_split_clause,[],[f194,f126,f45,f238])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    spl5_3 <=> k1_xboole_0 = sK0),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.47  fof(f126,plain,(
% 0.19/0.47    spl5_16 <=> v1_partfun1(sK2,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.19/0.47  fof(f194,plain,(
% 0.19/0.47    ~v1_partfun1(sK2,k1_xboole_0) | (~spl5_3 | spl5_16)),
% 0.19/0.47    inference(backward_demodulation,[],[f127,f47])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    k1_xboole_0 = sK0 | ~spl5_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f45])).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    ~v1_partfun1(sK2,sK0) | spl5_16),
% 0.19/0.47    inference(avatar_component_clause,[],[f126])).
% 0.19/0.47  fof(f226,plain,(
% 0.19/0.47    spl5_27 | ~spl5_3 | ~spl5_9),
% 0.19/0.47    inference(avatar_split_clause,[],[f191,f75,f45,f223])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    spl5_9 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.19/0.47  fof(f191,plain,(
% 0.19/0.47    v1_funct_2(sK2,k1_xboole_0,sK1) | (~spl5_3 | ~spl5_9)),
% 0.19/0.47    inference(backward_demodulation,[],[f77,f47])).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    v1_funct_2(sK2,sK0,sK1) | ~spl5_9),
% 0.19/0.47    inference(avatar_component_clause,[],[f75])).
% 0.19/0.47  fof(f221,plain,(
% 0.19/0.47    spl5_26 | ~spl5_3 | ~spl5_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f190,f70,f45,f218])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    spl5_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.47  fof(f190,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_3 | ~spl5_8)),
% 0.19/0.47    inference(backward_demodulation,[],[f72,f47])).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_8),
% 0.19/0.47    inference(avatar_component_clause,[],[f70])).
% 0.19/0.47  fof(f216,plain,(
% 0.19/0.47    spl5_25 | ~spl5_3 | ~spl5_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f189,f60,f45,f213])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    spl5_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.47  fof(f189,plain,(
% 0.19/0.47    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl5_3 | ~spl5_6)),
% 0.19/0.47    inference(backward_demodulation,[],[f62,f47])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    v1_funct_2(sK3,sK0,sK1) | ~spl5_6),
% 0.19/0.47    inference(avatar_component_clause,[],[f60])).
% 0.19/0.47  fof(f211,plain,(
% 0.19/0.47    spl5_24 | ~spl5_3 | ~spl5_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f188,f55,f45,f208])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.47  fof(f188,plain,(
% 0.19/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_3 | ~spl5_5)),
% 0.19/0.47    inference(backward_demodulation,[],[f57,f47])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_5),
% 0.19/0.47    inference(avatar_component_clause,[],[f55])).
% 0.19/0.47  fof(f186,plain,(
% 0.19/0.47    spl5_16 | spl5_2 | ~spl5_8 | ~spl5_9 | ~spl5_10),
% 0.19/0.47    inference(avatar_split_clause,[],[f185,f80,f75,f70,f41,f126])).
% 0.19/0.47  fof(f185,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | v1_partfun1(sK2,sK0) | (~spl5_8 | ~spl5_9 | ~spl5_10)),
% 0.19/0.47    inference(subsumption_resolution,[],[f184,f82])).
% 0.19/0.47  fof(f184,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | (~spl5_8 | ~spl5_9)),
% 0.19/0.47    inference(subsumption_resolution,[],[f117,f77])).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_8),
% 0.19/0.47    inference(resolution,[],[f72,f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f183,plain,(
% 0.19/0.47    ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_11 | ~spl5_16 | ~spl5_19),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f182])).
% 0.19/0.47  fof(f182,plain,(
% 0.19/0.47    $false | (~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_11 | ~spl5_16 | ~spl5_19)),
% 0.19/0.47    inference(subsumption_resolution,[],[f181,f155])).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    v1_partfun1(sK3,sK0) | ~spl5_19),
% 0.19/0.47    inference(avatar_component_clause,[],[f153])).
% 0.19/0.47  fof(f153,plain,(
% 0.19/0.47    spl5_19 <=> v1_partfun1(sK3,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.19/0.47  fof(f181,plain,(
% 0.19/0.47    ~v1_partfun1(sK3,sK0) | (~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_11 | ~spl5_16)),
% 0.19/0.47    inference(unit_resulting_resolution,[],[f82,f67,f89,f52,f57,f72,f128,f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~v1_funct_1(X3) | X2 = X3 | ~v1_funct_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.47    inference(flattening,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    v1_partfun1(sK2,sK0) | ~spl5_16),
% 0.19/0.47    inference(avatar_component_clause,[],[f126])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    r1_partfun1(sK2,sK3) | ~spl5_4),
% 0.19/0.47    inference(avatar_component_clause,[],[f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    spl5_4 <=> r1_partfun1(sK2,sK3)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    sK2 != sK3 | spl5_11),
% 0.19/0.47    inference(avatar_component_clause,[],[f88])).
% 0.19/0.47  fof(f88,plain,(
% 0.19/0.47    spl5_11 <=> sK2 = sK3),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.19/0.47  fof(f170,plain,(
% 0.19/0.47    spl5_19 | spl5_2 | ~spl5_5 | ~spl5_6 | ~spl5_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f169,f65,f60,f55,f41,f153])).
% 0.19/0.47  fof(f169,plain,(
% 0.19/0.47    v1_partfun1(sK3,sK0) | (spl5_2 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.19/0.47    inference(subsumption_resolution,[],[f168,f67])).
% 0.19/0.47  fof(f168,plain,(
% 0.19/0.47    v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | (spl5_2 | ~spl5_5 | ~spl5_6)),
% 0.19/0.47    inference(subsumption_resolution,[],[f167,f62])).
% 0.19/0.47  fof(f167,plain,(
% 0.19/0.47    v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | (spl5_2 | ~spl5_5)),
% 0.19/0.47    inference(subsumption_resolution,[],[f150,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    k1_xboole_0 != sK1 | spl5_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f41])).
% 0.19/0.47  fof(f150,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | ~spl5_5),
% 0.19/0.47    inference(resolution,[],[f57,f34])).
% 0.19/0.47  fof(f144,plain,(
% 0.19/0.47    ~spl5_15 | ~spl5_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f118,f70,f120])).
% 0.19/0.47  fof(f120,plain,(
% 0.19/0.47    spl5_15 <=> sP4(sK1,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.19/0.47  fof(f118,plain,(
% 0.19/0.47    ~sP4(sK1,sK0) | ~spl5_8),
% 0.19/0.47    inference(resolution,[],[f72,f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP4(X1,X0)) )),
% 0.19/0.47    inference(general_splitting,[],[f26,f31_D])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (sP4(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31_D])).
% 0.19/0.47  fof(f31_D,plain,(
% 0.19/0.47    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP4(X1,X0)) )),
% 0.19/0.47    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(flattening,[],[f8])).
% 0.19/0.47  fof(f8,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.19/0.47  fof(f124,plain,(
% 0.19/0.47    spl5_15 | ~spl5_8 | spl5_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f113,f101,f70,f120])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    spl5_13 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.19/0.47  fof(f113,plain,(
% 0.19/0.47    sP4(sK1,sK0) | (~spl5_8 | spl5_13)),
% 0.19/0.47    inference(unit_resulting_resolution,[],[f103,f72,f31])).
% 0.19/0.47  fof(f103,plain,(
% 0.19/0.47    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl5_13),
% 0.19/0.47    inference(avatar_component_clause,[],[f101])).
% 0.19/0.47  fof(f104,plain,(
% 0.19/0.47    ~spl5_13 | spl5_1 | ~spl5_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f95,f88,f36,f101])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    spl5_1 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.47  fof(f95,plain,(
% 0.19/0.47    ~r2_relset_1(sK0,sK1,sK2,sK2) | (spl5_1 | ~spl5_11)),
% 0.19/0.47    inference(backward_demodulation,[],[f38,f90])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    sK2 = sK3 | ~spl5_11),
% 0.19/0.47    inference(avatar_component_clause,[],[f88])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl5_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f36])).
% 0.19/0.47  fof(f83,plain,(
% 0.19/0.47    spl5_10),
% 0.19/0.47    inference(avatar_split_clause,[],[f17,f80])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    v1_funct_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f7,plain,(
% 0.19/0.47    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.47    inference(flattening,[],[f6])).
% 0.19/0.47  fof(f6,plain,(
% 0.19/0.47    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.19/0.47    inference(negated_conjecture,[],[f4])).
% 0.19/0.47  fof(f4,conjecture,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    spl5_9),
% 0.19/0.47    inference(avatar_split_clause,[],[f18,f75])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    spl5_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f19,f70])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    spl5_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f20,f65])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    v1_funct_1(sK3)),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    spl5_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f21,f60])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    spl5_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f22,f55])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    spl5_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f23,f50])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    r1_partfun1(sK2,sK3)),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ~spl5_2 | spl5_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f24,f45,f41])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ~spl5_1),
% 0.19/0.47    inference(avatar_split_clause,[],[f25,f36])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (7310)------------------------------
% 0.19/0.47  % (7310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (7310)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (7310)Memory used [KB]: 6396
% 0.19/0.47  % (7310)Time elapsed: 0.069 s
% 0.19/0.47  % (7310)------------------------------
% 0.19/0.47  % (7310)------------------------------
% 0.19/0.48  % (7296)Success in time 0.13 s
%------------------------------------------------------------------------------
