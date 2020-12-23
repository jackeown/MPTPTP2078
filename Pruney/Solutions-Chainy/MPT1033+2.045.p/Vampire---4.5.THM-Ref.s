%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 297 expanded)
%              Number of leaves         :   31 ( 129 expanded)
%              Depth                    :   10
%              Number of atoms          :  485 (1436 expanded)
%              Number of equality atoms :   52 ( 247 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f50,f55,f60,f65,f70,f75,f80,f85,f106,f119,f188,f191,f194,f222,f227,f232,f237,f254,f306,f312,f318,f324,f335,f336,f352])).

fof(f352,plain,
    ( ~ spl4_10
    | spl4_32
    | ~ spl4_36
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl4_10
    | spl4_32
    | ~ spl4_36
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f342,f266])).

fof(f266,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl4_32
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f342,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_36
    | ~ spl4_37 ),
    inference(unit_resulting_resolution,[],[f84,f305,f311,f35])).

fof(f35,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f311,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl4_37
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f305,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl4_36
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f84,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f336,plain,
    ( k1_xboole_0 != sK0
    | v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK2,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f335,plain,
    ( ~ spl4_7
    | spl4_30
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl4_7
    | spl4_30
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f333,f323])).

fof(f323,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl4_39
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f333,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_7
    | spl4_30
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f69,f253,f317,f35])).

fof(f317,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl4_38
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f253,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_30
  <=> v1_partfun1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f69,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f324,plain,
    ( spl4_39
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f319,f219,f43,f321])).

fof(f43,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f219,plain,
    ( spl4_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f319,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f221,f44])).

fof(f44,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f221,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f318,plain,
    ( spl4_38
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f313,f224,f43,f315])).

fof(f224,plain,
    ( spl4_25
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f313,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f226,f44])).

fof(f226,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f224])).

fof(f312,plain,
    ( spl4_37
    | ~ spl4_2
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f307,f229,f43,f309])).

fof(f229,plain,
    ( spl4_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f307,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_2
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f231,f44])).

fof(f231,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f229])).

fof(f306,plain,
    ( spl4_36
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f301,f234,f43,f303])).

fof(f234,plain,
    ( spl4_27
  <=> v1_funct_2(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f301,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f236,f44])).

fof(f236,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f234])).

fof(f254,plain,
    ( ~ spl4_30
    | ~ spl4_3
    | spl4_16 ),
    inference(avatar_split_clause,[],[f204,f136,f47,f251])).

fof(f47,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f136,plain,
    ( spl4_16
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f204,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ spl4_3
    | spl4_16 ),
    inference(backward_demodulation,[],[f137,f49])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f137,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f237,plain,
    ( spl4_27
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f199,f77,f47,f234])).

fof(f77,plain,
    ( spl4_9
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f199,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f79,f49])).

fof(f79,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f232,plain,
    ( spl4_26
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f198,f72,f47,f229])).

fof(f72,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f198,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f74,f49])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f227,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f197,f62,f47,f224])).

fof(f62,plain,
    ( spl4_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f197,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f64,f49])).

fof(f64,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f222,plain,
    ( spl4_24
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f196,f57,f47,f219])).

fof(f57,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f196,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f59,f49])).

fof(f59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f194,plain,
    ( spl4_16
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f193,f67,f62,f57,f43,f136])).

fof(f193,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK3,sK0)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f192,f69])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f127,f64])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f191,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | spl4_11
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | spl4_11
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f189,f173])).

fof(f173,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_20
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f189,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | spl4_11
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f84,f69,f91,f54,f74,f59,f138,f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f138,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f54,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,
    ( sK2 != sK3
    | spl4_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_11
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f188,plain,
    ( spl4_20
    | spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f187,f82,f77,f72,f43,f171])).

fof(f187,plain,
    ( v1_partfun1(sK2,sK0)
    | spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f186,f84])).

fof(f186,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f185,f79])).

fof(f185,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f162,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f162,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f74,f36])).

fof(f119,plain,
    ( ~ spl4_8
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl4_8
    | spl4_13 ),
    inference(subsumption_resolution,[],[f115,f74])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_13 ),
    inference(resolution,[],[f105,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f105,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f106,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f97,f90,f38,f103])).

fof(f38,plain,
    ( spl4_1
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f97,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl4_1
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f40,f92])).

fof(f92,plain,
    ( sK2 = sK3
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f40,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f85,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f18,f82])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f80,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f19,f77])).

fof(f19,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f20,f72])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f21,f67])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f62])).

fof(f22,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f25,f47,f43])).

fof(f25,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f38])).

fof(f26,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:23:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (23558)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (23558)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (23566)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (23552)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (23552)Refutation not found, incomplete strategy% (23552)------------------------------
% 0.20/0.50  % (23552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23567)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (23548)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f353,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f41,f50,f55,f60,f65,f70,f75,f80,f85,f106,f119,f188,f191,f194,f222,f227,f232,f237,f254,f306,f312,f318,f324,f335,f336,f352])).
% 0.20/0.51  fof(f352,plain,(
% 0.20/0.51    ~spl4_10 | spl4_32 | ~spl4_36 | ~spl4_37),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f351])).
% 0.20/0.51  fof(f351,plain,(
% 0.20/0.51    $false | (~spl4_10 | spl4_32 | ~spl4_36 | ~spl4_37)),
% 0.20/0.51    inference(subsumption_resolution,[],[f342,f266])).
% 0.20/0.51  fof(f266,plain,(
% 0.20/0.51    ~v1_partfun1(sK2,k1_xboole_0) | spl4_32),
% 0.20/0.51    inference(avatar_component_clause,[],[f265])).
% 0.20/0.51  fof(f265,plain,(
% 0.20/0.51    spl4_32 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.51  fof(f342,plain,(
% 0.20/0.51    v1_partfun1(sK2,k1_xboole_0) | (~spl4_10 | ~spl4_36 | ~spl4_37)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f84,f305,f311,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(equality_resolution,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.20/0.51  fof(f311,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_37),
% 0.20/0.51    inference(avatar_component_clause,[],[f309])).
% 0.20/0.51  fof(f309,plain,(
% 0.20/0.51    spl4_37 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.51  fof(f305,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl4_36),
% 0.20/0.51    inference(avatar_component_clause,[],[f303])).
% 0.20/0.51  fof(f303,plain,(
% 0.20/0.51    spl4_36 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    v1_funct_1(sK2) | ~spl4_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl4_10 <=> v1_funct_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.51  fof(f336,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | v1_partfun1(sK2,sK0) | ~v1_partfun1(sK2,k1_xboole_0)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f335,plain,(
% 0.20/0.51    ~spl4_7 | spl4_30 | ~spl4_38 | ~spl4_39),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f334])).
% 0.20/0.51  fof(f334,plain,(
% 0.20/0.51    $false | (~spl4_7 | spl4_30 | ~spl4_38 | ~spl4_39)),
% 0.20/0.51    inference(subsumption_resolution,[],[f333,f323])).
% 0.20/0.51  fof(f323,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_39),
% 0.20/0.51    inference(avatar_component_clause,[],[f321])).
% 0.20/0.51  fof(f321,plain,(
% 0.20/0.51    spl4_39 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.51  fof(f333,plain,(
% 0.20/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_7 | spl4_30 | ~spl4_38)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f69,f253,f317,f35])).
% 0.20/0.51  fof(f317,plain,(
% 0.20/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl4_38),
% 0.20/0.51    inference(avatar_component_clause,[],[f315])).
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    spl4_38 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    ~v1_partfun1(sK3,k1_xboole_0) | spl4_30),
% 0.20/0.51    inference(avatar_component_clause,[],[f251])).
% 0.20/0.51  fof(f251,plain,(
% 0.20/0.51    spl4_30 <=> v1_partfun1(sK3,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    v1_funct_1(sK3) | ~spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl4_7 <=> v1_funct_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f324,plain,(
% 0.20/0.51    spl4_39 | ~spl4_2 | ~spl4_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f319,f219,f43,f321])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    spl4_2 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    spl4_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.51  fof(f319,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_2 | ~spl4_24)),
% 0.20/0.51    inference(forward_demodulation,[],[f221,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f43])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f219])).
% 0.20/0.51  fof(f318,plain,(
% 0.20/0.51    spl4_38 | ~spl4_2 | ~spl4_25),
% 0.20/0.51    inference(avatar_split_clause,[],[f313,f224,f43,f315])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    spl4_25 <=> v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.51  fof(f313,plain,(
% 0.20/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_2 | ~spl4_25)),
% 0.20/0.51    inference(forward_demodulation,[],[f226,f44])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl4_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f224])).
% 0.20/0.51  fof(f312,plain,(
% 0.20/0.51    spl4_37 | ~spl4_2 | ~spl4_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f307,f229,f43,f309])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    spl4_26 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.51  fof(f307,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_2 | ~spl4_26)),
% 0.20/0.51    inference(forward_demodulation,[],[f231,f44])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f229])).
% 0.20/0.51  fof(f306,plain,(
% 0.20/0.51    spl4_36 | ~spl4_2 | ~spl4_27),
% 0.20/0.51    inference(avatar_split_clause,[],[f301,f234,f43,f303])).
% 0.20/0.51  fof(f234,plain,(
% 0.20/0.51    spl4_27 <=> v1_funct_2(sK2,k1_xboole_0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.51  fof(f301,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl4_2 | ~spl4_27)),
% 0.20/0.51    inference(forward_demodulation,[],[f236,f44])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl4_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f234])).
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    ~spl4_30 | ~spl4_3 | spl4_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f204,f136,f47,f251])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    spl4_3 <=> k1_xboole_0 = sK0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl4_16 <=> v1_partfun1(sK3,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    ~v1_partfun1(sK3,k1_xboole_0) | (~spl4_3 | spl4_16)),
% 0.20/0.51    inference(backward_demodulation,[],[f137,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f47])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ~v1_partfun1(sK3,sK0) | spl4_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    spl4_27 | ~spl4_3 | ~spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f199,f77,f47,f234])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl4_9 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_xboole_0,sK1) | (~spl4_3 | ~spl4_9)),
% 0.20/0.51    inference(backward_demodulation,[],[f79,f49])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f77])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    spl4_26 | ~spl4_3 | ~spl4_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f198,f72,f47,f229])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_3 | ~spl4_8)),
% 0.20/0.51    inference(backward_demodulation,[],[f74,f49])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f72])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    spl4_25 | ~spl4_3 | ~spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f197,f62,f47,f224])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl4_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl4_3 | ~spl4_6)),
% 0.20/0.51    inference(backward_demodulation,[],[f64,f49])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK0,sK1) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f62])).
% 0.20/0.51  fof(f222,plain,(
% 0.20/0.51    spl4_24 | ~spl4_3 | ~spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f196,f57,f47,f219])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_3 | ~spl4_5)),
% 0.20/0.51    inference(backward_demodulation,[],[f59,f49])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f57])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    spl4_16 | spl4_2 | ~spl4_5 | ~spl4_6 | ~spl4_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f193,f67,f62,f57,f43,f136])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | v1_partfun1(sK3,sK0) | (~spl4_5 | ~spl4_6 | ~spl4_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f192,f69])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | (~spl4_5 | ~spl4_6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f127,f64])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | ~spl4_5),
% 0.20/0.51    inference(resolution,[],[f59,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_10 | spl4_11 | ~spl4_16 | ~spl4_20),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f190])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    $false | (~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_10 | spl4_11 | ~spl4_16 | ~spl4_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f189,f173])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    v1_partfun1(sK2,sK0) | ~spl4_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f171])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    spl4_20 <=> v1_partfun1(sK2,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    ~v1_partfun1(sK2,sK0) | (~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_10 | spl4_11 | ~spl4_16)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f84,f69,f91,f54,f74,f59,f138,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~v1_funct_1(X3) | X2 = X3 | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    v1_partfun1(sK3,sK0) | ~spl4_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    r1_partfun1(sK2,sK3) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    spl4_4 <=> r1_partfun1(sK2,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    sK2 != sK3 | spl4_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl4_11 <=> sK2 = sK3),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    spl4_20 | spl4_2 | ~spl4_8 | ~spl4_9 | ~spl4_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f187,f82,f77,f72,f43,f171])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    v1_partfun1(sK2,sK0) | (spl4_2 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f186,f84])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_8 | ~spl4_9)),
% 0.20/0.51    inference(subsumption_resolution,[],[f185,f79])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f162,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f43])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_8),
% 0.20/0.51    inference(resolution,[],[f74,f36])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ~spl4_8 | spl4_13),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    $false | (~spl4_8 | spl4_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f74])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_13),
% 0.20/0.51    inference(resolution,[],[f105,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl4_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    spl4_13 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ~spl4_13 | spl4_1 | ~spl4_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f97,f90,f38,f103])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    spl4_1 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,sK1,sK2,sK2) | (spl4_1 | ~spl4_11)),
% 0.20/0.51    inference(backward_demodulation,[],[f40,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    sK2 = sK3 | ~spl4_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f38])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl4_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f18,f82])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f6])).
% 0.20/0.51  fof(f6,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f4])).
% 0.20/0.51  fof(f4,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f19,f77])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl4_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f20,f72])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl4_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f21,f67])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    v1_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f22,f62])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f23,f57])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f52])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    r1_partfun1(sK2,sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ~spl4_2 | spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f47,f43])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f38])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (23558)------------------------------
% 0.20/0.51  % (23558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23558)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (23558)Memory used [KB]: 6396
% 0.20/0.51  % (23558)Time elapsed: 0.069 s
% 0.20/0.51  % (23558)------------------------------
% 0.20/0.51  % (23558)------------------------------
% 0.20/0.51  % (23544)Success in time 0.153 s
%------------------------------------------------------------------------------
