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
% DateTime   : Thu Dec  3 13:13:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 328 expanded)
%              Number of leaves         :   44 ( 152 expanded)
%              Depth                    :   10
%              Number of atoms          :  546 (1278 expanded)
%              Number of equality atoms :  133 ( 423 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f82,f86,f90,f94,f98,f102,f106,f112,f124,f128,f136,f146,f168,f177,f188,f203,f207,f209,f212,f222,f224,f225,f237,f257,f262,f273,f276])).

fof(f276,plain,
    ( ~ spl3_6
    | spl3_29
    | ~ spl3_30
    | ~ spl3_10
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f269,f255,f110,f265,f260,f92])).

fof(f92,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f260,plain,
    ( spl3_29
  <=> o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f265,plain,
    ( spl3_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f110,plain,
    ( spl3_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f255,plain,
    ( spl3_28
  <=> v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f269,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_10
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f268,f113])).

fof(f113,plain,
    ( ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0)
    | ~ spl3_10 ),
    inference(superposition,[],[f70,f111])).

fof(f111,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_28 ),
    inference(resolution,[],[f256,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f256,plain,
    ( v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f273,plain,
    ( spl3_30
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f271,f218,f139,f110,f265])).

fof(f139,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f218,plain,
    ( spl3_23
  <=> o_0_0_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f271,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f270,f113])).

fof(f270,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),o_0_0_xboole_0)))
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(superposition,[],[f140,f219])).

fof(f219,plain,
    ( o_0_0_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f218])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f262,plain,
    ( ~ spl3_29
    | spl3_16
    | ~ spl3_23
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f258,f227,f218,f166,f260])).

fof(f166,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f227,plain,
    ( spl3_24
  <=> o_0_0_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f258,plain,
    ( o_0_0_xboole_0 != k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)
    | spl3_16
    | ~ spl3_23
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f241,f228])).

fof(f228,plain,
    ( o_0_0_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f227])).

fof(f241,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),o_0_0_xboole_0,sK2)
    | spl3_16
    | ~ spl3_23 ),
    inference(superposition,[],[f167,f219])).

fof(f167,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f257,plain,
    ( spl3_28
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f253,f227,f218,f144,f255])).

fof(f144,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f253,plain,
    ( v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f240,f228])).

fof(f240,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),o_0_0_xboole_0)
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(superposition,[],[f145,f219])).

fof(f145,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f237,plain,
    ( spl3_24
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f236,f110,f80,f227])).

fof(f80,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f236,plain,
    ( o_0_0_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f81,f111])).

fof(f81,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f225,plain,
    ( o_0_0_xboole_0 != k1_xboole_0
    | o_0_0_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f224,plain,
    ( ~ spl3_14
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f140,f202])).

fof(f202,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_22
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f222,plain,
    ( spl3_23
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f221,f197,f110,f218])).

fof(f197,plain,
    ( spl3_21
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f221,plain,
    ( o_0_0_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f216,f111])).

fof(f216,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_21 ),
    inference(resolution,[],[f198,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f198,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f197])).

fof(f212,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f211,f126,f122,f84,f139])).

fof(f84,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f122,plain,
    ( spl3_11
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f126,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f211,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f210,f127])).

% (30918)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f127,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f210,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f85,f123])).

fof(f123,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f209,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f207,plain,
    ( ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f85,f187])).

fof(f187,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_20
  <=> ! [X1,X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f203,plain,
    ( spl3_21
    | ~ spl3_14
    | spl3_18
    | spl3_22
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f195,f183,f126,f122,f88,f201,f175,f139,f197])).

fof(f175,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f88,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f183,plain,
    ( spl3_19
  <=> ! [X3,X2,X4] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | k1_relat_1(sK2) = X2
        | ~ v1_funct_2(sK2,X2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | v1_xboole_0(k2_struct_0(sK1)) )
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f194,f127])).

fof(f194,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | v1_xboole_0(k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f193,f127])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | v1_xboole_0(k2_struct_0(sK1))
        | u1_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f192,f127])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
        | v1_xboole_0(k2_struct_0(sK1))
        | u1_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f191,f123])).

fof(f191,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | u1_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f189,f123])).

fof(f189,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | u1_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(resolution,[],[f184,f89])).

fof(f89,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f184,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_funct_2(sK2,X2,X4)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | k1_relat_1(sK2) = X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f188,plain,
    ( spl3_19
    | spl3_20
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f181,f92,f186,f183])).

fof(f181,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(sK2,X2,X4)
        | k1_relat_1(sK2) = X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | v1_xboole_0(X4) )
    | ~ spl3_6 ),
    inference(resolution,[],[f180,f93])).

fof(f93,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f180,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X8)))
      | ~ v1_funct_2(X4,X5,X9)
      | k1_relat_1(X4) = X5
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X9)))
      | v1_xboole_0(X9) ) ),
    inference(resolution,[],[f178,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

% (30910)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f178,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f162,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f57,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f177,plain,
    ( ~ spl3_17
    | ~ spl3_18
    | spl3_16 ),
    inference(avatar_split_clause,[],[f170,f166,f175,f172])).

fof(f172,plain,
    ( spl3_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f170,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | spl3_16 ),
    inference(inner_rewriting,[],[f169])).

fof(f169,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_16 ),
    inference(superposition,[],[f167,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f168,plain,
    ( ~ spl3_14
    | ~ spl3_16
    | spl3_13 ),
    inference(avatar_split_clause,[],[f163,f134,f166,f139])).

fof(f134,plain,
    ( spl3_13
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f163,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_13 ),
    inference(superposition,[],[f135,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f135,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f146,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f142,f126,f122,f88,f144])).

fof(f142,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f131,f127])).

fof(f131,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f89,f123])).

fof(f136,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f132,f126,f122,f73,f134])).

fof(f73,plain,
    ( spl3_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f132,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f129,f127])).

fof(f129,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_11 ),
    inference(superposition,[],[f74,f123])).

fof(f74,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f128,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f120,f100,f126])).

fof(f100,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f120,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f52,f101])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f124,plain,
    ( spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f119,f96,f122])).

fof(f96,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f119,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f52,f97])).

fof(f97,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f112,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f108,f104,f110])).

fof(f104,plain,
    ( spl3_9
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f108,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_9 ),
    inference(resolution,[],[f53,f105])).

fof(f105,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f49,f104])).

fof(f49,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f102,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f98,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f46,f84])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f47,f80,f77])).

fof(f77,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f48,f73])).

fof(f48,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (30921)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (30913)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (30912)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (30912)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (30920)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f75,f82,f86,f90,f94,f98,f102,f106,f112,f124,f128,f136,f146,f168,f177,f188,f203,f207,f209,f212,f222,f224,f225,f237,f257,f262,f273,f276])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    ~spl3_6 | spl3_29 | ~spl3_30 | ~spl3_10 | ~spl3_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f269,f255,f110,f265,f260,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl3_6 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    spl3_29 <=> o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    spl3_30 <=> m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl3_10 <=> o_0_0_xboole_0 = k1_xboole_0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    spl3_28 <=> v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) | o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) | ~v1_funct_1(sK2) | (~spl3_10 | ~spl3_28)),
% 0.21/0.48    inference(forward_demodulation,[],[f268,f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X0] : (o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0)) ) | ~spl3_10),
% 0.21/0.48    inference(superposition,[],[f70,f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    o_0_0_xboole_0 = k1_xboole_0 | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f110])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) | o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) | ~v1_funct_1(sK2) | ~spl3_28),
% 0.21/0.48    inference(resolution,[],[f256,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0) | ~spl3_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f255])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    spl3_30 | ~spl3_10 | ~spl3_14 | ~spl3_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f271,f218,f139,f110,f265])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl3_23 <=> o_0_0_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) | (~spl3_10 | ~spl3_14 | ~spl3_23)),
% 0.21/0.48    inference(forward_demodulation,[],[f270,f113])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),o_0_0_xboole_0))) | (~spl3_14 | ~spl3_23)),
% 0.21/0.48    inference(superposition,[],[f140,f219])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    o_0_0_xboole_0 = k2_struct_0(sK1) | ~spl3_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    ~spl3_29 | spl3_16 | ~spl3_23 | ~spl3_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f258,f227,f218,f166,f260])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl3_16 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    spl3_24 <=> o_0_0_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    o_0_0_xboole_0 != k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) | (spl3_16 | ~spl3_23 | ~spl3_24)),
% 0.21/0.48    inference(forward_demodulation,[],[f241,f228])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    o_0_0_xboole_0 = k2_struct_0(sK0) | ~spl3_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f227])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),o_0_0_xboole_0,sK2) | (spl3_16 | ~spl3_23)),
% 0.21/0.48    inference(superposition,[],[f167,f219])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f166])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    spl3_28 | ~spl3_15 | ~spl3_23 | ~spl3_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f253,f227,f218,f144,f255])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl3_15 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0) | (~spl3_15 | ~spl3_23 | ~spl3_24)),
% 0.21/0.48    inference(forward_demodulation,[],[f240,f228])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    v1_funct_2(sK2,k2_struct_0(sK0),o_0_0_xboole_0) | (~spl3_15 | ~spl3_23)),
% 0.21/0.48    inference(superposition,[],[f145,f219])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f144])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    spl3_24 | ~spl3_3 | ~spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f236,f110,f80,f227])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl3_3 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    o_0_0_xboole_0 = k2_struct_0(sK0) | (~spl3_3 | ~spl3_10)),
% 0.21/0.48    inference(forward_demodulation,[],[f81,f111])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    o_0_0_xboole_0 != k1_xboole_0 | o_0_0_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    ~spl3_14 | ~spl3_22),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f223])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    $false | (~spl3_14 | ~spl3_22)),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f202])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f201])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    spl3_22 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    spl3_23 | ~spl3_10 | ~spl3_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f221,f197,f110,f218])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl3_21 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    o_0_0_xboole_0 = k2_struct_0(sK1) | (~spl3_10 | ~spl3_21)),
% 0.21/0.48    inference(forward_demodulation,[],[f216,f111])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_21),
% 0.21/0.48    inference(resolution,[],[f198,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f197])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    spl3_14 | ~spl3_4 | ~spl3_11 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f211,f126,f122,f84,f139])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl3_11 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl3_12 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_11 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f210,f127])).
% 0.21/0.48  % (30918)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f126])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_11)),
% 0.21/0.48    inference(forward_demodulation,[],[f85,f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f122])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_20),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f205])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    $false | (~spl3_4 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f187])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl3_20 <=> ! [X1,X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    spl3_21 | ~spl3_14 | spl3_18 | spl3_22 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f195,f183,f126,f122,f88,f201,f175,f139,f197])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    spl3_18 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    spl3_19 <=> ! [X3,X2,X4] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | k1_relat_1(sK2) = X2 | ~v1_funct_2(sK2,X2,X4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_xboole_0(k2_struct_0(sK1))) ) | (~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f194,f127])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    ( ! [X0] : (k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_xboole_0(k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f193,f127])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_xboole_0(k2_struct_0(sK1)) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f192,f127])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v1_xboole_0(k2_struct_0(sK1)) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f191,f123])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f189,f123])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_19)),
% 0.21/0.48    inference(resolution,[],[f184,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ( ! [X4,X2,X3] : (~v1_funct_2(sK2,X2,X4) | v1_xboole_0(X4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | k1_relat_1(sK2) = X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl3_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f183])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    spl3_19 | spl3_20 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f181,f92,f186,f183])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X4) | k1_relat_1(sK2) = X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | v1_xboole_0(X4)) ) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f180,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    ( ! [X6,X4,X8,X7,X5,X9] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X8))) | ~v1_funct_2(X4,X5,X9) | k1_relat_1(X4) = X5 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X9))) | v1_xboole_0(X9)) )),
% 0.21/0.48    inference(resolution,[],[f178,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % (30910)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.21/0.48    inference(resolution,[],[f162,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.48    inference(resolution,[],[f57,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ~spl3_17 | ~spl3_18 | spl3_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f170,f166,f175,f172])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl3_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | spl3_16),
% 0.21/0.48    inference(inner_rewriting,[],[f169])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_16),
% 0.21/0.48    inference(superposition,[],[f167,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ~spl3_14 | ~spl3_16 | spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f163,f134,f166,f139])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl3_13 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_13),
% 0.21/0.48    inference(superposition,[],[f135,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f134])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl3_15 | ~spl3_5 | ~spl3_11 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f142,f126,f122,f88,f144])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f131,f127])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_11)),
% 0.21/0.48    inference(superposition,[],[f89,f123])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ~spl3_13 | spl3_1 | ~spl3_11 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f132,f126,f122,f73,f134])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl3_1 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_11 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f129,f127])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_11)),
% 0.21/0.48    inference(superposition,[],[f74,f123])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl3_12 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f100,f126])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl3_8 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.21/0.48    inference(resolution,[],[f52,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl3_11 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f119,f96,f122])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl3_7 <=> l1_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.21/0.48    inference(resolution,[],[f52,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    l1_struct_0(sK1) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl3_10 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f108,f104,f110])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl3_9 <=> v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    o_0_0_xboole_0 = k1_xboole_0 | ~spl3_9),
% 0.21/0.48    inference(resolution,[],[f53,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v1_xboole_0(o_0_0_xboole_0) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f104])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f100])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    l1_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f37,f36,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f16])).
% 0.21/0.48  fof(f16,conjecture,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f96])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    l1_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f92])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f88])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f84])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~spl3_2 | spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f80,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f73])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30912)------------------------------
% 0.21/0.48  % (30912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30912)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30912)Memory used [KB]: 10746
% 0.21/0.48  % (30912)Time elapsed: 0.059 s
% 0.21/0.48  % (30912)------------------------------
% 0.21/0.48  % (30912)------------------------------
% 0.21/0.48  % (30905)Success in time 0.121 s
%------------------------------------------------------------------------------
