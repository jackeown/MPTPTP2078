%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 316 expanded)
%              Number of leaves         :   38 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  530 (1287 expanded)
%              Number of equality atoms :  112 ( 387 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f60,f64,f68,f72,f76,f80,f86,f90,f98,f103,f108,f122,f131,f140,f149,f153,f168,f170,f172,f196,f222,f227,f235,f241,f244])).

fof(f244,plain,
    ( ~ spl3_27
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl3_27
    | spl3_30 ),
    inference(subsumption_resolution,[],[f219,f242])).

fof(f242,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | spl3_30 ),
    inference(resolution,[],[f239,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f239,plain,
    ( ~ v4_relat_1(sK2,k1_xboole_0)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl3_30
  <=> v4_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl3_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f241,plain,
    ( ~ spl3_17
    | ~ spl3_30
    | spl3_28
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f236,f233,f225,f238,f135])).

fof(f135,plain,
    ( spl3_17
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f225,plain,
    ( spl3_28
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f233,plain,
    ( spl3_29
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f236,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_29 ),
    inference(resolution,[],[f234,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f234,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f233])).

fof(f235,plain,
    ( ~ spl3_6
    | ~ spl3_25
    | spl3_29
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f229,f218,f233,f194,f70])).

fof(f70,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f194,plain,
    ( spl3_25
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f229,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f219,f49])).

fof(f49,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f227,plain,
    ( ~ spl3_28
    | ~ spl3_3
    | spl3_16 ),
    inference(avatar_split_clause,[],[f223,f129,f58,f225])).

fof(f58,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f129,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f223,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_3
    | spl3_16 ),
    inference(superposition,[],[f130,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f130,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f222,plain,
    ( spl3_27
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f221,f101,f58,f55,f218])).

fof(f55,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f101,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f221,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f215,f59])).

fof(f215,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(superposition,[],[f102,f163])).

fof(f163,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f196,plain,
    ( spl3_25
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f192,f106,f58,f55,f194])).

fof(f106,plain,
    ( spl3_13
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f192,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f181,f163])).

fof(f181,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(superposition,[],[f107,f59])).

fof(f107,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f172,plain,
    ( ~ spl3_12
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f102,f167])).

fof(f167,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_20
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f170,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f168,plain,
    ( spl3_16
    | spl3_2
    | ~ spl3_13
    | spl3_20
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f161,f138,f88,f84,f62,f166,f106,f55,f129])).

fof(f62,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f84,plain,
    ( spl3_9
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,
    ( spl3_10
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f138,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | k1_xboole_0 = k2_struct_0(sK1)
        | k2_struct_0(sK0) = k1_relat_1(sK2) )
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f160,f89])).

fof(f89,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | k1_xboole_0 = k2_struct_0(sK1)
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f159,f89])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
        | k1_xboole_0 = k2_struct_0(sK1)
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f158,f85])).

fof(f85,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f158,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_struct_0(sK1)
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f157,f85])).

fof(f157,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) = k1_relat_1(sK2)
        | k1_xboole_0 = u1_struct_0(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f155,f89])).

fof(f155,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = k1_relat_1(sK2)
        | k1_xboole_0 = u1_struct_0(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(resolution,[],[f154,f63])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(sK2) = X0
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
    | ~ spl3_18 ),
    inference(resolution,[],[f139,f41])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(sK2) = X0
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f153,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_19 ),
    inference(resolution,[],[f148,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f148,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_19
  <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f149,plain,
    ( ~ spl3_19
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | spl3_17 ),
    inference(avatar_split_clause,[],[f145,f135,f88,f84,f62,f147])).

fof(f145,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | spl3_17 ),
    inference(forward_demodulation,[],[f144,f89])).

fof(f144,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_9
    | spl3_17 ),
    inference(forward_demodulation,[],[f142,f85])).

fof(f142,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl3_4
    | spl3_17 ),
    inference(resolution,[],[f141,f63])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_17 ),
    inference(resolution,[],[f136,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f135])).

fof(f140,plain,
    ( ~ spl3_17
    | spl3_18
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f133,f70,f138,f135])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_6 ),
    inference(resolution,[],[f132,f38])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | spl3_14 ),
    inference(avatar_split_clause,[],[f124,f120,f129,f126])).

fof(f126,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f120,plain,
    ( spl3_14
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f124,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | spl3_14 ),
    inference(inner_rewriting,[],[f123])).

fof(f123,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_14 ),
    inference(superposition,[],[f121,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f121,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( ~ spl3_12
    | ~ spl3_14
    | spl3_11 ),
    inference(avatar_split_clause,[],[f117,f96,f120,f101])).

fof(f96,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f117,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_11 ),
    inference(superposition,[],[f97,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f97,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f108,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f104,f88,f84,f66,f106])).

fof(f66,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f104,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f93,f89])).

fof(f93,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f67,f85])).

fof(f67,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f103,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f99,f88,f84,f62,f101])).

fof(f99,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f92,f89])).

fof(f92,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f63,f85])).

fof(f98,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f94,f88,f84,f51,f96])).

fof(f51,plain,
    ( spl3_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f94,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f91,f89])).

fof(f91,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f52,f85])).

fof(f52,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f90,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f82,f78,f88])).

fof(f78,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f35,f79])).

fof(f79,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f86,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f81,f74,f84])).

fof(f74,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f81,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f35,f75])).

fof(f75,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f80,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f78])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

% (9908)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (9899)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (9908)Refutation not found, incomplete strategy% (9908)------------------------------
% (9908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9908)Termination reason: Refutation not found, incomplete strategy

% (9908)Memory used [KB]: 6012
% (9908)Time elapsed: 0.003 s
% (9908)------------------------------
% (9908)------------------------------
fof(f12,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f76,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f74])).

fof(f29,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f33,f58,f55])).

fof(f33,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f34,f51])).

fof(f34,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (9902)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (9911)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (9902)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (9901)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (9905)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (9910)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f53,f60,f64,f68,f72,f76,f80,f86,f90,f98,f103,f108,f122,f131,f140,f149,f153,f168,f170,f172,f196,f222,f227,f235,f241,f244])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    ~spl3_27 | spl3_30),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f243])).
% 0.20/0.48  fof(f243,plain,(
% 0.20/0.48    $false | (~spl3_27 | spl3_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f219,f242])).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | spl3_30),
% 0.20/0.48    inference(resolution,[],[f239,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f239,plain,(
% 0.20/0.48    ~v4_relat_1(sK2,k1_xboole_0) | spl3_30),
% 0.20/0.48    inference(avatar_component_clause,[],[f238])).
% 0.20/0.48  fof(f238,plain,(
% 0.20/0.48    spl3_30 <=> v4_relat_1(sK2,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_27),
% 0.20/0.48    inference(avatar_component_clause,[],[f218])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    spl3_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.48  fof(f241,plain,(
% 0.20/0.48    ~spl3_17 | ~spl3_30 | spl3_28 | ~spl3_29),
% 0.20/0.48    inference(avatar_split_clause,[],[f236,f233,f225,f238,f135])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl3_17 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    spl3_28 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    spl3_29 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.48  fof(f236,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(sK2) | ~v4_relat_1(sK2,k1_xboole_0) | ~v1_relat_1(sK2) | ~spl3_29),
% 0.20/0.48    inference(resolution,[],[f234,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    v1_partfun1(sK2,k1_xboole_0) | ~spl3_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f233])).
% 0.20/0.48  fof(f235,plain,(
% 0.20/0.48    ~spl3_6 | ~spl3_25 | spl3_29 | ~spl3_27),
% 0.20/0.48    inference(avatar_split_clause,[],[f229,f218,f233,f194,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl3_6 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    spl3_25 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_27),
% 0.20/0.48    inference(resolution,[],[f219,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(equality_resolution,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    ~spl3_28 | ~spl3_3 | spl3_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f223,f129,f58,f225])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl3_3 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    spl3_16 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_3 | spl3_16)),
% 0.20/0.48    inference(superposition,[],[f130,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f58])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f129])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    spl3_27 | ~spl3_2 | ~spl3_3 | ~spl3_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f221,f101,f58,f55,f218])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_2 | ~spl3_3 | ~spl3_12)),
% 0.20/0.48    inference(forward_demodulation,[],[f215,f59])).
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_2 | ~spl3_12)),
% 0.20/0.48    inference(superposition,[],[f102,f163])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f55])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f101])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    spl3_25 | ~spl3_2 | ~spl3_3 | ~spl3_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f192,f106,f58,f55,f194])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl3_13 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_13)),
% 0.20/0.48    inference(forward_demodulation,[],[f181,f163])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) | (~spl3_3 | ~spl3_13)),
% 0.20/0.48    inference(superposition,[],[f107,f59])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    ~spl3_12 | ~spl3_20),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f171])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    $false | (~spl3_12 | ~spl3_20)),
% 0.20/0.48    inference(subsumption_resolution,[],[f102,f167])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl3_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f166])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    spl3_20 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    spl3_16 | spl3_2 | ~spl3_13 | spl3_20 | ~spl3_4 | ~spl3_9 | ~spl3_10 | ~spl3_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f161,f138,f88,f84,f62,f166,f106,f55,f129])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    spl3_9 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl3_10 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    spl3_18 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relat_1(sK2)) ) | (~spl3_4 | ~spl3_9 | ~spl3_10 | ~spl3_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f160,f89])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f88])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_4 | ~spl3_9 | ~spl3_10 | ~spl3_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f159,f89])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_4 | ~spl3_9 | ~spl3_10 | ~spl3_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f158,f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f84])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_4 | ~spl3_9 | ~spl3_10 | ~spl3_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f157,f85])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    ( ! [X0] : (k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_4 | ~spl3_10 | ~spl3_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f155,f89])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ( ! [X0] : (u1_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_4 | ~spl3_18)),
% 0.20/0.48    inference(resolution,[],[f154,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f62])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0 | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) ) | ~spl3_18),
% 0.20/0.48    inference(resolution,[],[f139,f41])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v4_relat_1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0 | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1)) ) | ~spl3_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f138])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    spl3_19),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    $false | spl3_19),
% 0.20/0.48    inference(resolution,[],[f148,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f147])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    spl3_19 <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    ~spl3_19 | ~spl3_4 | ~spl3_9 | ~spl3_10 | spl3_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f145,f135,f88,f84,f62,f147])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_9 | ~spl3_10 | spl3_17)),
% 0.20/0.48    inference(forward_demodulation,[],[f144,f89])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_9 | spl3_17)),
% 0.20/0.48    inference(forward_demodulation,[],[f142,f85])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | (~spl3_4 | spl3_17)),
% 0.20/0.48    inference(resolution,[],[f141,f63])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_17),
% 0.20/0.48    inference(resolution,[],[f136,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl3_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f135])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ~spl3_17 | spl3_18 | ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f133,f70,f138,f135])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1 | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_6),
% 0.20/0.48    inference(resolution,[],[f132,f38])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_partfun1(sK2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | k1_xboole_0 = X0) ) | ~spl3_6),
% 0.20/0.48    inference(resolution,[],[f48,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl3_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f70])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ~spl3_15 | ~spl3_16 | spl3_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f124,f120,f129,f126])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl3_14 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | spl3_14),
% 0.20/0.48    inference(inner_rewriting,[],[f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_14),
% 0.20/0.48    inference(superposition,[],[f121,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f120])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ~spl3_12 | ~spl3_14 | spl3_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f117,f96,f120,f101])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl3_11 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_11),
% 0.20/0.48    inference(superposition,[],[f97,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f96])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl3_13 | ~spl3_5 | ~spl3_9 | ~spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f104,f88,f84,f66,f106])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9 | ~spl3_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f93,f89])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9)),
% 0.20/0.48    inference(superposition,[],[f67,f85])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f66])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl3_12 | ~spl3_4 | ~spl3_9 | ~spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f99,f88,f84,f62,f101])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f92,f89])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9)),
% 0.20/0.48    inference(superposition,[],[f63,f85])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~spl3_11 | spl3_1 | ~spl3_9 | ~spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f94,f88,f84,f51,f96])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl3_1 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_9 | ~spl3_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f91,f89])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_9)),
% 0.20/0.48    inference(superposition,[],[f52,f85])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl3_10 | ~spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f82,f78,f88])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl3_8 <=> l1_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.20/0.48    inference(resolution,[],[f35,f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    l1_struct_0(sK0) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f78])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl3_9 | ~spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f81,f74,f84])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl3_7 <=> l1_struct_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.20/0.48    inference(resolution,[],[f35,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    l1_struct_0(sK1) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f74])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f78])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    l1_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25,f24,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.49  % (9908)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (9899)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (9908)Refutation not found, incomplete strategy% (9908)------------------------------
% 0.20/0.49  % (9908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (9908)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (9908)Memory used [KB]: 6012
% 0.20/0.49  % (9908)Time elapsed: 0.003 s
% 0.20/0.49  % (9908)------------------------------
% 0.20/0.49  % (9908)------------------------------
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f74])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    l1_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f70])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f66])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f62])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ~spl3_2 | spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f58,f55])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f51])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (9902)------------------------------
% 0.20/0.49  % (9902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (9902)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (9902)Memory used [KB]: 10746
% 0.20/0.49  % (9902)Time elapsed: 0.058 s
% 0.20/0.49  % (9902)------------------------------
% 0.20/0.49  % (9902)------------------------------
% 0.20/0.50  % (9893)Success in time 0.137 s
%------------------------------------------------------------------------------
