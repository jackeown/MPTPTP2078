%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 413 expanded)
%              Number of leaves         :   55 ( 186 expanded)
%              Depth                    :   10
%              Number of atoms          :  679 (1353 expanded)
%              Number of equality atoms :  143 ( 307 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f506,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f98,f102,f108,f112,f116,f125,f129,f157,f161,f171,f181,f190,f197,f204,f210,f231,f243,f244,f288,f319,f323,f329,f333,f361,f370,f410,f411,f439,f475,f503,f504,f505])).

fof(f505,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k4_relat_1(sK2) != k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k4_relat_1(sK2)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f504,plain,
    ( k4_relat_1(sK2) != k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k4_relat_1(sK2)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

% (11924)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f503,plain,
    ( spl3_69
    | ~ spl3_24
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f494,f473,f208,f501])).

fof(f501,plain,
    ( spl3_69
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f208,plain,
    ( spl3_24
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f473,plain,
    ( spl3_67
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f494,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_24
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f482,f209])).

fof(f209,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f482,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_67 ),
    inference(resolution,[],[f474,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f474,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f473])).

fof(f475,plain,
    ( spl3_67
    | ~ spl3_47
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f441,f413,f327,f473])).

fof(f327,plain,
    ( spl3_47
  <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f413,plain,
    ( spl3_56
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f441,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_47
    | ~ spl3_56 ),
    inference(superposition,[],[f328,f414])).

fof(f414,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f413])).

fof(f328,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f327])).

fof(f439,plain,
    ( spl3_56
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_32
    | ~ spl3_45
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f388,f331,f317,f246,f72,f68,f413])).

fof(f68,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f72,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f246,plain,
    ( spl3_32
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f317,plain,
    ( spl3_45
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f331,plain,
    ( spl3_48
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f388,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_32
    | ~ spl3_45
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f387,f73])).

fof(f73,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f387,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_32
    | ~ spl3_45
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f386,f247])).

fof(f247,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f246])).

fof(f386,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_45
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f385,f69])).

fof(f69,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f385,plain,
    ( ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_45
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f373,f318])).

fof(f318,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f317])).

fof(f373,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_48 ),
    inference(resolution,[],[f332,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f332,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f331])).

fof(f411,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f410,plain,
    ( spl3_55
    | ~ spl3_15
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f143,f127,f110,f72,f68,f163,f407])).

fof(f407,plain,
    ( spl3_55
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f163,plain,
    ( spl3_15
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f110,plain,
    ( spl3_9
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f127,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f143,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f142,f73])).

fof(f142,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f141,f69])).

fof(f141,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f132,f111])).

fof(f111,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f132,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f50])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f370,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f361,plain,
    ( spl3_50
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f130,f127,f359])).

fof(f359,plain,
    ( spl3_50
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f130,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f333,plain,
    ( spl3_48
    | ~ spl3_13
    | ~ spl3_16
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f263,f241,f169,f127,f331])).

fof(f169,plain,
    ( spl3_16
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f241,plain,
    ( spl3_31
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f263,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_16
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f256,f170])).

fof(f170,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f256,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(superposition,[],[f128,f242])).

fof(f242,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f241])).

fof(f329,plain,
    ( spl3_47
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f325,f321,f241,f169,f327])).

fof(f321,plain,
    ( spl3_46
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f325,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f324,f170])).

fof(f324,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ spl3_31
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f322,f242])).

fof(f322,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f321])).

fof(f323,plain,
    ( spl3_46
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f149,f127,f110,f68,f321])).

fof(f149,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f148,f69])).

fof(f148,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f135,f111])).

fof(f135,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f319,plain,
    ( spl3_45
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f262,f241,f169,f110,f317])).

fof(f262,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f255,f170])).

fof(f255,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(superposition,[],[f111,f242])).

fof(f288,plain,
    ( spl3_39
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f138,f127,f286])).

fof(f286,plain,
    ( spl3_39
  <=> k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f138,plain,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f244,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f243,plain,
    ( spl3_31
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f234,f226,f179,f123,f241])).

fof(f123,plain,
    ( spl3_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f179,plain,
    ( spl3_19
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f226,plain,
    ( spl3_28
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f234,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f233,f156])).

fof(f156,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f233,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f232,f180])).

fof(f180,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f232,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_28 ),
    inference(resolution,[],[f227,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f227,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f226])).

fof(f231,plain,
    ( spl3_28
    | spl3_29
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f151,f127,f110,f68,f229,f226])).

fof(f229,plain,
    ( spl3_29
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f151,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f150,f111])).

fof(f150,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f137,f69])).

fof(f137,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f210,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f154,f127,f72,f68,f208])).

fof(f154,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f92,f139])).

fof(f139,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f89,f69])).

fof(f89,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f73,f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f204,plain,
    ( ~ spl3_23
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_21 ),
    inference(avatar_split_clause,[],[f200,f192,f169,f106,f96,f202])).

fof(f202,plain,
    ( spl3_23
  <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f96,plain,
    ( spl3_6
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f106,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f192,plain,
    ( spl3_21
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f200,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_21 ),
    inference(forward_demodulation,[],[f199,f107])).

fof(f107,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f199,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_6
    | ~ spl3_16
    | spl3_21 ),
    inference(forward_demodulation,[],[f198,f170])).

fof(f198,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_6
    | spl3_21 ),
    inference(forward_demodulation,[],[f193,f97])).

fof(f97,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f193,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f192])).

fof(f197,plain,
    ( ~ spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f39,f195,f192])).

fof(f195,plain,
    ( spl3_22
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

% (11926)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f39,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f190,plain,
    ( ~ spl3_20
    | spl3_3
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f186,f169,f80,f76,f188])).

fof(f188,plain,
    ( spl3_20
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f76,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f186,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f185,f77])).

fof(f77,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f185,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f184,f81])).

fof(f81,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f184,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_16 ),
    inference(superposition,[],[f57,f170])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f181,plain,
    ( spl3_19
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f140,f127,f179])).

fof(f140,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f171,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f167,f159,f127,f106,f96,f169])).

fof(f159,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f167,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f166,f136])).

fof(f136,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f59])).

fof(f166,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f165,f107])).

fof(f165,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f160,f97])).

fof(f160,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f43,f159])).

fof(f43,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f157,plain,
    ( spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f139,f127,f123])).

fof(f129,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f118,f114,f106,f96,f127])).

fof(f114,plain,
    ( spl3_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f117,f107])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f115,f97])).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f125,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f90,f72,f68,f123,f120])).

fof(f120,plain,
    ( spl3_11
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f87,f69])).

fof(f87,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f116,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f42,f114])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f104,f100,f96,f84,f110])).

fof(f84,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,
    ( spl3_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f104,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f103,f94])).

fof(f94,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f85,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f103,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f101,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f108,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f94,f84,f106])).

fof(f102,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f41,f100])).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f93,f80,f96])).

fof(f93,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f81,f58])).

fof(f86,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f47,f84])).

fof(f47,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f76])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f44,f72])).

fof(f44,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f40,f68])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n009.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:45:11 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.44  % (11928)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.45  % (11941)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (11920)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.45  % (11941)Refutation not found, incomplete strategy% (11941)------------------------------
% 0.19/0.45  % (11941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (11927)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.46  % (11941)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (11941)Memory used [KB]: 10618
% 0.19/0.46  % (11941)Time elapsed: 0.005 s
% 0.19/0.46  % (11941)------------------------------
% 0.19/0.46  % (11941)------------------------------
% 0.19/0.47  % (11934)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % (11930)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.47  % (11925)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.47  % (11931)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.47  % (11920)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f506,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f98,f102,f108,f112,f116,f125,f129,f157,f161,f171,f181,f190,f197,f204,f210,f231,f243,f244,f288,f319,f323,f329,f333,f361,f370,f410,f411,f439,f475,f503,f504,f505])).
% 0.19/0.47  fof(f505,plain,(
% 0.19/0.47    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k4_relat_1(sK2) != k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) != k4_relat_1(sK2) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  fof(f504,plain,(
% 0.19/0.47    k4_relat_1(sK2) != k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) != k4_relat_1(sK2) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relat_1(sK2) | k2_struct_0(sK0) != k1_relat_1(sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  % (11924)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.47  fof(f503,plain,(
% 0.19/0.47    spl3_69 | ~spl3_24 | ~spl3_67),
% 0.19/0.47    inference(avatar_split_clause,[],[f494,f473,f208,f501])).
% 0.19/0.47  fof(f501,plain,(
% 0.19/0.47    spl3_69 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.19/0.47  fof(f208,plain,(
% 0.19/0.47    spl3_24 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.19/0.47  fof(f473,plain,(
% 0.19/0.47    spl3_67 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.19/0.47  fof(f494,plain,(
% 0.19/0.47    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_24 | ~spl3_67)),
% 0.19/0.47    inference(forward_demodulation,[],[f482,f209])).
% 0.19/0.47  fof(f209,plain,(
% 0.19/0.47    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 0.19/0.47    inference(avatar_component_clause,[],[f208])).
% 0.19/0.47  fof(f482,plain,(
% 0.19/0.47    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_67),
% 0.19/0.47    inference(resolution,[],[f474,f59])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.47  fof(f474,plain,(
% 0.19/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_67),
% 0.19/0.47    inference(avatar_component_clause,[],[f473])).
% 0.19/0.47  fof(f475,plain,(
% 0.19/0.47    spl3_67 | ~spl3_47 | ~spl3_56),
% 0.19/0.47    inference(avatar_split_clause,[],[f441,f413,f327,f473])).
% 0.19/0.47  fof(f327,plain,(
% 0.19/0.47    spl3_47 <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.19/0.47  fof(f413,plain,(
% 0.19/0.47    spl3_56 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.19/0.47  fof(f441,plain,(
% 0.19/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_47 | ~spl3_56)),
% 0.19/0.47    inference(superposition,[],[f328,f414])).
% 0.19/0.47  fof(f414,plain,(
% 0.19/0.47    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_56),
% 0.19/0.47    inference(avatar_component_clause,[],[f413])).
% 0.19/0.47  fof(f328,plain,(
% 0.19/0.47    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_47),
% 0.19/0.47    inference(avatar_component_clause,[],[f327])).
% 0.19/0.47  fof(f439,plain,(
% 0.19/0.47    spl3_56 | ~spl3_1 | ~spl3_2 | ~spl3_32 | ~spl3_45 | ~spl3_48),
% 0.19/0.47    inference(avatar_split_clause,[],[f388,f331,f317,f246,f72,f68,f413])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    spl3_1 <=> v1_funct_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    spl3_2 <=> v2_funct_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.47  fof(f246,plain,(
% 0.19/0.47    spl3_32 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.19/0.47  fof(f317,plain,(
% 0.19/0.47    spl3_45 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.19/0.47  fof(f331,plain,(
% 0.19/0.47    spl3_48 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.19/0.47  fof(f388,plain,(
% 0.19/0.47    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_32 | ~spl3_45 | ~spl3_48)),
% 0.19/0.47    inference(subsumption_resolution,[],[f387,f73])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    v2_funct_1(sK2) | ~spl3_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f72])).
% 0.19/0.47  fof(f387,plain,(
% 0.19/0.47    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_32 | ~spl3_45 | ~spl3_48)),
% 0.19/0.47    inference(subsumption_resolution,[],[f386,f247])).
% 0.19/0.47  fof(f247,plain,(
% 0.19/0.47    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_32),
% 0.19/0.47    inference(avatar_component_clause,[],[f246])).
% 0.19/0.47  fof(f386,plain,(
% 0.19/0.47    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_45 | ~spl3_48)),
% 0.19/0.47    inference(subsumption_resolution,[],[f385,f69])).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    v1_funct_1(sK2) | ~spl3_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f68])).
% 0.19/0.47  fof(f385,plain,(
% 0.19/0.47    ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_45 | ~spl3_48)),
% 0.19/0.47    inference(subsumption_resolution,[],[f373,f318])).
% 0.19/0.47  fof(f318,plain,(
% 0.19/0.47    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_45),
% 0.19/0.47    inference(avatar_component_clause,[],[f317])).
% 0.19/0.47  fof(f373,plain,(
% 0.19/0.47    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_48),
% 0.19/0.47    inference(resolution,[],[f332,f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.47    inference(flattening,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.19/0.47  fof(f332,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_48),
% 0.19/0.47    inference(avatar_component_clause,[],[f331])).
% 0.19/0.47  fof(f411,plain,(
% 0.19/0.47    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  fof(f410,plain,(
% 0.19/0.47    spl3_55 | ~spl3_15 | ~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f143,f127,f110,f72,f68,f163,f407])).
% 0.19/0.47  fof(f407,plain,(
% 0.19/0.47    spl3_55 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.19/0.47  fof(f163,plain,(
% 0.19/0.47    spl3_15 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.47  fof(f110,plain,(
% 0.19/0.47    spl3_9 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.47  fof(f143,plain,(
% 0.19/0.47    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f142,f73])).
% 0.19/0.47  fof(f142,plain,(
% 0.19/0.47    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_9 | ~spl3_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f141,f69])).
% 0.19/0.47  fof(f141,plain,(
% 0.19/0.47    ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_9 | ~spl3_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f132,f111])).
% 0.19/0.47  fof(f111,plain,(
% 0.19/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_9),
% 0.19/0.47    inference(avatar_component_clause,[],[f110])).
% 0.19/0.47  fof(f132,plain,(
% 0.19/0.47    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.19/0.47    inference(resolution,[],[f128,f50])).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.19/0.47    inference(avatar_component_clause,[],[f127])).
% 0.19/0.47  fof(f370,plain,(
% 0.19/0.47    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK1) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  fof(f361,plain,(
% 0.19/0.47    spl3_50 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f130,f127,f359])).
% 0.19/0.47  fof(f359,plain,(
% 0.19/0.47    spl3_50 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.19/0.47  fof(f130,plain,(
% 0.19/0.47    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~spl3_13),
% 0.19/0.47    inference(resolution,[],[f128,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).
% 0.19/0.47  fof(f333,plain,(
% 0.19/0.47    spl3_48 | ~spl3_13 | ~spl3_16 | ~spl3_31),
% 0.19/0.47    inference(avatar_split_clause,[],[f263,f241,f169,f127,f331])).
% 0.19/0.47  fof(f169,plain,(
% 0.19/0.47    spl3_16 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.47  fof(f241,plain,(
% 0.19/0.47    spl3_31 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.19/0.47  fof(f263,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_16 | ~spl3_31)),
% 0.19/0.47    inference(forward_demodulation,[],[f256,f170])).
% 0.19/0.47  fof(f170,plain,(
% 0.19/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_16),
% 0.19/0.47    inference(avatar_component_clause,[],[f169])).
% 0.19/0.47  fof(f256,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | (~spl3_13 | ~spl3_31)),
% 0.19/0.47    inference(superposition,[],[f128,f242])).
% 0.19/0.47  fof(f242,plain,(
% 0.19/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_31),
% 0.19/0.47    inference(avatar_component_clause,[],[f241])).
% 0.19/0.47  fof(f329,plain,(
% 0.19/0.47    spl3_47 | ~spl3_16 | ~spl3_31 | ~spl3_46),
% 0.19/0.47    inference(avatar_split_clause,[],[f325,f321,f241,f169,f327])).
% 0.19/0.47  fof(f321,plain,(
% 0.19/0.47    spl3_46 <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.19/0.47  fof(f325,plain,(
% 0.19/0.47    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_16 | ~spl3_31 | ~spl3_46)),
% 0.19/0.47    inference(forward_demodulation,[],[f324,f170])).
% 0.19/0.47  fof(f324,plain,(
% 0.19/0.47    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | (~spl3_31 | ~spl3_46)),
% 0.19/0.47    inference(forward_demodulation,[],[f322,f242])).
% 0.19/0.47  fof(f322,plain,(
% 0.19/0.47    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_46),
% 0.19/0.47    inference(avatar_component_clause,[],[f321])).
% 0.19/0.47  fof(f323,plain,(
% 0.19/0.47    spl3_46 | ~spl3_1 | ~spl3_9 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f149,f127,f110,f68,f321])).
% 0.19/0.47  fof(f149,plain,(
% 0.19/0.47    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_9 | ~spl3_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f148,f69])).
% 0.19/0.47  fof(f148,plain,(
% 0.19/0.47    ~v1_funct_1(sK2) | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_9 | ~spl3_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f135,f111])).
% 0.19/0.47  fof(f135,plain,(
% 0.19/0.47    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_13),
% 0.19/0.47    inference(resolution,[],[f128,f53])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.47    inference(flattening,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.19/0.47  fof(f319,plain,(
% 0.19/0.47    spl3_45 | ~spl3_9 | ~spl3_16 | ~spl3_31),
% 0.19/0.47    inference(avatar_split_clause,[],[f262,f241,f169,f110,f317])).
% 0.19/0.47  fof(f262,plain,(
% 0.19/0.47    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_9 | ~spl3_16 | ~spl3_31)),
% 0.19/0.47    inference(forward_demodulation,[],[f255,f170])).
% 0.19/0.47  fof(f255,plain,(
% 0.19/0.47    v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | (~spl3_9 | ~spl3_31)),
% 0.19/0.47    inference(superposition,[],[f111,f242])).
% 0.19/0.47  fof(f288,plain,(
% 0.19/0.47    spl3_39 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f138,f127,f286])).
% 0.19/0.47  fof(f286,plain,(
% 0.19/0.47    spl3_39 <=> k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.19/0.47  fof(f138,plain,(
% 0.19/0.47    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.19/0.47    inference(resolution,[],[f128,f61])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.19/0.47  fof(f244,plain,(
% 0.19/0.47    k2_struct_0(sK1) != k2_relat_1(sK2) | v1_xboole_0(k2_relat_1(sK2)) | ~v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  fof(f243,plain,(
% 0.19/0.47    spl3_31 | ~spl3_12 | ~spl3_19 | ~spl3_28),
% 0.19/0.47    inference(avatar_split_clause,[],[f234,f226,f179,f123,f241])).
% 0.19/0.47  fof(f123,plain,(
% 0.19/0.47    spl3_12 <=> v1_relat_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.47  fof(f179,plain,(
% 0.19/0.47    spl3_19 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.19/0.47  fof(f226,plain,(
% 0.19/0.47    spl3_28 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.19/0.47  fof(f234,plain,(
% 0.19/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_12 | ~spl3_19 | ~spl3_28)),
% 0.19/0.47    inference(subsumption_resolution,[],[f233,f156])).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    v1_relat_1(sK2) | ~spl3_12),
% 0.19/0.47    inference(avatar_component_clause,[],[f123])).
% 0.19/0.47  fof(f233,plain,(
% 0.19/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_19 | ~spl3_28)),
% 0.19/0.47    inference(subsumption_resolution,[],[f232,f180])).
% 0.19/0.47  fof(f180,plain,(
% 0.19/0.47    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_19),
% 0.19/0.47    inference(avatar_component_clause,[],[f179])).
% 0.19/0.47  fof(f232,plain,(
% 0.19/0.47    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_28),
% 0.19/0.47    inference(resolution,[],[f227,f63])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f36])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.19/0.47  fof(f227,plain,(
% 0.19/0.47    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_28),
% 0.19/0.47    inference(avatar_component_clause,[],[f226])).
% 0.19/0.47  fof(f231,plain,(
% 0.19/0.47    spl3_28 | spl3_29 | ~spl3_1 | ~spl3_9 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f151,f127,f110,f68,f229,f226])).
% 0.19/0.47  fof(f229,plain,(
% 0.19/0.47    spl3_29 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.19/0.47  fof(f151,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_9 | ~spl3_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f150,f111])).
% 0.19/0.47  fof(f150,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f137,f69])).
% 0.19/0.47  fof(f137,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.19/0.47    inference(resolution,[],[f128,f60])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.47    inference(flattening,[],[f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.47  fof(f210,plain,(
% 0.19/0.47    spl3_24 | ~spl3_1 | ~spl3_2 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f154,f127,f72,f68,f208])).
% 0.19/0.47  fof(f154,plain,(
% 0.19/0.47    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f92,f139])).
% 0.19/0.47  fof(f139,plain,(
% 0.19/0.47    v1_relat_1(sK2) | ~spl3_13),
% 0.19/0.47    inference(resolution,[],[f128,f64])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f37])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f89,f69])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.19/0.47    inference(resolution,[],[f73,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(flattening,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.19/0.47  fof(f204,plain,(
% 0.19/0.47    ~spl3_23 | ~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_21),
% 0.19/0.47    inference(avatar_split_clause,[],[f200,f192,f169,f106,f96,f202])).
% 0.19/0.47  fof(f202,plain,(
% 0.19/0.47    spl3_23 <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.19/0.47  fof(f96,plain,(
% 0.19/0.47    spl3_6 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.47  fof(f106,plain,(
% 0.19/0.47    spl3_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.47  fof(f192,plain,(
% 0.19/0.47    spl3_21 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.19/0.47  fof(f200,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_21)),
% 0.19/0.47    inference(forward_demodulation,[],[f199,f107])).
% 0.19/0.47  fof(f107,plain,(
% 0.19/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.19/0.47    inference(avatar_component_clause,[],[f106])).
% 0.19/0.47  fof(f199,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_6 | ~spl3_16 | spl3_21)),
% 0.19/0.47    inference(forward_demodulation,[],[f198,f170])).
% 0.19/0.47  fof(f198,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_6 | spl3_21)),
% 0.19/0.47    inference(forward_demodulation,[],[f193,f97])).
% 0.19/0.47  fof(f97,plain,(
% 0.19/0.47    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_6),
% 0.19/0.47    inference(avatar_component_clause,[],[f96])).
% 0.19/0.47  fof(f193,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_21),
% 0.19/0.47    inference(avatar_component_clause,[],[f192])).
% 0.19/0.47  fof(f197,plain,(
% 0.19/0.47    ~spl3_21 | ~spl3_22),
% 0.19/0.47    inference(avatar_split_clause,[],[f39,f195,f192])).
% 0.19/0.47  fof(f195,plain,(
% 0.19/0.47    spl3_22 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.19/0.47  % (11926)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,negated_conjecture,(
% 0.19/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.19/0.47    inference(negated_conjecture,[],[f14])).
% 0.19/0.47  fof(f14,conjecture,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.19/0.47  fof(f190,plain,(
% 0.19/0.47    ~spl3_20 | spl3_3 | ~spl3_4 | ~spl3_16),
% 0.19/0.47    inference(avatar_split_clause,[],[f186,f169,f80,f76,f188])).
% 0.19/0.47  fof(f188,plain,(
% 0.19/0.47    spl3_20 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    spl3_3 <=> v2_struct_0(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    spl3_4 <=> l1_struct_0(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.47  fof(f186,plain,(
% 0.19/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_3 | ~spl3_4 | ~spl3_16)),
% 0.19/0.47    inference(subsumption_resolution,[],[f185,f77])).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    ~v2_struct_0(sK1) | spl3_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f76])).
% 0.19/0.47  fof(f185,plain,(
% 0.19/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_16)),
% 0.19/0.47    inference(subsumption_resolution,[],[f184,f81])).
% 0.19/0.47  fof(f81,plain,(
% 0.19/0.47    l1_struct_0(sK1) | ~spl3_4),
% 0.19/0.47    inference(avatar_component_clause,[],[f80])).
% 0.19/0.47  fof(f184,plain,(
% 0.19/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_16),
% 0.19/0.47    inference(superposition,[],[f57,f170])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.19/0.47  fof(f181,plain,(
% 0.19/0.47    spl3_19 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f140,f127,f179])).
% 0.19/0.47  fof(f140,plain,(
% 0.19/0.47    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.19/0.47    inference(resolution,[],[f128,f65])).
% 0.19/0.47  fof(f65,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f38])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.47  fof(f171,plain,(
% 0.19/0.47    spl3_16 | ~spl3_6 | ~spl3_8 | ~spl3_13 | ~spl3_14),
% 0.19/0.47    inference(avatar_split_clause,[],[f167,f159,f127,f106,f96,f169])).
% 0.19/0.47  fof(f159,plain,(
% 0.19/0.47    spl3_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.19/0.47  fof(f167,plain,(
% 0.19/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_6 | ~spl3_8 | ~spl3_13 | ~spl3_14)),
% 0.19/0.47    inference(forward_demodulation,[],[f166,f136])).
% 0.19/0.47  fof(f136,plain,(
% 0.19/0.47    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.19/0.47    inference(resolution,[],[f128,f59])).
% 0.19/0.47  fof(f166,plain,(
% 0.19/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_6 | ~spl3_8 | ~spl3_14)),
% 0.19/0.47    inference(forward_demodulation,[],[f165,f107])).
% 0.19/0.47  fof(f165,plain,(
% 0.19/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_6 | ~spl3_14)),
% 0.19/0.47    inference(forward_demodulation,[],[f160,f97])).
% 0.19/0.47  fof(f160,plain,(
% 0.19/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_14),
% 0.19/0.47    inference(avatar_component_clause,[],[f159])).
% 0.19/0.47  fof(f161,plain,(
% 0.19/0.47    spl3_14),
% 0.19/0.47    inference(avatar_split_clause,[],[f43,f159])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f157,plain,(
% 0.19/0.47    spl3_12 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f139,f127,f123])).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    spl3_13 | ~spl3_6 | ~spl3_8 | ~spl3_10),
% 0.19/0.47    inference(avatar_split_clause,[],[f118,f114,f106,f96,f127])).
% 0.19/0.47  fof(f114,plain,(
% 0.19/0.47    spl3_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.47  fof(f118,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_6 | ~spl3_8 | ~spl3_10)),
% 0.19/0.47    inference(forward_demodulation,[],[f117,f107])).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_6 | ~spl3_10)),
% 0.19/0.47    inference(forward_demodulation,[],[f115,f97])).
% 0.19/0.47  fof(f115,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_10),
% 0.19/0.47    inference(avatar_component_clause,[],[f114])).
% 0.19/0.47  fof(f125,plain,(
% 0.19/0.47    spl3_11 | ~spl3_12 | ~spl3_1 | ~spl3_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f90,f72,f68,f123,f120])).
% 0.19/0.47  fof(f120,plain,(
% 0.19/0.47    spl3_11 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl3_1 | ~spl3_2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f87,f69])).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_2),
% 0.19/0.47    inference(resolution,[],[f73,f56])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = k4_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(flattening,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    spl3_10),
% 0.19/0.47    inference(avatar_split_clause,[],[f42,f114])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f112,plain,(
% 0.19/0.47    spl3_9 | ~spl3_5 | ~spl3_6 | ~spl3_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f104,f100,f96,f84,f110])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    spl3_5 <=> l1_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.47  fof(f100,plain,(
% 0.19/0.47    spl3_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.47  fof(f104,plain,(
% 0.19/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_6 | ~spl3_7)),
% 0.19/0.47    inference(forward_demodulation,[],[f103,f94])).
% 0.19/0.47  fof(f94,plain,(
% 0.19/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.19/0.47    inference(resolution,[],[f85,f58])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,axiom,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    l1_struct_0(sK0) | ~spl3_5),
% 0.19/0.47    inference(avatar_component_clause,[],[f84])).
% 0.19/0.47  fof(f103,plain,(
% 0.19/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_7)),
% 0.19/0.47    inference(forward_demodulation,[],[f101,f97])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_7),
% 0.19/0.47    inference(avatar_component_clause,[],[f100])).
% 0.19/0.47  fof(f108,plain,(
% 0.19/0.47    spl3_8 | ~spl3_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f94,f84,f106])).
% 0.19/0.47  fof(f102,plain,(
% 0.19/0.47    spl3_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f41,f100])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f98,plain,(
% 0.19/0.47    spl3_6 | ~spl3_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f93,f80,f96])).
% 0.19/0.47  fof(f93,plain,(
% 0.19/0.47    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.19/0.47    inference(resolution,[],[f81,f58])).
% 0.19/0.47  fof(f86,plain,(
% 0.19/0.47    spl3_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f47,f84])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    l1_struct_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    spl3_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f46,f80])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    l1_struct_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    ~spl3_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f45,f76])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ~v2_struct_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    spl3_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f44,f72])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    v2_funct_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    spl3_1),
% 0.19/0.47    inference(avatar_split_clause,[],[f40,f68])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    v1_funct_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (11920)------------------------------
% 0.19/0.47  % (11920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (11920)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (11920)Memory used [KB]: 6524
% 0.19/0.47  % (11920)Time elapsed: 0.077 s
% 0.19/0.47  % (11920)------------------------------
% 0.19/0.47  % (11920)------------------------------
% 0.19/0.47  % (11936)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.47  % (11919)Success in time 0.132 s
%------------------------------------------------------------------------------
