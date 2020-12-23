%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t185_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:38 EDT 2019

% Result     : Theorem 6.25s
% Output     : Refutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 357 expanded)
%              Number of leaves         :   48 ( 169 expanded)
%              Depth                    :    9
%              Number of atoms          :  666 (1865 expanded)
%              Number of equality atoms :  133 ( 405 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63770,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f147,f154,f161,f182,f189,f196,f205,f220,f227,f268,f275,f319,f355,f362,f375,f382,f608,f653,f1467,f1469,f1524,f1912,f1913,f2067,f2381,f3613,f22769,f43959,f63769])).

fof(f63769,plain,
    ( ~ spl12_2
    | ~ spl12_16
    | ~ spl12_22
    | spl12_305
    | spl12_335
    | ~ spl12_4110 ),
    inference(avatar_contradiction_clause,[],[f63768])).

fof(f63768,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_16
    | ~ spl12_22
    | ~ spl12_305
    | ~ spl12_335
    | ~ spl12_4110 ),
    inference(subsumption_resolution,[],[f63767,f1905])).

fof(f1905,plain,
    ( k1_xboole_0 != sK2
    | ~ spl12_305 ),
    inference(avatar_component_clause,[],[f1904])).

fof(f1904,plain,
    ( spl12_305
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_305])])).

fof(f63767,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_2
    | ~ spl12_16
    | ~ spl12_22
    | ~ spl12_335
    | ~ spl12_4110 ),
    inference(subsumption_resolution,[],[f63766,f146])).

fof(f146,plain,
    ( v1_funct_1(sK3)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl12_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f63766,plain,
    ( ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | ~ spl12_16
    | ~ spl12_22
    | ~ spl12_335
    | ~ spl12_4110 ),
    inference(subsumption_resolution,[],[f63765,f2066])).

fof(f2066,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl12_335 ),
    inference(avatar_component_clause,[],[f2065])).

fof(f2065,plain,
    ( spl12_335
  <=> k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_335])])).

fof(f63765,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | ~ spl12_16
    | ~ spl12_22
    | ~ spl12_4110 ),
    inference(subsumption_resolution,[],[f63758,f219])).

fof(f219,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl12_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f63758,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | ~ spl12_16
    | ~ spl12_4110 ),
    inference(resolution,[],[f43958,f195])).

fof(f195,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl12_16
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f43958,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | k1_funct_1(k5_relat_1(X0,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0,sK5))
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X1 )
    | ~ spl12_4110 ),
    inference(avatar_component_clause,[],[f43957])).

fof(f43957,plain,
    ( spl12_4110
  <=> ! [X1,X0] :
        ( k1_funct_1(k5_relat_1(X0,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0,sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1)
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4110])])).

fof(f43959,plain,
    ( spl12_4110
    | ~ spl12_2130 ),
    inference(avatar_split_clause,[],[f22784,f21292,f43957])).

fof(f21292,plain,
    ( spl12_2130
  <=> ! [X89] :
        ( sP10(X89,sK1)
        | k1_funct_1(k5_relat_1(X89,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X89,sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2130])])).

fof(f22784,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k5_relat_1(X0,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0,sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1)
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X1 )
    | ~ spl12_2130 ),
    inference(resolution,[],[f21293,f130])).

fof(f130,plain,(
    ! [X0,X3,X1] :
      ( ~ sP10(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1 ) ),
    inference(general_splitting,[],[f128,f129_D])).

fof(f129,plain,(
    ! [X2,X0,X3] :
      ( ~ sP9(X3,X2)
      | ~ r2_hidden(X2,X0)
      | sP10(X3,X0) ) ),
    inference(cnf_transformation,[],[f129_D])).

fof(f129_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ sP9(X3,X2)
          | ~ r2_hidden(X2,X0) )
    <=> ~ sP10(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP9(X3,X2) ) ),
    inference(general_splitting,[],[f110,f127_D])).

fof(f127,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_funct_1(X4)
      | k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
      | ~ v1_relat_1(X4)
      | sP9(X3,X2) ) ),
    inference(cnf_transformation,[],[f127_D])).

fof(f127_D,plain,(
    ! [X2,X3] :
      ( ! [X4] :
          ( ~ v1_funct_1(X4)
          | k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
          | ~ v1_relat_1(X4) )
    <=> ~ sP9(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',t21_funct_2)).

fof(f21293,plain,
    ( ! [X89] :
        ( sP10(X89,sK1)
        | k1_funct_1(k5_relat_1(X89,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X89,sK5)) )
    | ~ spl12_2130 ),
    inference(avatar_component_clause,[],[f21292])).

fof(f22769,plain,
    ( spl12_2130
    | ~ spl12_12
    | spl12_175
    | ~ spl12_460 ),
    inference(avatar_split_clause,[],[f19636,f3611,f1171,f180,f21292])).

fof(f180,plain,
    ( spl12_12
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f1171,plain,
    ( spl12_175
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_175])])).

fof(f3611,plain,
    ( spl12_460
  <=> ! [X1,X0,X2] :
        ( k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1))
        | sP10(X0,X2)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_460])])).

fof(f19636,plain,
    ( ! [X241] :
        ( sP10(X241,sK1)
        | k1_funct_1(k5_relat_1(X241,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X241,sK5)) )
    | ~ spl12_12
    | ~ spl12_175
    | ~ spl12_460 ),
    inference(subsumption_resolution,[],[f19591,f1172])).

fof(f1172,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl12_175 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f19591,plain,
    ( ! [X241] :
        ( sP10(X241,sK1)
        | v1_xboole_0(sK1)
        | k1_funct_1(k5_relat_1(X241,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X241,sK5)) )
    | ~ spl12_12
    | ~ spl12_460 ),
    inference(resolution,[],[f3612,f181])).

fof(f181,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f3612,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,X2)
        | sP10(X0,X2)
        | v1_xboole_0(X2)
        | k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1)) )
    | ~ spl12_460 ),
    inference(avatar_component_clause,[],[f3611])).

fof(f3613,plain,
    ( spl12_460
    | ~ spl12_208 ),
    inference(avatar_split_clause,[],[f1488,f1398,f3611])).

fof(f1398,plain,
    ( spl12_208
  <=> ! [X1,X0,X2] :
        ( k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1))
        | ~ r2_hidden(X1,X2)
        | sP10(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_208])])).

fof(f1488,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1))
        | sP10(X0,X2)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X1,X2) )
    | ~ spl12_208 ),
    inference(resolution,[],[f1399,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',t2_subset)).

fof(f1399,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X2)
        | k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1))
        | sP10(X0,X2) )
    | ~ spl12_208 ),
    inference(avatar_component_clause,[],[f1398])).

fof(f2381,plain,
    ( spl12_15
    | ~ spl12_174 ),
    inference(avatar_contradiction_clause,[],[f2380])).

fof(f2380,plain,
    ( $false
    | ~ spl12_15
    | ~ spl12_174 ),
    inference(subsumption_resolution,[],[f2376,f188])).

fof(f188,plain,
    ( k1_xboole_0 != sK1
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl12_15
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f2376,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_174 ),
    inference(resolution,[],[f1175,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',t6_boole)).

fof(f1175,plain,
    ( v1_xboole_0(sK1)
    | ~ spl12_174 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f1174,plain,
    ( spl12_174
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_174])])).

fof(f2067,plain,
    ( ~ spl12_335
    | ~ spl12_4
    | ~ spl12_24
    | spl12_43
    | ~ spl12_50
    | ~ spl12_56
    | ~ spl12_246
    | ~ spl12_306 ),
    inference(avatar_split_clause,[],[f2053,f1910,f1522,f380,f353,f317,f225,f152,f2065])).

fof(f152,plain,
    ( spl12_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f225,plain,
    ( spl12_24
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f317,plain,
    ( spl12_43
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).

fof(f353,plain,
    ( spl12_50
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f380,plain,
    ( spl12_56
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).

fof(f1522,plain,
    ( spl12_246
  <=> k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_246])])).

fof(f1910,plain,
    ( spl12_306
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_306])])).

fof(f2053,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_43
    | ~ spl12_50
    | ~ spl12_56
    | ~ spl12_246
    | ~ spl12_306 ),
    inference(backward_demodulation,[],[f1921,f318])).

fof(f318,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)
    | ~ spl12_43 ),
    inference(avatar_component_clause,[],[f317])).

fof(f1921,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_50
    | ~ spl12_56
    | ~ spl12_246
    | ~ spl12_306 ),
    inference(forward_demodulation,[],[f1920,f1523])).

fof(f1523,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl12_246 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1920,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_50
    | ~ spl12_56
    | ~ spl12_306 ),
    inference(subsumption_resolution,[],[f1919,f226])).

fof(f226,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f1919,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl12_4
    | ~ spl12_50
    | ~ spl12_56
    | ~ spl12_306 ),
    inference(subsumption_resolution,[],[f1918,f153])).

fof(f153,plain,
    ( v1_funct_1(sK4)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1918,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl12_50
    | ~ spl12_56
    | ~ spl12_306 ),
    inference(subsumption_resolution,[],[f1914,f381])).

fof(f381,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl12_56 ),
    inference(avatar_component_clause,[],[f380])).

fof(f1914,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl12_50
    | ~ spl12_306 ),
    inference(superposition,[],[f1911,f354])).

fof(f354,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl12_50 ),
    inference(avatar_component_clause,[],[f353])).

fof(f1911,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) )
    | ~ spl12_306 ),
    inference(avatar_component_clause,[],[f1910])).

fof(f1913,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != o_0_0_xboole_0
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(theory_axiom,[])).

fof(f1912,plain,
    ( spl12_304
    | spl12_306
    | ~ spl12_2
    | ~ spl12_16
    | ~ spl12_22
    | ~ spl12_54 ),
    inference(avatar_split_clause,[],[f455,f373,f218,f194,f145,f1910,f1907])).

fof(f1907,plain,
    ( spl12_304
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_304])])).

fof(f373,plain,
    ( spl12_54
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).

fof(f455,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | k1_xboole_0 = sK2
        | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1) )
    | ~ spl12_2
    | ~ spl12_16
    | ~ spl12_22
    | ~ spl12_54 ),
    inference(subsumption_resolution,[],[f454,f146])).

fof(f454,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | k1_xboole_0 = sK2
        | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK3) )
    | ~ spl12_16
    | ~ spl12_22
    | ~ spl12_54 ),
    inference(subsumption_resolution,[],[f453,f195])).

fof(f453,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | k1_xboole_0 = sK2
        | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3) )
    | ~ spl12_22
    | ~ spl12_54 ),
    inference(subsumption_resolution,[],[f452,f219])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | k1_xboole_0 = sK2
        | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3) )
    | ~ spl12_54 ),
    inference(superposition,[],[f111,f374])).

fof(f374,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl12_54 ),
    inference(avatar_component_clause,[],[f373])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | k1_xboole_0 = X1
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',d12_funct_2)).

fof(f1524,plain,
    ( spl12_246
    | ~ spl12_24
    | ~ spl12_216 ),
    inference(avatar_split_clause,[],[f1509,f1420,f225,f1522])).

fof(f1420,plain,
    ( spl12_216
  <=> ! [X18,X17] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | k1_partfun1(sK1,sK2,X17,X18,sK3,sK4) = k5_relat_1(sK3,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_216])])).

fof(f1509,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl12_24
    | ~ spl12_216 ),
    inference(resolution,[],[f1421,f226])).

fof(f1421,plain,
    ( ! [X17,X18] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | k1_partfun1(sK1,sK2,X17,X18,sK3,sK4) = k5_relat_1(sK3,sK4) )
    | ~ spl12_216 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f1469,plain,
    ( spl12_216
    | ~ spl12_4
    | ~ spl12_100 ),
    inference(avatar_split_clause,[],[f1083,f651,f152,f1420])).

fof(f651,plain,
    ( spl12_100
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | k1_partfun1(sK1,sK2,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_100])])).

fof(f1083,plain,
    ( ! [X17,X18] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | k1_partfun1(sK1,sK2,X17,X18,sK3,sK4) = k5_relat_1(sK3,sK4) )
    | ~ spl12_4
    | ~ spl12_100 ),
    inference(resolution,[],[f652,f153])).

fof(f652,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_partfun1(sK1,sK2,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) )
    | ~ spl12_100 ),
    inference(avatar_component_clause,[],[f651])).

fof(f1467,plain,
    ( spl12_208
    | ~ spl12_98 ),
    inference(avatar_split_clause,[],[f1068,f606,f1398])).

fof(f606,plain,
    ( spl12_98
  <=> ! [X3,X2] :
        ( k1_funct_1(k5_relat_1(X2,sK4),X3) = k1_funct_1(sK4,k1_funct_1(X2,X3))
        | sP9(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_98])])).

fof(f1068,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1))
        | ~ r2_hidden(X1,X2)
        | sP10(X0,X2) )
    | ~ spl12_98 ),
    inference(resolution,[],[f607,f129])).

fof(f607,plain,
    ( ! [X2,X3] :
        ( sP9(X2,X3)
        | k1_funct_1(k5_relat_1(X2,sK4),X3) = k1_funct_1(sK4,k1_funct_1(X2,X3)) )
    | ~ spl12_98 ),
    inference(avatar_component_clause,[],[f606])).

fof(f653,plain,
    ( spl12_100
    | ~ spl12_2
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f397,f218,f145,f651])).

fof(f397,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | k1_partfun1(sK1,sK2,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) )
    | ~ spl12_2
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f394,f146])).

fof(f394,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | k1_partfun1(sK1,sK2,X1,X2,sK3,X0) = k5_relat_1(sK3,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl12_22 ),
    inference(resolution,[],[f119,f219])).

fof(f119,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',redefinition_k1_partfun1)).

fof(f608,plain,
    ( spl12_98
    | ~ spl12_4
    | ~ spl12_32 ),
    inference(avatar_split_clause,[],[f335,f266,f152,f606])).

fof(f266,plain,
    ( spl12_32
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f335,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(k5_relat_1(X2,sK4),X3) = k1_funct_1(sK4,k1_funct_1(X2,X3))
        | sP9(X2,X3) )
    | ~ spl12_4
    | ~ spl12_32 ),
    inference(subsumption_resolution,[],[f333,f267])).

fof(f267,plain,
    ( v1_relat_1(sK4)
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f266])).

fof(f333,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(k5_relat_1(X2,sK4),X3) = k1_funct_1(sK4,k1_funct_1(X2,X3))
        | ~ v1_relat_1(sK4)
        | sP9(X2,X3) )
    | ~ spl12_4 ),
    inference(resolution,[],[f127,f153])).

fof(f382,plain,
    ( spl12_56
    | ~ spl12_22
    | ~ spl12_52 ),
    inference(avatar_split_clause,[],[f368,f360,f218,f380])).

fof(f360,plain,
    ( spl12_52
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_52])])).

fof(f368,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl12_22
    | ~ spl12_52 ),
    inference(backward_demodulation,[],[f303,f361])).

fof(f361,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl12_52 ),
    inference(avatar_component_clause,[],[f360])).

fof(f303,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl12_22 ),
    inference(resolution,[],[f105,f219])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',redefinition_k2_relset_1)).

fof(f375,plain,
    ( spl12_54
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f303,f218,f373])).

fof(f362,plain,
    ( spl12_52
    | ~ spl12_24
    | ~ spl12_34 ),
    inference(avatar_split_clause,[],[f348,f273,f225,f360])).

fof(f273,plain,
    ( spl12_34
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_34])])).

fof(f348,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl12_24
    | ~ spl12_34 ),
    inference(backward_demodulation,[],[f294,f274])).

fof(f274,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl12_34 ),
    inference(avatar_component_clause,[],[f273])).

fof(f294,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl12_24 ),
    inference(resolution,[],[f104,f226])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',redefinition_k1_relset_1)).

fof(f355,plain,
    ( spl12_50
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f294,f225,f353])).

fof(f319,plain,(
    ~ spl12_43 ),
    inference(avatar_split_clause,[],[f91,f317])).

fof(f91,plain,(
    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f74,f73,f72,f71])).

fof(f71,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK3,X1,X2)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',t185_funct_2)).

fof(f275,plain,(
    spl12_34 ),
    inference(avatar_split_clause,[],[f89,f273])).

fof(f89,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f75])).

fof(f268,plain,
    ( spl12_32
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f252,f225,f266])).

fof(f252,plain,
    ( v1_relat_1(sK4)
    | ~ spl12_24 ),
    inference(resolution,[],[f103,f226])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',cc1_relset_1)).

fof(f227,plain,(
    spl12_24 ),
    inference(avatar_split_clause,[],[f87,f225])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f75])).

fof(f220,plain,(
    spl12_22 ),
    inference(avatar_split_clause,[],[f85,f218])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f75])).

fof(f205,plain,
    ( spl12_18
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f197,f159,f203])).

fof(f203,plain,
    ( spl12_18
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f159,plain,
    ( spl12_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f197,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl12_6 ),
    inference(resolution,[],[f93,f160])).

fof(f160,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f196,plain,(
    spl12_16 ),
    inference(avatar_split_clause,[],[f84,f194])).

fof(f84,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f189,plain,(
    ~ spl12_15 ),
    inference(avatar_split_clause,[],[f90,f187])).

fof(f90,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f75])).

fof(f182,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f88,f180])).

fof(f88,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f161,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f92,f159])).

fof(f92,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t185_funct_2.p',dt_o_0_0_xboole_0)).

fof(f154,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f86,f152])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

fof(f147,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f83,f145])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

fof(f140,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f82,f138])).

fof(f138,plain,
    ( spl12_1
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f82,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f75])).
%------------------------------------------------------------------------------
