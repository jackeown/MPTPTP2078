%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 422 expanded)
%              Number of leaves         :   36 ( 152 expanded)
%              Depth                    :   12
%              Number of atoms          :  644 (1542 expanded)
%              Number of equality atoms :  141 ( 361 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f135,f140,f145,f175,f190,f199,f263,f268,f284,f304,f528,f849,f859,f865,f866,f867,f970,f1045,f1071,f1072,f1208,f1218])).

fof(f1218,plain,
    ( ~ spl4_9
    | spl4_11
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_32
    | ~ spl4_37
    | ~ spl4_51 ),
    inference(avatar_contradiction_clause,[],[f1217])).

fof(f1217,plain,
    ( $false
    | ~ spl4_9
    | spl4_11
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_32
    | ~ spl4_37
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f1075,f1206])).

fof(f1206,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_37
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f1205,f106])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

% (2108)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1205,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0))))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_37
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f1189,f995])).

fof(f995,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f993])).

fof(f993,plain,
    ( spl4_51
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f1189,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f1188,f763])).

fof(f763,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f761])).

fof(f761,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1188,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1187,f262])).

fof(f262,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl4_14
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1187,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1177,f180])).

fof(f180,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_9
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1177,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_37 ),
    inference(superposition,[],[f76,f858])).

fof(f858,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f856])).

fof(f856,plain,
    ( spl4_37
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1075,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_11
    | ~ spl4_17
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1074,f763])).

fof(f1074,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_11
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f1073,f106])).

fof(f1073,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_11
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f189,f299])).

fof(f299,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl4_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f189,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_11
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1208,plain,
    ( ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_37
    | ~ spl4_51
    | spl4_60 ),
    inference(avatar_contradiction_clause,[],[f1207])).

fof(f1207,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_37
    | ~ spl4_51
    | spl4_60 ),
    inference(subsumption_resolution,[],[f1206,f1038])).

fof(f1038,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_60 ),
    inference(avatar_component_clause,[],[f1037])).

fof(f1037,plain,
    ( spl4_60
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f1072,plain,
    ( k1_xboole_0 != sK2
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | sK1 != k2_relat_1(sK2)
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1071,plain,
    ( ~ spl4_51
    | ~ spl4_60
    | spl4_61 ),
    inference(avatar_contradiction_clause,[],[f1070])).

fof(f1070,plain,
    ( $false
    | ~ spl4_51
    | ~ spl4_60
    | spl4_61 ),
    inference(subsumption_resolution,[],[f1069,f1063])).

fof(f1063,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0))
    | ~ spl4_51
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f1049,f995])).

fof(f1049,plain,
    ( ! [X0] : k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0))
    | ~ spl4_60 ),
    inference(unit_resulting_resolution,[],[f1039,f231])).

fof(f231,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f95,f106])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1039,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f1037])).

fof(f1069,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | ~ spl4_60
    | spl4_61 ),
    inference(unit_resulting_resolution,[],[f1039,f1044,f114])).

fof(f114,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f110,f106])).

fof(f110,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1044,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_61 ),
    inference(avatar_component_clause,[],[f1042])).

fof(f1042,plain,
    ( spl4_61
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f1045,plain,
    ( ~ spl4_61
    | spl4_10
    | ~ spl4_17
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f1035,f761,f297,f183,f1042])).

fof(f183,plain,
    ( spl4_10
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1035,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_10
    | ~ spl4_17
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1034,f763])).

fof(f1034,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_10
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f185,f299])).

fof(f185,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f183])).

fof(f970,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f969])).

fof(f969,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f968,f189])).

fof(f968,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f967,f563])).

fof(f563,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f532,f562])).

fof(f562,plain,
    ( sK1 = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f561,f267])).

fof(f267,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f265])).

% (2096)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f265,plain,
    ( spl4_15
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f561,plain,
    ( k2_relat_1(sK2) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f535,f221])).

fof(f221,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f174,f119,f124,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f124,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f119,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f174,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f535,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f496,f223])).

fof(f223,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f174,f119,f124,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f496,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f532,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f484,f223])).

fof(f484,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f262,f70])).

fof(f967,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f966,f262])).

fof(f966,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_9
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f960,f180])).

fof(f960,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_38 ),
    inference(superposition,[],[f76,f863])).

fof(f863,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f861])).

fof(f861,plain,
    ( spl4_38
  <=> sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f867,plain,
    ( spl4_32
    | ~ spl4_17
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f279,f265,f172,f297,f761])).

fof(f279,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f272,f174])).

% (2109)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f272,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(superposition,[],[f73,f267])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f866,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f865,plain,
    ( spl4_38
    | ~ spl4_22
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f864,f856,f332,f861])).

fof(f332,plain,
    ( spl4_22
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f864,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_22
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f858,f334])).

fof(f334,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f332])).

fof(f859,plain,
    ( spl4_37
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f223,f172,f122,f117,f856])).

fof(f849,plain,
    ( spl4_35
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f221,f172,f122,f117,f846])).

fof(f846,plain,
    ( spl4_35
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f528,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_10
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_10
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f526,f185])).

fof(f526,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f525,f267])).

fof(f525,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f524,f221])).

fof(f524,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f523,f343])).

fof(f343,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(superposition,[],[f303,f283])).

fof(f283,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl4_16
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f303,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl4_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f523,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f486,f223])).

fof(f486,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f180,f262,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f304,plain,
    ( spl4_17
    | spl4_18
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f257,f137,f132,f301,f297])).

fof(f132,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f137,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f257,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f254,f139])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f254,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(resolution,[],[f97,f134])).

fof(f134,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f284,plain,
    ( spl4_16
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f225,f137,f281])).

fof(f225,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f139,f95])).

fof(f268,plain,
    ( spl4_15
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f239,f142,f137,f265])).

fof(f142,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f239,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f232,f144])).

fof(f144,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f232,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f139,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f263,plain,
    ( spl4_14
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f204,f172,f117,f260])).

fof(f204,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f119,f174,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f199,plain,
    ( ~ spl4_1
    | ~ spl4_8
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_8
    | spl4_9 ),
    inference(subsumption_resolution,[],[f197,f174])).

fof(f197,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_1
    | spl4_9 ),
    inference(subsumption_resolution,[],[f193,f119])).

fof(f193,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_9 ),
    inference(resolution,[],[f181,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f181,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f190,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f65,f187,f183,f179])).

fof(f65,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f175,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f159,f137,f172])).

fof(f159,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f139,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f145,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f64,f142])).

fof(f64,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f140,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f62,f137])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f135,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f61,f132])).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f63,f122])).

fof(f63,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f120,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f60,f117])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (2095)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.46  % (2114)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.46  % (2106)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.47  % (2119)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.48  % (2100)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (2098)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (2116)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (2101)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (2113)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (2099)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (2119)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f1223,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f120,f125,f135,f140,f145,f175,f190,f199,f263,f268,f284,f304,f528,f849,f859,f865,f866,f867,f970,f1045,f1071,f1072,f1208,f1218])).
% 0.20/0.51  fof(f1218,plain,(
% 0.20/0.51    ~spl4_9 | spl4_11 | ~spl4_14 | ~spl4_17 | ~spl4_32 | ~spl4_37 | ~spl4_51),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1217])).
% 0.20/0.51  fof(f1217,plain,(
% 0.20/0.51    $false | (~spl4_9 | spl4_11 | ~spl4_14 | ~spl4_17 | ~spl4_32 | ~spl4_37 | ~spl4_51)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1075,f1206])).
% 0.20/0.51  fof(f1206,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_37 | ~spl4_51)),
% 0.20/0.51    inference(forward_demodulation,[],[f1205,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    inference(flattening,[],[f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  % (2108)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f1205,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) | (~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_37 | ~spl4_51)),
% 0.20/0.51    inference(forward_demodulation,[],[f1189,f995])).
% 0.20/0.51  fof(f995,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_51),
% 0.20/0.51    inference(avatar_component_clause,[],[f993])).
% 0.20/0.51  fof(f993,plain,(
% 0.20/0.51    spl4_51 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.20/0.51  fof(f1189,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)))) | (~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_37)),
% 0.20/0.51    inference(forward_demodulation,[],[f1188,f763])).
% 0.20/0.51  fof(f763,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~spl4_32),
% 0.20/0.51    inference(avatar_component_clause,[],[f761])).
% 0.20/0.51  fof(f761,plain,(
% 0.20/0.51    spl4_32 <=> k1_xboole_0 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.51  fof(f1188,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl4_9 | ~spl4_14 | ~spl4_37)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1187,f262])).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl4_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f260])).
% 0.20/0.51  fof(f260,plain,(
% 0.20/0.51    spl4_14 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.51  fof(f1187,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_9 | ~spl4_37)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1177,f180])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    v1_funct_1(k2_funct_1(sK2)) | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f179])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    spl4_9 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f1177,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_37),
% 0.20/0.51    inference(superposition,[],[f76,f858])).
% 0.20/0.51  fof(f858,plain,(
% 0.20/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_37),
% 0.20/0.51    inference(avatar_component_clause,[],[f856])).
% 0.20/0.51  fof(f856,plain,(
% 0.20/0.51    spl4_37 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.51  fof(f1075,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_11 | ~spl4_17 | ~spl4_32)),
% 0.20/0.51    inference(forward_demodulation,[],[f1074,f763])).
% 0.20/0.51  fof(f1074,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_11 | ~spl4_17)),
% 0.20/0.51    inference(forward_demodulation,[],[f1073,f106])).
% 0.20/0.51  fof(f1073,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_11 | ~spl4_17)),
% 0.20/0.51    inference(forward_demodulation,[],[f189,f299])).
% 0.20/0.51  fof(f299,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl4_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f297])).
% 0.20/0.51  fof(f297,plain,(
% 0.20/0.51    spl4_17 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f187])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    spl4_11 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.51  fof(f1208,plain,(
% 0.20/0.51    ~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_37 | ~spl4_51 | spl4_60),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1207])).
% 0.20/0.51  fof(f1207,plain,(
% 0.20/0.51    $false | (~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_37 | ~spl4_51 | spl4_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1206,f1038])).
% 0.20/0.51  fof(f1038,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl4_60),
% 0.20/0.51    inference(avatar_component_clause,[],[f1037])).
% 0.20/0.51  fof(f1037,plain,(
% 0.20/0.51    spl4_60 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.20/0.51  fof(f1072,plain,(
% 0.20/0.51    k1_xboole_0 != sK2 | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | sK1 != k2_relat_1(sK2) | k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f1071,plain,(
% 0.20/0.51    ~spl4_51 | ~spl4_60 | spl4_61),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1070])).
% 0.20/0.51  fof(f1070,plain,(
% 0.20/0.51    $false | (~spl4_51 | ~spl4_60 | spl4_61)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1069,f1063])).
% 0.20/0.51  fof(f1063,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0))) ) | (~spl4_51 | ~spl4_60)),
% 0.20/0.51    inference(forward_demodulation,[],[f1049,f995])).
% 0.20/0.51  fof(f1049,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0))) ) | ~spl4_60),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f1039,f231])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 0.20/0.51    inference(superposition,[],[f95,f106])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f1039,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_60),
% 0.20/0.52    inference(avatar_component_clause,[],[f1037])).
% 0.20/0.52  fof(f1069,plain,(
% 0.20/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (~spl4_60 | spl4_61)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f1039,f1044,f114])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f110,f106])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.52    inference(equality_resolution,[],[f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f1044,plain,(
% 0.20/0.52    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | spl4_61),
% 0.20/0.52    inference(avatar_component_clause,[],[f1042])).
% 0.20/0.52  fof(f1042,plain,(
% 0.20/0.52    spl4_61 <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.20/0.52  fof(f1045,plain,(
% 0.20/0.52    ~spl4_61 | spl4_10 | ~spl4_17 | ~spl4_32),
% 0.20/0.52    inference(avatar_split_clause,[],[f1035,f761,f297,f183,f1042])).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    spl4_10 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.52  fof(f1035,plain,(
% 0.20/0.52    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_10 | ~spl4_17 | ~spl4_32)),
% 0.20/0.52    inference(forward_demodulation,[],[f1034,f763])).
% 0.20/0.52  fof(f1034,plain,(
% 0.20/0.52    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_10 | ~spl4_17)),
% 0.20/0.52    inference(forward_demodulation,[],[f185,f299])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f183])).
% 0.20/0.52  fof(f970,plain,(
% 0.20/0.52    ~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_38),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f969])).
% 0.20/0.52  fof(f969,plain,(
% 0.20/0.52    $false | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_38)),
% 0.20/0.52    inference(subsumption_resolution,[],[f968,f189])).
% 0.20/0.52  fof(f968,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | ~spl4_14 | ~spl4_15 | ~spl4_38)),
% 0.20/0.52    inference(forward_demodulation,[],[f967,f563])).
% 0.20/0.52  fof(f563,plain,(
% 0.20/0.52    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_14 | ~spl4_15)),
% 0.20/0.52    inference(forward_demodulation,[],[f532,f562])).
% 0.20/0.52  fof(f562,plain,(
% 0.20/0.52    sK1 = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_14 | ~spl4_15)),
% 0.20/0.52    inference(forward_demodulation,[],[f561,f267])).
% 0.20/0.52  fof(f267,plain,(
% 0.20/0.52    sK1 = k2_relat_1(sK2) | ~spl4_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f265])).
% 0.20/0.52  % (2096)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  fof(f265,plain,(
% 0.20/0.52    spl4_15 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.52  fof(f561,plain,(
% 0.20/0.52    k2_relat_1(sK2) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_14)),
% 0.20/0.52    inference(forward_demodulation,[],[f535,f221])).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_8)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f174,f119,f124,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    v2_funct_1(sK2) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f122])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl4_2 <=> v2_funct_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    v1_funct_1(sK2) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    spl4_1 <=> v1_funct_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    v1_relat_1(sK2) | ~spl4_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f172])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    spl4_8 <=> v1_relat_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.52  fof(f535,plain,(
% 0.20/0.52    k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_14)),
% 0.20/0.52    inference(forward_demodulation,[],[f496,f223])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_8)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f174,f119,f124,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f496,plain,(
% 0.20/0.52    k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~spl4_14),
% 0.20/0.52    inference(resolution,[],[f262,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.52  fof(f532,plain,(
% 0.20/0.52    k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_14)),
% 0.20/0.52    inference(forward_demodulation,[],[f484,f223])).
% 0.20/0.52  fof(f484,plain,(
% 0.20/0.52    k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~spl4_14),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f262,f70])).
% 0.20/0.52  fof(f967,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl4_9 | ~spl4_14 | ~spl4_38)),
% 0.20/0.52    inference(subsumption_resolution,[],[f966,f262])).
% 0.20/0.52  fof(f966,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_9 | ~spl4_38)),
% 0.20/0.52    inference(subsumption_resolution,[],[f960,f180])).
% 0.20/0.52  fof(f960,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_38),
% 0.20/0.52    inference(superposition,[],[f76,f863])).
% 0.20/0.52  fof(f863,plain,(
% 0.20/0.52    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl4_38),
% 0.20/0.52    inference(avatar_component_clause,[],[f861])).
% 0.20/0.52  fof(f861,plain,(
% 0.20/0.52    spl4_38 <=> sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.52  fof(f867,plain,(
% 0.20/0.52    spl4_32 | ~spl4_17 | ~spl4_8 | ~spl4_15),
% 0.20/0.52    inference(avatar_split_clause,[],[f279,f265,f172,f297,f761])).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | (~spl4_8 | ~spl4_15)),
% 0.20/0.52    inference(subsumption_resolution,[],[f272,f174])).
% 0.20/0.52  % (2109)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl4_15),
% 0.20/0.52    inference(superposition,[],[f73,f267])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.52  fof(f866,plain,(
% 0.20/0.52    sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | sK0 = k1_relat_1(sK2)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f865,plain,(
% 0.20/0.52    spl4_38 | ~spl4_22 | ~spl4_37),
% 0.20/0.52    inference(avatar_split_clause,[],[f864,f856,f332,f861])).
% 0.20/0.52  fof(f332,plain,(
% 0.20/0.52    spl4_22 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.52  fof(f864,plain,(
% 0.20/0.52    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl4_22 | ~spl4_37)),
% 0.20/0.52    inference(forward_demodulation,[],[f858,f334])).
% 0.20/0.52  fof(f334,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK2) | ~spl4_22),
% 0.20/0.52    inference(avatar_component_clause,[],[f332])).
% 0.20/0.52  fof(f859,plain,(
% 0.20/0.52    spl4_37 | ~spl4_1 | ~spl4_2 | ~spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f223,f172,f122,f117,f856])).
% 0.20/0.52  fof(f849,plain,(
% 0.20/0.52    spl4_35 | ~spl4_1 | ~spl4_2 | ~spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f221,f172,f122,f117,f846])).
% 0.20/0.52  fof(f846,plain,(
% 0.20/0.52    spl4_35 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.52  fof(f528,plain,(
% 0.20/0.52    ~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_10 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_18),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f527])).
% 0.20/0.52  fof(f527,plain,(
% 0.20/0.52    $false | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_10 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_18)),
% 0.20/0.52    inference(subsumption_resolution,[],[f526,f185])).
% 0.20/0.52  fof(f526,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_18)),
% 0.20/0.52    inference(forward_demodulation,[],[f525,f267])).
% 0.20/0.52  fof(f525,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | ~spl4_14 | ~spl4_16 | ~spl4_18)),
% 0.20/0.52    inference(forward_demodulation,[],[f524,f221])).
% 0.20/0.52  fof(f524,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | ~spl4_14 | ~spl4_16 | ~spl4_18)),
% 0.20/0.52    inference(forward_demodulation,[],[f523,f343])).
% 0.20/0.52  fof(f343,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK2) | (~spl4_16 | ~spl4_18)),
% 0.20/0.52    inference(superposition,[],[f303,f283])).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl4_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f281])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    spl4_16 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.52  fof(f303,plain,(
% 0.20/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f301])).
% 0.20/0.52  fof(f301,plain,(
% 0.20/0.52    spl4_18 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.52  fof(f523,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | ~spl4_14)),
% 0.20/0.52    inference(forward_demodulation,[],[f486,f223])).
% 0.20/0.52  fof(f486,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl4_9 | ~spl4_14)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f180,f262,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f304,plain,(
% 0.20/0.52    spl4_17 | spl4_18 | ~spl4_4 | ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f257,f137,f132,f301,f297])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    spl4_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | (~spl4_4 | ~spl4_5)),
% 0.20/0.52    inference(subsumption_resolution,[],[f254,f139])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f137])).
% 0.20/0.52  fof(f254,plain,(
% 0.20/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.20/0.52    inference(resolution,[],[f97,f134])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    v1_funct_2(sK2,sK0,sK1) | ~spl4_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f132])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f59])).
% 0.20/0.52  fof(f284,plain,(
% 0.20/0.52    spl4_16 | ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f225,f137,f281])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl4_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f139,f95])).
% 0.20/0.52  fof(f268,plain,(
% 0.20/0.52    spl4_15 | ~spl4_5 | ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f239,f142,f137,f265])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    sK1 = k2_relat_1(sK2) | (~spl4_5 | ~spl4_6)),
% 0.20/0.52    inference(forward_demodulation,[],[f232,f144])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f142])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f139,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f263,plain,(
% 0.20/0.52    spl4_14 | ~spl4_1 | ~spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f204,f172,f117,f260])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_8)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f119,f174,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ~spl4_1 | ~spl4_8 | spl4_9),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f198])).
% 0.20/0.52  fof(f198,plain,(
% 0.20/0.52    $false | (~spl4_1 | ~spl4_8 | spl4_9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f197,f174])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | (~spl4_1 | spl4_9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f193,f119])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_9),
% 0.20/0.52    inference(resolution,[],[f181,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | spl4_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f179])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    ~spl4_9 | ~spl4_10 | ~spl4_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f65,f187,f183,f179])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f21])).
% 0.20/0.52  fof(f21,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    spl4_8 | ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f159,f137,f172])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f139,f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f64,f142])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f52])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f62,f137])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f52])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f61,f132])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f52])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f63,f122])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    v2_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f52])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f60,f117])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    v1_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f52])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (2119)------------------------------
% 0.20/0.52  % (2119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2119)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (2119)Memory used [KB]: 11257
% 0.20/0.52  % (2119)Time elapsed: 0.091 s
% 0.20/0.52  % (2119)------------------------------
% 0.20/0.52  % (2119)------------------------------
% 0.20/0.52  % (2094)Success in time 0.164 s
%------------------------------------------------------------------------------
