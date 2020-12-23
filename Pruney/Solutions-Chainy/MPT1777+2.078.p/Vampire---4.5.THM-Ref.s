%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 643 expanded)
%              Number of leaves         :   61 ( 334 expanded)
%              Depth                    :   26
%              Number of atoms          : 1396 (6315 expanded)
%              Number of equality atoms :   52 ( 682 expanded)
%              Maximal formula depth    :   32 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f988,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f195,f200,f205,f210,f218,f224,f261,f267,f327,f443,f537,f570,f593,f595,f615,f733,f734,f748,f759,f787,f978,f987])).

fof(f987,plain,
    ( ~ spl14_51
    | ~ spl14_64
    | ~ spl14_67
    | ~ spl14_69
    | spl14_89 ),
    inference(avatar_contradiction_clause,[],[f986])).

fof(f986,plain,
    ( $false
    | ~ spl14_51
    | ~ spl14_64
    | ~ spl14_67
    | ~ spl14_69
    | spl14_89 ),
    inference(subsumption_resolution,[],[f979,f778])).

fof(f778,plain,
    ( m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ spl14_69 ),
    inference(avatar_component_clause,[],[f776])).

fof(f776,plain,
    ( spl14_69
  <=> m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_69])])).

fof(f979,plain,
    ( ~ m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ spl14_51
    | ~ spl14_64
    | ~ spl14_67
    | spl14_89 ),
    inference(unit_resulting_resolution,[],[f591,f752,f725,f959,f112])).

fof(f112,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | sP12(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f112_D])).

fof(f112_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
          | ~ r2_hidden(X7,X5)
          | ~ v3_pre_topc(X5,X3)
          | ~ r1_tarski(X5,u1_struct_0(X2)) )
    <=> ~ sP12(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).

fof(f959,plain,
    ( ~ sP12(sK7,sK6,sK9)
    | spl14_89 ),
    inference(avatar_component_clause,[],[f957])).

fof(f957,plain,
    ( spl14_89
  <=> sP12(sK7,sK6,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_89])])).

fof(f725,plain,
    ( r1_tarski(sK11(sK6,sK9,k1_xboole_0),u1_struct_0(sK6))
    | ~ spl14_64 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl14_64
  <=> r1_tarski(sK11(sK6,sK9,k1_xboole_0),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_64])])).

fof(f752,plain,
    ( v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK7)
    | ~ spl14_67 ),
    inference(avatar_component_clause,[],[f750])).

fof(f750,plain,
    ( spl14_67
  <=> v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_67])])).

fof(f591,plain,
    ( r2_hidden(sK9,sK11(sK6,sK9,k1_xboole_0))
    | ~ spl14_51 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl14_51
  <=> r2_hidden(sK9,sK11(sK6,sK9,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_51])])).

fof(f978,plain,
    ( ~ spl14_89
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | spl14_16
    | ~ spl14_17
    | ~ spl14_18
    | spl14_19
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(avatar_split_clause,[],[f977,f440,f221,f215,f207,f202,f197,f192,f187,f182,f177,f172,f167,f162,f157,f152,f147,f137,f117,f957])).

fof(f117,plain,
    ( spl14_1
  <=> r1_tmap_1(sK7,sK5,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f137,plain,
    ( spl14_5
  <=> m1_subset_1(sK9,u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f147,plain,
    ( spl14_7
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f152,plain,
    ( spl14_8
  <=> v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f157,plain,
    ( spl14_9
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f162,plain,
    ( spl14_10
  <=> m1_pre_topc(sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f167,plain,
    ( spl14_11
  <=> v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f172,plain,
    ( spl14_12
  <=> m1_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f177,plain,
    ( spl14_13
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f182,plain,
    ( spl14_14
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f187,plain,
    ( spl14_15
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f192,plain,
    ( spl14_16
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f197,plain,
    ( spl14_17
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f202,plain,
    ( spl14_18
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f207,plain,
    ( spl14_19
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f215,plain,
    ( spl14_20
  <=> m1_subset_1(sK9,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f221,plain,
    ( spl14_21
  <=> r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_21])])).

fof(f440,plain,
    ( spl14_39
  <=> m1_pre_topc(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_39])])).

fof(f977,plain,
    ( ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | spl14_16
    | ~ spl14_17
    | ~ spl14_18
    | spl14_19
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f976,f209])).

fof(f209,plain,
    ( ~ v2_struct_0(sK4)
    | spl14_19 ),
    inference(avatar_component_clause,[],[f207])).

% (12164)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f976,plain,
    ( v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | spl14_16
    | ~ spl14_17
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f975,f204])).

fof(f204,plain,
    ( v2_pre_topc(sK4)
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f202])).

fof(f975,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | spl14_16
    | ~ spl14_17
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f974,f199])).

fof(f199,plain,
    ( l1_pre_topc(sK4)
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f197])).

fof(f974,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | spl14_16
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f973,f194])).

fof(f194,plain,
    ( ~ v2_struct_0(sK5)
    | spl14_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f973,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f972,f189])).

fof(f189,plain,
    ( v2_pre_topc(sK5)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f187])).

fof(f972,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | spl14_13
    | ~ spl14_14
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f971,f184])).

fof(f184,plain,
    ( l1_pre_topc(sK5)
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f971,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | spl14_13
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f970,f179])).

fof(f179,plain,
    ( ~ v2_struct_0(sK6)
    | spl14_13 ),
    inference(avatar_component_clause,[],[f177])).

fof(f970,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_12
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f969,f174])).

fof(f174,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f969,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | spl14_11
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f968,f169])).

fof(f169,plain,
    ( ~ v2_struct_0(sK7)
    | spl14_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f968,plain,
    ( v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_10
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f967,f164])).

fof(f164,plain,
    ( m1_pre_topc(sK7,sK4)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f967,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f966,f159])).

fof(f159,plain,
    ( v1_funct_1(sK8)
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f966,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_pre_topc(sK7,sK4)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f965,f154])).

fof(f154,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f965,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK8)
    | ~ m1_pre_topc(sK7,sK4)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_7
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f964,f149])).

fof(f149,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f964,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK8)
    | ~ m1_pre_topc(sK7,sK4)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_20
    | ~ spl14_21
    | ~ spl14_39 ),
    inference(subsumption_resolution,[],[f963,f442])).

fof(f442,plain,
    ( m1_pre_topc(sK6,sK7)
    | ~ spl14_39 ),
    inference(avatar_component_clause,[],[f440])).

% (12165)Refutation not found, incomplete strategy% (12165)------------------------------
% (12165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12165)Termination reason: Refutation not found, incomplete strategy

% (12165)Memory used [KB]: 10746
% (12165)Time elapsed: 0.092 s
% (12165)------------------------------
% (12165)------------------------------
fof(f963,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK8)
    | ~ m1_pre_topc(sK7,sK4)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_5
    | ~ spl14_20
    | ~ spl14_21 ),
    inference(subsumption_resolution,[],[f962,f139])).

fof(f139,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f962,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_pre_topc(sK6,sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK8)
    | ~ m1_pre_topc(sK7,sK4)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_20
    | ~ spl14_21 ),
    inference(subsumption_resolution,[],[f961,f217])).

fof(f217,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f215])).

fof(f961,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_pre_topc(sK6,sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK8)
    | ~ m1_pre_topc(sK7,sK4)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | spl14_1
    | ~ spl14_21 ),
    inference(subsumption_resolution,[],[f955,f119])).

fof(f119,plain,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f955,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_pre_topc(sK6,sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK8)
    | ~ m1_pre_topc(sK7,sK4)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP12(sK7,sK6,sK9)
    | ~ spl14_21 ),
    inference(resolution,[],[f113,f223])).

fof(f223,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9)
    | ~ spl14_21 ),
    inference(avatar_component_clause,[],[f221])).

fof(f113,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP12(X3,X2,X7) ) ),
    inference(general_splitting,[],[f110,f112_D])).

fof(f110,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f787,plain,
    ( spl14_69
    | ~ spl14_6
    | ~ spl14_66 ),
    inference(avatar_split_clause,[],[f763,f745,f142,f776])).

fof(f142,plain,
    ( spl14_6
  <=> g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f745,plain,
    ( spl14_66
  <=> sP3(sK6,sK11(sK6,sK9,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_66])])).

fof(f763,plain,
    ( m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ spl14_6
    | ~ spl14_66 ),
    inference(unit_resulting_resolution,[],[f747,f401])).

fof(f401,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
        | ~ sP3(sK6,X0) )
    | ~ spl14_6 ),
    inference(superposition,[],[f97,f144])).

fof(f144,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f747,plain,
    ( sP3(sK6,sK11(sK6,sK9,k1_xboole_0))
    | ~ spl14_66 ),
    inference(avatar_component_clause,[],[f745])).

fof(f759,plain,
    ( spl14_67
    | ~ spl14_6
    | ~ spl14_24
    | ~ spl14_30
    | ~ spl14_65 ),
    inference(avatar_split_clause,[],[f742,f728,f313,f249,f142,f750])).

fof(f249,plain,
    ( spl14_24
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f313,plain,
    ( spl14_30
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f728,plain,
    ( spl14_65
  <=> sP2(sK6,sK11(sK6,sK9,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_65])])).

fof(f742,plain,
    ( v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK7)
    | ~ spl14_6
    | ~ spl14_24
    | ~ spl14_30
    | ~ spl14_65 ),
    inference(resolution,[],[f730,f333])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ sP2(sK6,X0)
        | v3_pre_topc(X0,sK7) )
    | ~ spl14_6
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(subsumption_resolution,[],[f332,f315])).

fof(f315,plain,
    ( v2_pre_topc(sK6)
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f313])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ sP2(sK6,X0)
        | ~ v2_pre_topc(sK6)
        | v3_pre_topc(X0,sK7) )
    | ~ spl14_6
    | ~ spl14_24 ),
    inference(subsumption_resolution,[],[f331,f251])).

fof(f251,plain,
    ( l1_pre_topc(sK6)
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f249])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ sP2(sK6,X0)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v3_pre_topc(X0,sK7) )
    | ~ spl14_6 ),
    inference(resolution,[],[f102,f330])).

fof(f330,plain,
    ( ! [X0] :
        ( ~ sP3(sK6,X0)
        | v3_pre_topc(X0,sK7) )
    | ~ spl14_6 ),
    inference(superposition,[],[f96,f144])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f102,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ sP2(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP2(X0,X1)
            | ~ sP3(X0,X1) )
          & ( sP3(X0,X1)
            | ~ sP2(X0,X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
        <=> sP3(X0,X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f27,f35,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f730,plain,
    ( sP2(sK6,sK11(sK6,sK9,k1_xboole_0))
    | ~ spl14_65 ),
    inference(avatar_component_clause,[],[f728])).

fof(f748,plain,
    ( spl14_66
    | ~ spl14_24
    | ~ spl14_30
    | ~ spl14_65 ),
    inference(avatar_split_clause,[],[f738,f728,f313,f249,f745])).

fof(f738,plain,
    ( sP3(sK6,sK11(sK6,sK9,k1_xboole_0))
    | ~ spl14_24
    | ~ spl14_30
    | ~ spl14_65 ),
    inference(unit_resulting_resolution,[],[f315,f251,f730,f102])).

fof(f734,plain,
    ( spl14_64
    | ~ spl14_53 ),
    inference(avatar_split_clause,[],[f721,f612,f723])).

fof(f612,plain,
    ( spl14_53
  <=> m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_53])])).

fof(f721,plain,
    ( r1_tarski(sK11(sK6,sK9,k1_xboole_0),u1_struct_0(sK6))
    | ~ spl14_53 ),
    inference(resolution,[],[f614,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f614,plain,
    ( m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl14_53 ),
    inference(avatar_component_clause,[],[f612])).

fof(f733,plain,
    ( spl14_65
    | ~ spl14_49
    | ~ spl14_53 ),
    inference(avatar_split_clause,[],[f732,f612,f579,f728])).

fof(f579,plain,
    ( spl14_49
  <=> v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_49])])).

fof(f732,plain,
    ( sP2(sK6,sK11(sK6,sK9,k1_xboole_0))
    | ~ spl14_49
    | ~ spl14_53 ),
    inference(subsumption_resolution,[],[f719,f581])).

fof(f581,plain,
    ( v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK6)
    | ~ spl14_49 ),
    inference(avatar_component_clause,[],[f579])).

fof(f719,plain,
    ( sP2(sK6,sK11(sK6,sK9,k1_xboole_0))
    | ~ v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK6)
    | ~ spl14_53 ),
    inference(resolution,[],[f614,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X0,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v3_pre_topc(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v3_pre_topc(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f615,plain,
    ( spl14_53
    | spl14_13
    | ~ spl14_20
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(avatar_split_clause,[],[f607,f313,f249,f215,f177,f612])).

fof(f607,plain,
    ( m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK6)))
    | spl14_13
    | ~ spl14_20
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f179,f315,f251,f217,f212])).

% (12164)Refutation not found, incomplete strategy% (12164)------------------------------
% (12164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f212,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK11(X0,X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f109,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK11(X0,X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

% (12164)Termination reason: Refutation not found, incomplete strategy

% (12164)Memory used [KB]: 6268
% (12164)Time elapsed: 0.073 s
% (12164)------------------------------
% (12164)------------------------------
fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ( sP1(X0,X1,sK11(X0,X1,X2),X2)
                & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f33,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sP1(X0,X1,sK11(X0,X1,X2),X2)
        & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( sP1(X0,X1,X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f32,f31])).

% (12182)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f31,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ( r2_hidden(X1,X3)
        & v4_pre_topc(X3,X0)
        & v3_pre_topc(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0,X1,X3,X2] :
      ( ( r2_hidden(X3,X2)
      <~> sP0(X3,X1,X0) )
      | ~ sP1(X0,X1,X3,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( r2_hidden(X3,X2)
                  <~> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( r2_hidden(X3,X2)
                  <~> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f595,plain,
    ( spl14_49
    | ~ spl14_48 ),
    inference(avatar_split_clause,[],[f577,f565,f579])).

fof(f565,plain,
    ( spl14_48
  <=> sP0(sK11(sK6,sK9,k1_xboole_0),sK9,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).

fof(f577,plain,
    ( v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK6)
    | ~ spl14_48 ),
    inference(resolution,[],[f567,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v3_pre_topc(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ v4_pre_topc(X0,X2)
        | ~ v3_pre_topc(X0,X2) )
      & ( ( r2_hidden(X1,X0)
          & v4_pre_topc(X0,X2)
          & v3_pre_topc(X0,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ~ r2_hidden(X1,X3)
        | ~ v4_pre_topc(X3,X0)
        | ~ v3_pre_topc(X3,X0) )
      & ( ( r2_hidden(X1,X3)
          & v4_pre_topc(X3,X0)
          & v3_pre_topc(X3,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ~ r2_hidden(X1,X3)
        | ~ v4_pre_topc(X3,X0)
        | ~ v3_pre_topc(X3,X0) )
      & ( ( r2_hidden(X1,X3)
          & v4_pre_topc(X3,X0)
          & v3_pre_topc(X3,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f567,plain,
    ( sP0(sK11(sK6,sK9,k1_xboole_0),sK9,sK6)
    | ~ spl14_48 ),
    inference(avatar_component_clause,[],[f565])).

fof(f593,plain,
    ( spl14_51
    | ~ spl14_48 ),
    inference(avatar_split_clause,[],[f575,f565,f589])).

fof(f575,plain,
    ( r2_hidden(sK9,sK11(sK6,sK9,k1_xboole_0))
    | ~ spl14_48 ),
    inference(resolution,[],[f567,f89])).

% (12172)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f570,plain,
    ( spl14_48
    | ~ spl14_46 ),
    inference(avatar_split_clause,[],[f569,f534,f565])).

fof(f534,plain,
    ( spl14_46
  <=> sP1(sK6,sK9,sK11(sK6,sK9,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_46])])).

fof(f569,plain,
    ( sP0(sK11(sK6,sK9,k1_xboole_0),sK9,sK6)
    | ~ spl14_46 ),
    inference(subsumption_resolution,[],[f563,f237])).

fof(f237,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f79,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f563,plain,
    ( r2_hidden(sK11(sK6,sK9,k1_xboole_0),k1_xboole_0)
    | sP0(sK11(sK6,sK9,k1_xboole_0),sK9,sK6)
    | ~ spl14_46 ),
    inference(resolution,[],[f536,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r2_hidden(X2,X3)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ~ sP0(X2,X1,X0)
          | ~ r2_hidden(X2,X3) )
        & ( sP0(X2,X1,X0)
          | r2_hidden(X2,X3) ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X3,X2] :
      ( ( ( ~ sP0(X3,X1,X0)
          | ~ r2_hidden(X3,X2) )
        & ( sP0(X3,X1,X0)
          | r2_hidden(X3,X2) ) )
      | ~ sP1(X0,X1,X3,X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f536,plain,
    ( sP1(sK6,sK9,sK11(sK6,sK9,k1_xboole_0),k1_xboole_0)
    | ~ spl14_46 ),
    inference(avatar_component_clause,[],[f534])).

fof(f537,plain,
    ( spl14_46
    | spl14_13
    | ~ spl14_20
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(avatar_split_clause,[],[f530,f313,f249,f215,f177,f534])).

fof(f530,plain,
    ( sP1(sK6,sK9,sK11(sK6,sK9,k1_xboole_0),k1_xboole_0)
    | spl14_13
    | ~ spl14_20
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f179,f315,f251,f217,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,sK11(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f108,f80])).

fof(f108,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,sK11(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | sP1(X0,X1,sK11(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f443,plain,
    ( spl14_39
    | ~ spl14_6
    | ~ spl14_24
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f438,f264,f249,f142,f440])).

fof(f264,plain,
    ( spl14_26
  <=> m1_pre_topc(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f438,plain,
    ( m1_pre_topc(sK6,sK7)
    | ~ spl14_6
    | ~ spl14_24
    | ~ spl14_26 ),
    inference(forward_demodulation,[],[f428,f144])).

fof(f428,plain,
    ( m1_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ spl14_24
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f251,f251,f266,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f266,plain,
    ( m1_pre_topc(sK6,sK6)
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f264])).

fof(f327,plain,
    ( spl14_30
    | ~ spl14_12
    | ~ spl14_17
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f326,f202,f197,f172,f313])).

fof(f326,plain,
    ( v2_pre_topc(sK6)
    | ~ spl14_12
    | ~ spl14_17
    | ~ spl14_18 ),
    inference(subsumption_resolution,[],[f325,f204])).

fof(f325,plain,
    ( v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK4)
    | ~ spl14_12
    | ~ spl14_17 ),
    inference(subsumption_resolution,[],[f306,f199])).

fof(f306,plain,
    ( v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ spl14_12 ),
    inference(resolution,[],[f95,f174])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f267,plain,
    ( spl14_26
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f262,f249,f264])).

fof(f262,plain,
    ( m1_pre_topc(sK6,sK6)
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f251,f81])).

fof(f81,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f261,plain,
    ( spl14_24
    | ~ spl14_12
    | ~ spl14_17 ),
    inference(avatar_split_clause,[],[f260,f197,f172,f249])).

fof(f260,plain,
    ( l1_pre_topc(sK6)
    | ~ spl14_12
    | ~ spl14_17 ),
    inference(subsumption_resolution,[],[f243,f199])).

fof(f243,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ spl14_12 ),
    inference(resolution,[],[f84,f174])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f224,plain,
    ( spl14_21
    | ~ spl14_2
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f219,f127,f122,f221])).

fof(f122,plain,
    ( spl14_2
  <=> r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f127,plain,
    ( spl14_3
  <=> sK9 = sK10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f219,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9)
    | ~ spl14_2
    | ~ spl14_3 ),
    inference(forward_demodulation,[],[f124,f129])).

fof(f129,plain,
    ( sK9 = sK10
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f124,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f218,plain,
    ( spl14_20
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f213,f132,f127,f215])).

fof(f132,plain,
    ( spl14_4
  <=> m1_subset_1(sK10,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f213,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(backward_demodulation,[],[f134,f129])).

fof(f134,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK6))
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f210,plain,(
    ~ spl14_19 ),
    inference(avatar_split_clause,[],[f60,f207])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
    & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
    & sK9 = sK10
    & m1_subset_1(sK10,u1_struct_0(sK6))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    & v1_funct_1(sK8)
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f16,f43,f42,f41,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

% (12168)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK5,X4,X5)
                          & r1_tmap_1(X2,sK5,k3_tmap_1(sK4,sK5,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK4)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK4)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK5,X4,X5)
                        & r1_tmap_1(X2,sK5,k3_tmap_1(sK4,sK5,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK5,X4,X5)
                      & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,X3,sK6,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK6)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK5,X4,X5)
                    & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,X3,sK6,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK6)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK4)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK7,sK5,X4,X5)
                  & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK6)) )
              & m1_subset_1(X5,u1_struct_0(sK7)) )
          & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
          & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK5))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK7,sK5,X4,X5)
                & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK6)) )
            & m1_subset_1(X5,u1_struct_0(sK7)) )
        & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
        & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK5))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK7,sK5,sK8,X5)
              & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK6)) )
          & m1_subset_1(X5,u1_struct_0(sK7)) )
      & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK7,sK5,sK8,X5)
            & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK6)) )
        & m1_subset_1(X5,u1_struct_0(sK7)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
          & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
          & sK9 = X6
          & m1_subset_1(X6,u1_struct_0(sK6)) )
      & m1_subset_1(sK9,u1_struct_0(sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
        & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
        & sK9 = X6
        & m1_subset_1(X6,u1_struct_0(sK6)) )
   => ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
      & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
      & sK9 = sK10
      & m1_subset_1(sK10,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

% (12173)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f205,plain,(
    spl14_18 ),
    inference(avatar_split_clause,[],[f61,f202])).

fof(f61,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f200,plain,(
    spl14_17 ),
    inference(avatar_split_clause,[],[f62,f197])).

fof(f62,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f195,plain,(
    ~ spl14_16 ),
    inference(avatar_split_clause,[],[f63,f192])).

fof(f63,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f190,plain,(
    spl14_15 ),
    inference(avatar_split_clause,[],[f64,f187])).

fof(f64,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f185,plain,(
    spl14_14 ),
    inference(avatar_split_clause,[],[f65,f182])).

fof(f65,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f180,plain,(
    ~ spl14_13 ),
    inference(avatar_split_clause,[],[f66,f177])).

fof(f66,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f175,plain,(
    spl14_12 ),
    inference(avatar_split_clause,[],[f67,f172])).

fof(f67,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f170,plain,(
    ~ spl14_11 ),
    inference(avatar_split_clause,[],[f68,f167])).

fof(f68,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f165,plain,(
    spl14_10 ),
    inference(avatar_split_clause,[],[f69,f162])).

fof(f69,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f160,plain,(
    spl14_9 ),
    inference(avatar_split_clause,[],[f70,f157])).

% (12171)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f70,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f155,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f71,f152])).

fof(f71,plain,(
    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f150,plain,(
    spl14_7 ),
    inference(avatar_split_clause,[],[f72,f147])).

fof(f72,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f145,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f73,f142])).

fof(f73,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,(
    spl14_5 ),
    inference(avatar_split_clause,[],[f74,f137])).

fof(f74,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f75,f132])).

fof(f75,plain,(
    m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f44])).

fof(f130,plain,(
    spl14_3 ),
    inference(avatar_split_clause,[],[f76,f127])).

fof(f76,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f44])).

fof(f125,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f77,f122])).

fof(f77,plain,(
    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f78,f117])).

fof(f78,plain,(
    ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:01:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (12179)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.46  % (12179)Refutation not found, incomplete strategy% (12179)------------------------------
% 0.22/0.46  % (12179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (12179)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (12179)Memory used [KB]: 6652
% 0.22/0.46  % (12179)Time elapsed: 0.053 s
% 0.22/0.46  % (12179)------------------------------
% 0.22/0.46  % (12179)------------------------------
% 0.22/0.48  % (12175)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (12167)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (12180)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (12166)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (12176)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12174)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (12175)Refutation not found, incomplete strategy% (12175)------------------------------
% 0.22/0.50  % (12175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12175)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12175)Memory used [KB]: 11001
% 0.22/0.50  % (12175)Time elapsed: 0.086 s
% 0.22/0.50  % (12175)------------------------------
% 0.22/0.50  % (12175)------------------------------
% 0.22/0.50  % (12177)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (12165)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12167)Refutation not found, incomplete strategy% (12167)------------------------------
% 0.22/0.50  % (12167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12167)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12167)Memory used [KB]: 10874
% 0.22/0.50  % (12167)Time elapsed: 0.074 s
% 0.22/0.50  % (12167)------------------------------
% 0.22/0.50  % (12167)------------------------------
% 0.22/0.50  % (12180)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f988,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f195,f200,f205,f210,f218,f224,f261,f267,f327,f443,f537,f570,f593,f595,f615,f733,f734,f748,f759,f787,f978,f987])).
% 0.22/0.50  fof(f987,plain,(
% 0.22/0.50    ~spl14_51 | ~spl14_64 | ~spl14_67 | ~spl14_69 | spl14_89),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f986])).
% 0.22/0.50  fof(f986,plain,(
% 0.22/0.50    $false | (~spl14_51 | ~spl14_64 | ~spl14_67 | ~spl14_69 | spl14_89)),
% 0.22/0.50    inference(subsumption_resolution,[],[f979,f778])).
% 0.22/0.50  fof(f778,plain,(
% 0.22/0.50    m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK7))) | ~spl14_69),
% 0.22/0.50    inference(avatar_component_clause,[],[f776])).
% 0.22/0.50  fof(f776,plain,(
% 0.22/0.50    spl14_69 <=> m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK7)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_69])])).
% 0.22/0.50  fof(f979,plain,(
% 0.22/0.50    ~m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK7))) | (~spl14_51 | ~spl14_64 | ~spl14_67 | spl14_89)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f591,f752,f725,f959,f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X2,X7,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~r1_tarski(X5,u1_struct_0(X2)) | sP12(X3,X2,X7)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f112_D])).
% 0.22/0.50  fof(f112_D,plain,(
% 0.22/0.50    ( ! [X7,X2,X3] : (( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~r1_tarski(X5,u1_struct_0(X2))) ) <=> ~sP12(X3,X2,X7)) )),
% 0.22/0.50    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).
% 0.22/0.50  fof(f959,plain,(
% 0.22/0.50    ~sP12(sK7,sK6,sK9) | spl14_89),
% 0.22/0.50    inference(avatar_component_clause,[],[f957])).
% 0.22/0.50  fof(f957,plain,(
% 0.22/0.50    spl14_89 <=> sP12(sK7,sK6,sK9)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_89])])).
% 0.22/0.50  fof(f725,plain,(
% 0.22/0.50    r1_tarski(sK11(sK6,sK9,k1_xboole_0),u1_struct_0(sK6)) | ~spl14_64),
% 0.22/0.50    inference(avatar_component_clause,[],[f723])).
% 0.22/0.50  fof(f723,plain,(
% 0.22/0.50    spl14_64 <=> r1_tarski(sK11(sK6,sK9,k1_xboole_0),u1_struct_0(sK6))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_64])])).
% 0.22/0.50  fof(f752,plain,(
% 0.22/0.50    v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK7) | ~spl14_67),
% 0.22/0.50    inference(avatar_component_clause,[],[f750])).
% 0.22/0.50  fof(f750,plain,(
% 0.22/0.50    spl14_67 <=> v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK7)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_67])])).
% 0.22/0.50  fof(f591,plain,(
% 0.22/0.50    r2_hidden(sK9,sK11(sK6,sK9,k1_xboole_0)) | ~spl14_51),
% 0.22/0.50    inference(avatar_component_clause,[],[f589])).
% 0.22/0.50  fof(f589,plain,(
% 0.22/0.50    spl14_51 <=> r2_hidden(sK9,sK11(sK6,sK9,k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_51])])).
% 0.22/0.50  fof(f978,plain,(
% 0.22/0.50    ~spl14_89 | spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | spl14_13 | ~spl14_14 | ~spl14_15 | spl14_16 | ~spl14_17 | ~spl14_18 | spl14_19 | ~spl14_20 | ~spl14_21 | ~spl14_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f977,f440,f221,f215,f207,f202,f197,f192,f187,f182,f177,f172,f167,f162,f157,f152,f147,f137,f117,f957])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl14_1 <=> r1_tmap_1(sK7,sK5,sK8,sK9)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    spl14_5 <=> m1_subset_1(sK9,u1_struct_0(sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    spl14_7 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    spl14_8 <=> v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl14_9 <=> v1_funct_1(sK8)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    spl14_10 <=> m1_pre_topc(sK7,sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl14_11 <=> v2_struct_0(sK7)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    spl14_12 <=> m1_pre_topc(sK6,sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    spl14_13 <=> v2_struct_0(sK6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    spl14_14 <=> l1_pre_topc(sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    spl14_15 <=> v2_pre_topc(sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    spl14_16 <=> v2_struct_0(sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl14_17 <=> l1_pre_topc(sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    spl14_18 <=> v2_pre_topc(sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    spl14_19 <=> v2_struct_0(sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    spl14_20 <=> m1_subset_1(sK9,u1_struct_0(sK6))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl14_21 <=> r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_21])])).
% 0.22/0.51  fof(f440,plain,(
% 0.22/0.51    spl14_39 <=> m1_pre_topc(sK6,sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_39])])).
% 0.22/0.51  fof(f977,plain,(
% 0.22/0.51    ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | spl14_13 | ~spl14_14 | ~spl14_15 | spl14_16 | ~spl14_17 | ~spl14_18 | spl14_19 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f976,f209])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    ~v2_struct_0(sK4) | spl14_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f207])).
% 0.22/0.51  % (12164)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  fof(f976,plain,(
% 0.22/0.51    v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | spl14_13 | ~spl14_14 | ~spl14_15 | spl14_16 | ~spl14_17 | ~spl14_18 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f975,f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    v2_pre_topc(sK4) | ~spl14_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f202])).
% 0.22/0.51  fof(f975,plain,(
% 0.22/0.51    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | spl14_13 | ~spl14_14 | ~spl14_15 | spl14_16 | ~spl14_17 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f974,f199])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    l1_pre_topc(sK4) | ~spl14_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f197])).
% 0.22/0.51  fof(f974,plain,(
% 0.22/0.51    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | spl14_13 | ~spl14_14 | ~spl14_15 | spl14_16 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f973,f194])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ~v2_struct_0(sK5) | spl14_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f192])).
% 0.22/0.51  fof(f973,plain,(
% 0.22/0.51    v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | spl14_13 | ~spl14_14 | ~spl14_15 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f972,f189])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    v2_pre_topc(sK5) | ~spl14_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f187])).
% 0.22/0.51  fof(f972,plain,(
% 0.22/0.51    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | spl14_13 | ~spl14_14 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f971,f184])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    l1_pre_topc(sK5) | ~spl14_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f182])).
% 0.22/0.51  fof(f971,plain,(
% 0.22/0.51    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | spl14_13 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f970,f179])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    ~v2_struct_0(sK6) | spl14_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f177])).
% 0.22/0.51  fof(f970,plain,(
% 0.22/0.51    v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_12 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f969,f174])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    m1_pre_topc(sK6,sK4) | ~spl14_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f172])).
% 0.22/0.51  fof(f969,plain,(
% 0.22/0.51    ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | spl14_11 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f968,f169])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ~v2_struct_0(sK7) | spl14_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f167])).
% 0.22/0.51  fof(f968,plain,(
% 0.22/0.51    v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_10 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f967,f164])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    m1_pre_topc(sK7,sK4) | ~spl14_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f162])).
% 0.22/0.51  fof(f967,plain,(
% 0.22/0.51    ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_9 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f966,f159])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    v1_funct_1(sK8) | ~spl14_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f157])).
% 0.22/0.51  fof(f966,plain,(
% 0.22/0.51    ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_8 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f965,f154])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) | ~spl14_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f152])).
% 0.22/0.51  fof(f965,plain,(
% 0.22/0.51    ~v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_7 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f964,f149])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~spl14_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f147])).
% 0.22/0.51  fof(f964,plain,(
% 0.22/0.51    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_20 | ~spl14_21 | ~spl14_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f963,f442])).
% 0.22/0.51  fof(f442,plain,(
% 0.22/0.51    m1_pre_topc(sK6,sK7) | ~spl14_39),
% 0.22/0.51    inference(avatar_component_clause,[],[f440])).
% 0.22/0.51  % (12165)Refutation not found, incomplete strategy% (12165)------------------------------
% 0.22/0.51  % (12165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12165)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12165)Memory used [KB]: 10746
% 0.22/0.51  % (12165)Time elapsed: 0.092 s
% 0.22/0.51  % (12165)------------------------------
% 0.22/0.51  % (12165)------------------------------
% 0.22/0.51  fof(f963,plain,(
% 0.22/0.51    ~m1_pre_topc(sK6,sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_5 | ~spl14_20 | ~spl14_21)),
% 0.22/0.51    inference(subsumption_resolution,[],[f962,f139])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    m1_subset_1(sK9,u1_struct_0(sK7)) | ~spl14_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f137])).
% 0.22/0.51  fof(f962,plain,(
% 0.22/0.51    ~m1_subset_1(sK9,u1_struct_0(sK7)) | ~m1_pre_topc(sK6,sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_20 | ~spl14_21)),
% 0.22/0.51    inference(subsumption_resolution,[],[f961,f217])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    m1_subset_1(sK9,u1_struct_0(sK6)) | ~spl14_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f215])).
% 0.22/0.51  fof(f961,plain,(
% 0.22/0.51    ~m1_subset_1(sK9,u1_struct_0(sK6)) | ~m1_subset_1(sK9,u1_struct_0(sK7)) | ~m1_pre_topc(sK6,sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | (spl14_1 | ~spl14_21)),
% 0.22/0.51    inference(subsumption_resolution,[],[f955,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ~r1_tmap_1(sK7,sK5,sK8,sK9) | spl14_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f955,plain,(
% 0.22/0.51    r1_tmap_1(sK7,sK5,sK8,sK9) | ~m1_subset_1(sK9,u1_struct_0(sK6)) | ~m1_subset_1(sK9,u1_struct_0(sK7)) | ~m1_pre_topc(sK6,sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP12(sK7,sK6,sK9) | ~spl14_21),
% 0.22/0.51    inference(resolution,[],[f113,f223])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) | ~spl14_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f221])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP12(X3,X2,X7)) )),
% 0.22/0.51    inference(general_splitting,[],[f110,f112_D])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.22/0.51  fof(f787,plain,(
% 0.22/0.51    spl14_69 | ~spl14_6 | ~spl14_66),
% 0.22/0.51    inference(avatar_split_clause,[],[f763,f745,f142,f776])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    spl14_6 <=> g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 0.22/0.51  fof(f745,plain,(
% 0.22/0.51    spl14_66 <=> sP3(sK6,sK11(sK6,sK9,k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_66])])).
% 0.22/0.51  fof(f763,plain,(
% 0.22/0.51    m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK7))) | (~spl14_6 | ~spl14_66)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f747,f401])).
% 0.22/0.51  fof(f401,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) | ~sP3(sK6,X0)) ) | ~spl14_6),
% 0.22/0.51    inference(superposition,[],[f97,f144])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 | ~spl14_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f142])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~sP3(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP3(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~sP3(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP3(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~sP3(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : (sP3(X0,X1) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.51  fof(f747,plain,(
% 0.22/0.51    sP3(sK6,sK11(sK6,sK9,k1_xboole_0)) | ~spl14_66),
% 0.22/0.51    inference(avatar_component_clause,[],[f745])).
% 0.22/0.51  fof(f759,plain,(
% 0.22/0.51    spl14_67 | ~spl14_6 | ~spl14_24 | ~spl14_30 | ~spl14_65),
% 0.22/0.51    inference(avatar_split_clause,[],[f742,f728,f313,f249,f142,f750])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    spl14_24 <=> l1_pre_topc(sK6)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    spl14_30 <=> v2_pre_topc(sK6)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).
% 0.22/0.51  fof(f728,plain,(
% 0.22/0.51    spl14_65 <=> sP2(sK6,sK11(sK6,sK9,k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_65])])).
% 0.22/0.51  fof(f742,plain,(
% 0.22/0.51    v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK7) | (~spl14_6 | ~spl14_24 | ~spl14_30 | ~spl14_65)),
% 0.22/0.51    inference(resolution,[],[f730,f333])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    ( ! [X0] : (~sP2(sK6,X0) | v3_pre_topc(X0,sK7)) ) | (~spl14_6 | ~spl14_24 | ~spl14_30)),
% 0.22/0.51    inference(subsumption_resolution,[],[f332,f315])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    v2_pre_topc(sK6) | ~spl14_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f313])).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    ( ! [X0] : (~sP2(sK6,X0) | ~v2_pre_topc(sK6) | v3_pre_topc(X0,sK7)) ) | (~spl14_6 | ~spl14_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f331,f251])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    l1_pre_topc(sK6) | ~spl14_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f249])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    ( ! [X0] : (~sP2(sK6,X0) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v3_pre_topc(X0,sK7)) ) | ~spl14_6),
% 0.22/0.51    inference(resolution,[],[f102,f330])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    ( ! [X0] : (~sP3(sK6,X0) | v3_pre_topc(X0,sK7)) ) | ~spl14_6),
% 0.22/0.51    inference(superposition,[],[f96,f144])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP3(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f55])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP3(X0,X1) | ~sP2(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((sP2(X0,X1) | ~sP3(X0,X1)) & (sP3(X0,X1) | ~sP2(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (sP2(X0,X1) <=> sP3(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(definition_folding,[],[f27,f35,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (sP2(X0,X1) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).
% 0.22/0.51  fof(f730,plain,(
% 0.22/0.51    sP2(sK6,sK11(sK6,sK9,k1_xboole_0)) | ~spl14_65),
% 0.22/0.51    inference(avatar_component_clause,[],[f728])).
% 0.22/0.51  fof(f748,plain,(
% 0.22/0.51    spl14_66 | ~spl14_24 | ~spl14_30 | ~spl14_65),
% 0.22/0.51    inference(avatar_split_clause,[],[f738,f728,f313,f249,f745])).
% 0.22/0.51  fof(f738,plain,(
% 0.22/0.51    sP3(sK6,sK11(sK6,sK9,k1_xboole_0)) | (~spl14_24 | ~spl14_30 | ~spl14_65)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f315,f251,f730,f102])).
% 0.22/0.51  fof(f734,plain,(
% 0.22/0.51    spl14_64 | ~spl14_53),
% 0.22/0.51    inference(avatar_split_clause,[],[f721,f612,f723])).
% 0.22/0.51  fof(f612,plain,(
% 0.22/0.51    spl14_53 <=> m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK6)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_53])])).
% 0.22/0.51  fof(f721,plain,(
% 0.22/0.51    r1_tarski(sK11(sK6,sK9,k1_xboole_0),u1_struct_0(sK6)) | ~spl14_53),
% 0.22/0.51    inference(resolution,[],[f614,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f614,plain,(
% 0.22/0.51    m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK6))) | ~spl14_53),
% 0.22/0.51    inference(avatar_component_clause,[],[f612])).
% 0.22/0.51  fof(f733,plain,(
% 0.22/0.51    spl14_65 | ~spl14_49 | ~spl14_53),
% 0.22/0.51    inference(avatar_split_clause,[],[f732,f612,f579,f728])).
% 0.22/0.51  fof(f579,plain,(
% 0.22/0.51    spl14_49 <=> v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK6)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_49])])).
% 0.22/0.51  fof(f732,plain,(
% 0.22/0.51    sP2(sK6,sK11(sK6,sK9,k1_xboole_0)) | (~spl14_49 | ~spl14_53)),
% 0.22/0.51    inference(subsumption_resolution,[],[f719,f581])).
% 0.22/0.51  fof(f581,plain,(
% 0.22/0.51    v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK6) | ~spl14_49),
% 0.22/0.51    inference(avatar_component_clause,[],[f579])).
% 0.22/0.51  fof(f719,plain,(
% 0.22/0.51    sP2(sK6,sK11(sK6,sK9,k1_xboole_0)) | ~v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK6) | ~spl14_53),
% 0.22/0.51    inference(resolution,[],[f614,f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X0,X1) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~sP2(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~sP2(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f34])).
% 0.22/0.51  fof(f615,plain,(
% 0.22/0.51    spl14_53 | spl14_13 | ~spl14_20 | ~spl14_24 | ~spl14_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f607,f313,f249,f215,f177,f612])).
% 0.22/0.51  fof(f607,plain,(
% 0.22/0.51    m1_subset_1(sK11(sK6,sK9,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK6))) | (spl14_13 | ~spl14_20 | ~spl14_24 | ~spl14_30)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f179,f315,f251,f217,f212])).
% 0.22/0.51  % (12164)Refutation not found, incomplete strategy% (12164)------------------------------
% 0.22/0.51  % (12164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(sK11(X0,X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f109,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(sK11(X0,X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  % (12164)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12164)Memory used [KB]: 6268
% 0.22/0.51  % (12164)Time elapsed: 0.073 s
% 0.22/0.51  % (12164)------------------------------
% 0.22/0.51  % (12164)------------------------------
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k1_xboole_0 != X2 | (sP1(X0,X1,sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f33,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (sP1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (sP1(X0,X1,sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k1_xboole_0 != X2 | ? [X3] : (sP1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(definition_folding,[],[f21,f32,f31])).
% 0.22/0.51  % (12182)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X3,X2] : ((r2_hidden(X3,X2) <~> sP0(X3,X1,X0)) | ~sP1(X0,X1,X3,X2))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k1_xboole_0 != X2 | ? [X3] : ((r2_hidden(X3,X2) <~> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_xboole_0 != X2 | ? [X3] : ((r2_hidden(X3,X2) <~> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.22/0.51  fof(f595,plain,(
% 0.22/0.51    spl14_49 | ~spl14_48),
% 0.22/0.51    inference(avatar_split_clause,[],[f577,f565,f579])).
% 0.22/0.51  fof(f565,plain,(
% 0.22/0.51    spl14_48 <=> sP0(sK11(sK6,sK9,k1_xboole_0),sK9,sK6)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).
% 0.22/0.51  fof(f577,plain,(
% 0.22/0.51    v3_pre_topc(sK11(sK6,sK9,k1_xboole_0),sK6) | ~spl14_48),
% 0.22/0.51    inference(resolution,[],[f567,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v3_pre_topc(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~v4_pre_topc(X0,X2) | ~v3_pre_topc(X0,X2)) & ((r2_hidden(X1,X0) & v4_pre_topc(X0,X2) & v3_pre_topc(X0,X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~sP0(X3,X1,X0)))),
% 0.22/0.51    inference(flattening,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~sP0(X3,X1,X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f31])).
% 0.22/0.51  fof(f567,plain,(
% 0.22/0.51    sP0(sK11(sK6,sK9,k1_xboole_0),sK9,sK6) | ~spl14_48),
% 0.22/0.51    inference(avatar_component_clause,[],[f565])).
% 0.22/0.51  fof(f593,plain,(
% 0.22/0.51    spl14_51 | ~spl14_48),
% 0.22/0.51    inference(avatar_split_clause,[],[f575,f565,f589])).
% 0.22/0.51  fof(f575,plain,(
% 0.22/0.51    r2_hidden(sK9,sK11(sK6,sK9,k1_xboole_0)) | ~spl14_48),
% 0.22/0.51    inference(resolution,[],[f567,f89])).
% 0.22/0.51  % (12172)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f50])).
% 0.22/0.51  fof(f570,plain,(
% 0.22/0.51    spl14_48 | ~spl14_46),
% 0.22/0.51    inference(avatar_split_clause,[],[f569,f534,f565])).
% 0.22/0.51  fof(f534,plain,(
% 0.22/0.51    spl14_46 <=> sP1(sK6,sK9,sK11(sK6,sK9,k1_xboole_0),k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_46])])).
% 0.22/0.51  fof(f569,plain,(
% 0.22/0.51    sP0(sK11(sK6,sK9,k1_xboole_0),sK9,sK6) | ~spl14_46),
% 0.22/0.51    inference(subsumption_resolution,[],[f563,f237])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f79,f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f563,plain,(
% 0.22/0.51    r2_hidden(sK11(sK6,sK9,k1_xboole_0),k1_xboole_0) | sP0(sK11(sK6,sK9,k1_xboole_0),sK9,sK6) | ~spl14_46),
% 0.22/0.51    inference(resolution,[],[f536,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r2_hidden(X2,X3) | sP0(X2,X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (((~sP0(X2,X1,X0) | ~r2_hidden(X2,X3)) & (sP0(X2,X1,X0) | r2_hidden(X2,X3))) | ~sP1(X0,X1,X2,X3))),
% 0.22/0.51    inference(rectify,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0,X1,X3,X2] : (((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) | ~sP1(X0,X1,X3,X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f32])).
% 0.22/0.51  fof(f536,plain,(
% 0.22/0.51    sP1(sK6,sK9,sK11(sK6,sK9,k1_xboole_0),k1_xboole_0) | ~spl14_46),
% 0.22/0.51    inference(avatar_component_clause,[],[f534])).
% 0.22/0.51  fof(f537,plain,(
% 0.22/0.51    spl14_46 | spl14_13 | ~spl14_20 | ~spl14_24 | ~spl14_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f530,f313,f249,f215,f177,f534])).
% 0.22/0.51  fof(f530,plain,(
% 0.22/0.51    sP1(sK6,sK9,sK11(sK6,sK9,k1_xboole_0),k1_xboole_0) | (spl14_13 | ~spl14_20 | ~spl14_24 | ~spl14_30)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f179,f315,f251,f217,f211])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP1(X0,X1,sK11(X0,X1,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f80])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP1(X0,X1,sK11(X0,X1,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | sP1(X0,X1,sK11(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  fof(f443,plain,(
% 0.22/0.51    spl14_39 | ~spl14_6 | ~spl14_24 | ~spl14_26),
% 0.22/0.51    inference(avatar_split_clause,[],[f438,f264,f249,f142,f440])).
% 0.22/0.51  fof(f264,plain,(
% 0.22/0.51    spl14_26 <=> m1_pre_topc(sK6,sK6)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).
% 0.22/0.51  fof(f438,plain,(
% 0.22/0.51    m1_pre_topc(sK6,sK7) | (~spl14_6 | ~spl14_24 | ~spl14_26)),
% 0.22/0.51    inference(forward_demodulation,[],[f428,f144])).
% 0.22/0.51  fof(f428,plain,(
% 0.22/0.51    m1_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | (~spl14_24 | ~spl14_26)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f251,f251,f266,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    m1_pre_topc(sK6,sK6) | ~spl14_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f264])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    spl14_30 | ~spl14_12 | ~spl14_17 | ~spl14_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f326,f202,f197,f172,f313])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    v2_pre_topc(sK6) | (~spl14_12 | ~spl14_17 | ~spl14_18)),
% 0.22/0.51    inference(subsumption_resolution,[],[f325,f204])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    v2_pre_topc(sK6) | ~v2_pre_topc(sK4) | (~spl14_12 | ~spl14_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f306,f199])).
% 0.22/0.51  fof(f306,plain,(
% 0.22/0.51    v2_pre_topc(sK6) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~spl14_12),
% 0.22/0.51    inference(resolution,[],[f95,f174])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.51  fof(f267,plain,(
% 0.22/0.51    spl14_26 | ~spl14_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f262,f249,f264])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    m1_pre_topc(sK6,sK6) | ~spl14_24),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f251,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    spl14_24 | ~spl14_12 | ~spl14_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f260,f197,f172,f249])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    l1_pre_topc(sK6) | (~spl14_12 | ~spl14_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f243,f199])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    l1_pre_topc(sK6) | ~l1_pre_topc(sK4) | ~spl14_12),
% 0.22/0.51    inference(resolution,[],[f84,f174])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    spl14_21 | ~spl14_2 | ~spl14_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f219,f127,f122,f221])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    spl14_2 <=> r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl14_3 <=> sK9 = sK10),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) | (~spl14_2 | ~spl14_3)),
% 0.22/0.51    inference(forward_demodulation,[],[f124,f129])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    sK9 = sK10 | ~spl14_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f127])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) | ~spl14_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f122])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    spl14_20 | ~spl14_3 | ~spl14_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f213,f132,f127,f215])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl14_4 <=> m1_subset_1(sK10,u1_struct_0(sK6))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    m1_subset_1(sK9,u1_struct_0(sK6)) | (~spl14_3 | ~spl14_4)),
% 0.22/0.51    inference(backward_demodulation,[],[f134,f129])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    m1_subset_1(sK10,u1_struct_0(sK6)) | ~spl14_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f132])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ~spl14_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f60,f207])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ~v2_struct_0(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ((((((~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f16,f43,f42,f41,f40,f39,f38,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (12168)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(sK4,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(sK4,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,sK5,X4,X5) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,sK5,X4,X5) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK7,sK5,sK8,X5) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ? [X5] : (? [X6] : (~r1_tmap_1(sK7,sK5,sK8,X5) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(sK7))) => (? [X6] : (~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ? [X6] : (~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) => (~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f13])).
% 0.22/0.51  % (12173)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  fof(f13,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl14_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f61,f202])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    v2_pre_topc(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    spl14_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f62,f197])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    l1_pre_topc(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    ~spl14_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f63,f192])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ~v2_struct_0(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    spl14_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f64,f187])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    v2_pre_topc(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    spl14_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f65,f182])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    l1_pre_topc(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ~spl14_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f66,f177])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ~v2_struct_0(sK6)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    spl14_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f67,f172])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    m1_pre_topc(sK6,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ~spl14_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f68,f167])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ~v2_struct_0(sK7)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl14_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f69,f162])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    m1_pre_topc(sK7,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl14_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f70,f157])).
% 0.22/0.51  % (12171)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    v1_funct_1(sK8)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    spl14_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f71,f152])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    spl14_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f72,f147])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    spl14_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f73,f142])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    spl14_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f74,f137])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    m1_subset_1(sK9,u1_struct_0(sK7))),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl14_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f75,f132])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    m1_subset_1(sK10,u1_struct_0(sK6))),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    spl14_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f76,f127])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    sK9 = sK10),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl14_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f77,f122])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ~spl14_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f78,f117])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ~r1_tmap_1(sK7,sK5,sK8,sK9)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (12180)------------------------------
% 0.22/0.51  % (12180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12180)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (12180)Memory used [KB]: 11385
% 0.22/0.51  % (12180)Time elapsed: 0.090 s
% 0.22/0.51  % (12180)------------------------------
% 0.22/0.51  % (12180)------------------------------
% 0.22/0.51  % (12163)Success in time 0.152 s
%------------------------------------------------------------------------------
