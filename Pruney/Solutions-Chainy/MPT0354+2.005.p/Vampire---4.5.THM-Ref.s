%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 228 expanded)
%              Number of leaves         :   35 ( 114 expanded)
%              Depth                    :    6
%              Number of atoms          :  335 ( 578 expanded)
%              Number of equality atoms :   78 ( 147 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f50,f54,f58,f62,f66,f70,f74,f87,f97,f117,f123,f140,f162,f179,f214,f234,f340,f386,f400,f1160,f1201,f1207,f1210])).

fof(f1210,plain,
    ( spl3_61
    | ~ spl3_183
    | ~ spl3_184 ),
    inference(avatar_contradiction_clause,[],[f1209])).

fof(f1209,plain,
    ( $false
    | spl3_61
    | ~ spl3_183
    | ~ spl3_184 ),
    inference(subsumption_resolution,[],[f1208,f399])).

fof(f399,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | spl3_61 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl3_61
  <=> k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f1208,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_183
    | ~ spl3_184 ),
    inference(forward_demodulation,[],[f1200,f1206])).

fof(f1206,plain,
    ( k4_xboole_0(sK1,sK2) = k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | ~ spl3_184 ),
    inference(avatar_component_clause,[],[f1204])).

fof(f1204,plain,
    ( spl3_184
  <=> k4_xboole_0(sK1,sK2) = k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_184])])).

fof(f1200,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)))
    | ~ spl3_183 ),
    inference(avatar_component_clause,[],[f1198])).

fof(f1198,plain,
    ( spl3_183
  <=> k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_183])])).

fof(f1207,plain,
    ( spl3_184
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_176 ),
    inference(avatar_split_clause,[],[f1202,f1157,f177,f52,f1204])).

% (30942)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f52,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f177,plain,
    ( spl3_26
  <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1157,plain,
    ( spl3_176
  <=> m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_176])])).

fof(f1202,plain,
    ( k4_xboole_0(sK1,sK2) = k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_176 ),
    inference(forward_demodulation,[],[f1168,f178])).

fof(f178,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK1,X0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1168,plain,
    ( k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | ~ spl3_5
    | ~ spl3_176 ),
    inference(resolution,[],[f1159,f53])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f1159,plain,
    ( m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0))
    | ~ spl3_176 ),
    inference(avatar_component_clause,[],[f1157])).

fof(f1201,plain,
    ( spl3_183
    | ~ spl3_6
    | ~ spl3_176 ),
    inference(avatar_split_clause,[],[f1167,f1157,f56,f1198])).

fof(f56,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1167,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)))
    | ~ spl3_6
    | ~ spl3_176 ),
    inference(resolution,[],[f1159,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f1160,plain,
    ( spl3_176
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f1155,f383,f114,f68,f38,f1157])).

fof(f38,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f114,plain,
    ( spl3_17
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f383,plain,
    ( spl3_58
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f1155,plain,
    ( m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f1154,f116])).

fof(f116,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1154,plain,
    ( m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f1153,f40])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f1153,plain,
    ( m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_9
    | ~ spl3_58 ),
    inference(superposition,[],[f69,f385])).

fof(f385,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f383])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f400,plain,
    ( ~ spl3_61
    | spl3_36
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f395,f383,f231,f397])).

fof(f231,plain,
    ( spl3_36
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f395,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | spl3_36
    | ~ spl3_58 ),
    inference(backward_demodulation,[],[f233,f385])).

fof(f233,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k3_subset_1(sK0,k4_xboole_0(sK1,sK2))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f231])).

fof(f386,plain,
    ( spl3_58
    | ~ spl3_17
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f364,f338,f114,f383])).

fof(f338,plain,
    ( spl3_49
  <=> ! [X0] :
        ( k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f364,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_17
    | ~ spl3_49 ),
    inference(resolution,[],[f339,f116])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f338])).

fof(f340,plain,
    ( spl3_49
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f331,f72,f38,f338])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f331,plain,
    ( ! [X0] :
        ( k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f73,f40])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f234,plain,
    ( ~ spl3_36
    | spl3_14
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f229,f212,f94,f231])).

fof(f94,plain,
    ( spl3_14
  <=> k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f212,plain,
    ( spl3_32
  <=> ! [X1] : k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f229,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k3_subset_1(sK0,k4_xboole_0(sK1,sK2))
    | spl3_14
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f96,f213])).

fof(f213,plain,
    ( ! [X1] : k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f212])).

fof(f96,plain,
    ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f214,plain,
    ( spl3_32
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f203,f64,f43,f212])).

fof(f43,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f203,plain,
    ( ! [X1] : k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f65,f45])).

fof(f45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f179,plain,
    ( spl3_26
    | ~ spl3_7
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f173,f159,f60,f177])).

fof(f60,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f159,plain,
    ( spl3_24
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f173,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK1,X0)
    | ~ spl3_7
    | ~ spl3_24 ),
    inference(superposition,[],[f61,f161])).

fof(f161,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f159])).

fof(f61,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f162,plain,
    ( spl3_24
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f157,f137,f120,f159])).

fof(f120,plain,
    ( spl3_18
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f137,plain,
    ( spl3_20
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f157,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f122,f139])).

fof(f139,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f137])).

fof(f122,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f140,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f135,f84,f56,f43,f137])).

fof(f84,plain,
    ( spl3_12
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f135,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f125,f86])).

fof(f86,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f125,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f57,f45])).

fof(f123,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f118,f114,f52,f120])).

fof(f118,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(resolution,[],[f116,f53])).

fof(f117,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f112,f84,f48,f43,f114])).

fof(f48,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f112,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f111,f45])).

fof(f111,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f49,f86])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f97,plain,
    ( ~ spl3_14
    | spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f92,f84,f33,f94])).

fof(f33,plain,
    ( spl3_1
  <=> k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f92,plain,
    ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)
    | spl3_1
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f35,f86])).

fof(f35,plain,
    ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f87,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f76,f52,f43,f84])).

fof(f76,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f53,f45])).

fof(f74,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f70,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f66,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f62,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f58,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f54,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f38])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f33])).

fof(f24,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (30945)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (30951)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  % (30941)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (30948)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.44  % (30944)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.45  % (30950)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.45  % (30943)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.46  % (30947)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.46  % (30946)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  % (30949)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.46  % (30950)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f1223,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f36,f41,f46,f50,f54,f58,f62,f66,f70,f74,f87,f97,f117,f123,f140,f162,f179,f214,f234,f340,f386,f400,f1160,f1201,f1207,f1210])).
% 0.21/0.46  fof(f1210,plain,(
% 0.21/0.46    spl3_61 | ~spl3_183 | ~spl3_184),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f1209])).
% 0.21/0.46  fof(f1209,plain,(
% 0.21/0.46    $false | (spl3_61 | ~spl3_183 | ~spl3_184)),
% 0.21/0.46    inference(subsumption_resolution,[],[f1208,f399])).
% 0.21/0.46  fof(f399,plain,(
% 0.21/0.46    k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | spl3_61),
% 0.21/0.46    inference(avatar_component_clause,[],[f397])).
% 0.21/0.46  fof(f397,plain,(
% 0.21/0.46    spl3_61 <=> k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.21/0.46  fof(f1208,plain,(
% 0.21/0.46    k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | (~spl3_183 | ~spl3_184)),
% 0.21/0.46    inference(forward_demodulation,[],[f1200,f1206])).
% 0.21/0.46  fof(f1206,plain,(
% 0.21/0.46    k4_xboole_0(sK1,sK2) = k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) | ~spl3_184),
% 0.21/0.46    inference(avatar_component_clause,[],[f1204])).
% 0.21/0.46  fof(f1204,plain,(
% 0.21/0.46    spl3_184 <=> k4_xboole_0(sK1,sK2) = k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_184])])).
% 0.21/0.46  fof(f1200,plain,(
% 0.21/0.46    k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))) | ~spl3_183),
% 0.21/0.46    inference(avatar_component_clause,[],[f1198])).
% 0.21/0.46  fof(f1198,plain,(
% 0.21/0.46    spl3_183 <=> k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_183])])).
% 0.21/0.46  fof(f1207,plain,(
% 0.21/0.46    spl3_184 | ~spl3_5 | ~spl3_26 | ~spl3_176),
% 0.21/0.46    inference(avatar_split_clause,[],[f1202,f1157,f177,f52,f1204])).
% 0.21/0.46  % (30942)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl3_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    spl3_26 <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK1,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.46  fof(f1157,plain,(
% 0.21/0.46    spl3_176 <=> m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_176])])).
% 0.21/0.46  fof(f1202,plain,(
% 0.21/0.46    k4_xboole_0(sK1,sK2) = k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) | (~spl3_5 | ~spl3_26 | ~spl3_176)),
% 0.21/0.46    inference(forward_demodulation,[],[f1168,f178])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK1,X0)) ) | ~spl3_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f177])).
% 0.21/0.46  fof(f1168,plain,(
% 0.21/0.46    k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) | (~spl3_5 | ~spl3_176)),
% 0.21/0.46    inference(resolution,[],[f1159,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  fof(f1159,plain,(
% 0.21/0.46    m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0)) | ~spl3_176),
% 0.21/0.46    inference(avatar_component_clause,[],[f1157])).
% 0.21/0.46  fof(f1201,plain,(
% 0.21/0.46    spl3_183 | ~spl3_6 | ~spl3_176),
% 0.21/0.46    inference(avatar_split_clause,[],[f1167,f1157,f56,f1198])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl3_6 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f1167,plain,(
% 0.21/0.46    k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))) | (~spl3_6 | ~spl3_176)),
% 0.21/0.46    inference(resolution,[],[f1159,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f56])).
% 0.21/0.46  fof(f1160,plain,(
% 0.21/0.46    spl3_176 | ~spl3_2 | ~spl3_9 | ~spl3_17 | ~spl3_58),
% 0.21/0.46    inference(avatar_split_clause,[],[f1155,f383,f114,f68,f38,f1157])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    spl3_9 <=> ! [X1,X0,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    spl3_17 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f383,plain,(
% 0.21/0.46    spl3_58 <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.21/0.46  fof(f1155,plain,(
% 0.21/0.46    m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_9 | ~spl3_17 | ~spl3_58)),
% 0.21/0.46    inference(subsumption_resolution,[],[f1154,f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f114])).
% 0.21/0.46  fof(f1154,plain,(
% 0.21/0.46    m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_9 | ~spl3_58)),
% 0.21/0.46    inference(subsumption_resolution,[],[f1153,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f38])).
% 0.21/0.46  fof(f1153,plain,(
% 0.21/0.46    m1_subset_1(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_9 | ~spl3_58)),
% 0.21/0.46    inference(superposition,[],[f69,f385])).
% 0.21/0.46  fof(f385,plain,(
% 0.21/0.46    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_58),
% 0.21/0.46    inference(avatar_component_clause,[],[f383])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f68])).
% 0.21/0.46  fof(f400,plain,(
% 0.21/0.46    ~spl3_61 | spl3_36 | ~spl3_58),
% 0.21/0.46    inference(avatar_split_clause,[],[f395,f383,f231,f397])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    spl3_36 <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k3_subset_1(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.46  fof(f395,plain,(
% 0.21/0.46    k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | (spl3_36 | ~spl3_58)),
% 0.21/0.46    inference(backward_demodulation,[],[f233,f385])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) | spl3_36),
% 0.21/0.46    inference(avatar_component_clause,[],[f231])).
% 0.21/0.46  fof(f386,plain,(
% 0.21/0.46    spl3_58 | ~spl3_17 | ~spl3_49),
% 0.21/0.46    inference(avatar_split_clause,[],[f364,f338,f114,f383])).
% 0.21/0.46  fof(f338,plain,(
% 0.21/0.46    spl3_49 <=> ! [X0] : (k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.46  fof(f364,plain,(
% 0.21/0.46    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | (~spl3_17 | ~spl3_49)),
% 0.21/0.46    inference(resolution,[],[f339,f116])).
% 0.21/0.46  fof(f339,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2)) ) | ~spl3_49),
% 0.21/0.46    inference(avatar_component_clause,[],[f338])).
% 0.21/0.46  fof(f340,plain,(
% 0.21/0.46    spl3_49 | ~spl3_2 | ~spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f331,f72,f38,f338])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl3_10 <=> ! [X1,X0,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f331,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | (~spl3_2 | ~spl3_10)),
% 0.21/0.46    inference(resolution,[],[f73,f40])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f72])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ~spl3_36 | spl3_14 | ~spl3_32),
% 0.21/0.46    inference(avatar_split_clause,[],[f229,f212,f94,f231])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl3_14 <=> k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f212,plain,(
% 0.21/0.46    spl3_32 <=> ! [X1] : k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) | (spl3_14 | ~spl3_32)),
% 0.21/0.46    inference(backward_demodulation,[],[f96,f213])).
% 0.21/0.46  fof(f213,plain,(
% 0.21/0.46    ( ! [X1] : (k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl3_32),
% 0.21/0.46    inference(avatar_component_clause,[],[f212])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) | spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f94])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    spl3_32 | ~spl3_3 | ~spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f203,f64,f43,f212])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl3_8 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    ( ! [X1] : (k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)) ) | (~spl3_3 | ~spl3_8)),
% 0.21/0.46    inference(resolution,[],[f65,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f43])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) ) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f64])).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    spl3_26 | ~spl3_7 | ~spl3_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f173,f159,f60,f177])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl3_7 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    spl3_24 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK1,X0)) ) | (~spl3_7 | ~spl3_24)),
% 0.21/0.46    inference(superposition,[],[f61,f161])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f159])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f60])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    spl3_24 | ~spl3_18 | ~spl3_20),
% 0.21/0.46    inference(avatar_split_clause,[],[f157,f137,f120,f159])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    spl3_18 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    spl3_20 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_18 | ~spl3_20)),
% 0.21/0.46    inference(backward_demodulation,[],[f122,f139])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f137])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f120])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    spl3_20 | ~spl3_3 | ~spl3_6 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f135,f84,f56,f43,f137])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl3_12 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_3 | ~spl3_6 | ~spl3_12)),
% 0.21/0.46    inference(forward_demodulation,[],[f125,f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f84])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | (~spl3_3 | ~spl3_6)),
% 0.21/0.46    inference(resolution,[],[f57,f45])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    spl3_18 | ~spl3_5 | ~spl3_17),
% 0.21/0.46    inference(avatar_split_clause,[],[f118,f114,f52,f120])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_5 | ~spl3_17)),
% 0.21/0.46    inference(resolution,[],[f116,f53])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl3_17 | ~spl3_3 | ~spl3_4 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f112,f84,f48,f43,f114])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl3_4 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.46    inference(subsumption_resolution,[],[f111,f45])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_4 | ~spl3_12)),
% 0.21/0.46    inference(superposition,[],[f49,f86])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ~spl3_14 | spl3_1 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f92,f84,f33,f94])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    spl3_1 <=> k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) | (spl3_1 | ~spl3_12)),
% 0.21/0.46    inference(backward_demodulation,[],[f35,f86])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f33])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl3_12 | ~spl3_3 | ~spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f76,f52,f43,f84])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_5)),
% 0.21/0.46    inference(resolution,[],[f53,f45])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f72])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f68])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f64])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f60])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f56])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f52])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f48])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f43])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    (k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X2] : (k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f38])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f33])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (30950)------------------------------
% 0.21/0.46  % (30950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (30950)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (30950)Memory used [KB]: 6908
% 0.21/0.46  % (30950)Time elapsed: 0.051 s
% 0.21/0.46  % (30950)------------------------------
% 0.21/0.46  % (30950)------------------------------
% 0.21/0.47  % (30939)Success in time 0.108 s
%------------------------------------------------------------------------------
