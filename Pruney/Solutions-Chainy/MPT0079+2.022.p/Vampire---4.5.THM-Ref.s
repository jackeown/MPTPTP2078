%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:54 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 463 expanded)
%              Number of leaves         :   47 ( 193 expanded)
%              Depth                    :   10
%              Number of atoms          :  396 ( 830 expanded)
%              Number of equality atoms :  161 ( 445 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f100,f114,f120,f126,f148,f160,f166,f178,f183,f487,f511,f740,f744,f1011,f1016,f1085,f1103,f1119,f1189,f1238,f1250,f1311,f1316,f1378,f1379])).

fof(f1379,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK3)
    | sK0 != sK3
    | sK0 != k4_xboole_0(sK0,sK2)
    | sK2 != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2))
    | k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) != k4_xboole_0(sK1,sK0)
    | sK1 != k4_xboole_0(sK1,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1378,plain,
    ( spl6_81
    | ~ spl6_50
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f1374,f1307,f1112,f1376])).

fof(f1376,plain,
    ( spl6_81
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f1112,plain,
    ( spl6_50
  <=> sK3 = k2_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f1307,plain,
    ( spl6_71
  <=> k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f1374,plain,
    ( sK0 = sK3
    | ~ spl6_50
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f1373,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1373,plain,
    ( sK3 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_50
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f1367,f1113])).

fof(f1113,plain,
    ( sK3 = k2_xboole_0(sK0,sK3)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1367,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)
    | ~ spl6_71 ),
    inference(superposition,[],[f42,f1308])).

fof(f1308,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK0)
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f1307])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1316,plain,
    ( spl6_72
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f1312,f1236,f1314])).

fof(f1314,plain,
    ( spl6_72
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f1236,plain,
    ( spl6_62
  <=> sK0 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f1312,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f1300,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1300,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,sK3)
    | ~ spl6_62 ),
    inference(superposition,[],[f42,f1237])).

fof(f1237,plain,
    ( sK0 = k4_xboole_0(sK3,sK1)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f1311,plain,
    ( spl6_71
    | ~ spl6_12
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f1310,f1236,f176,f1307])).

fof(f176,plain,
    ( spl6_12
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f1310,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK0)
    | ~ spl6_12
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f1298,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f176])).

fof(f1298,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,sK0)
    | ~ spl6_62 ),
    inference(superposition,[],[f49,f1237])).

% (9274)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (9259)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (9283)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (9266)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (9275)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (9267)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (9254)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f40,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1250,plain,
    ( sK1 != k4_xboole_0(sK1,sK0)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) != k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1238,plain,
    ( spl6_62
    | ~ spl6_4
    | ~ spl6_41
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f1234,f1209,f1009,f66,f1236])).

fof(f66,plain,
    ( spl6_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1009,plain,
    ( spl6_41
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1209,plain,
    ( spl6_57
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f1234,plain,
    ( sK0 = k4_xboole_0(sK3,sK1)
    | ~ spl6_4
    | ~ spl6_41
    | ~ spl6_57 ),
    inference(forward_demodulation,[],[f1233,f34])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1233,plain,
    ( k4_xboole_0(sK3,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_41
    | ~ spl6_57 ),
    inference(forward_demodulation,[],[f1232,f1087])).

fof(f1087,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X1,sK3))
    | ~ spl6_4
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f1064,f285])).

fof(f285,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f284,f101])).

fof(f101,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f92,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f48,f34])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f92,plain,(
    ! [X8] : k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X8,X8) ),
    inference(superposition,[],[f43,f69])).

fof(f69,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f39,f35])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f284,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f264,f34])).

fof(f264,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)) ),
    inference(superposition,[],[f46,f48])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1064,plain,
    ( ! [X1] : k4_xboole_0(sK0,k2_xboole_0(X1,sK3)) = k4_xboole_0(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,X1)))
    | ~ spl6_4
    | ~ spl6_41 ),
    inference(superposition,[],[f1047,f570])).

fof(f570,plain,
    ( ! [X0] : k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3))
    | ~ spl6_4 ),
    inference(superposition,[],[f471,f39])).

fof(f471,plain,
    ( ! [X28] : k2_xboole_0(sK2,k2_xboole_0(sK3,X28)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X28))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f438,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f438,plain,
    ( ! [X28] : k2_xboole_0(sK2,k2_xboole_0(sK3,X28)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X28)
    | ~ spl6_4 ),
    inference(superposition,[],[f47,f67])).

fof(f67,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f1047,plain,
    ( ! [X7] : k4_xboole_0(sK0,k2_xboole_0(sK2,X7)) = k4_xboole_0(sK0,X7)
    | ~ spl6_41 ),
    inference(superposition,[],[f46,f1010])).

fof(f1010,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1232,plain,
    ( k4_xboole_0(sK3,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)))
    | ~ spl6_57 ),
    inference(forward_demodulation,[],[f1210,f89])).

fof(f89,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f43,f39])).

fof(f1210,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK1)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f1209])).

fof(f1189,plain,
    ( spl6_52
    | ~ spl6_42
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f1185,f1101,f1014,f1187])).

fof(f1187,plain,
    ( spl6_52
  <=> sK1 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f1014,plain,
    ( spl6_42
  <=> sK1 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f1101,plain,
    ( spl6_49
  <=> sK3 = k2_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f1185,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl6_42
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f1163,f1015])).

fof(f1015,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f1163,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK0)
    | ~ spl6_42
    | ~ spl6_49 ),
    inference(superposition,[],[f1060,f1102])).

fof(f1102,plain,
    ( sK3 = k2_xboole_0(sK3,sK0)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f1060,plain,
    ( ! [X7] : k4_xboole_0(sK1,k2_xboole_0(sK3,X7)) = k4_xboole_0(sK1,X7)
    | ~ spl6_42 ),
    inference(superposition,[],[f46,f1015])).

fof(f1119,plain,
    ( spl6_50
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f1110,f1101,f1112])).

fof(f1110,plain,
    ( sK3 = k2_xboole_0(sK0,sK3)
    | ~ spl6_49 ),
    inference(superposition,[],[f39,f1102])).

fof(f1103,plain,
    ( spl6_49
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f1099,f1083,f1101])).

fof(f1083,plain,
    ( spl6_48
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f1099,plain,
    ( sK3 = k2_xboole_0(sK3,sK0)
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f1097,f35])).

fof(f1097,plain,
    ( k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_48 ),
    inference(superposition,[],[f42,f1084])).

fof(f1084,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK3)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1085,plain,
    ( spl6_48
    | ~ spl6_4
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f1081,f1009,f66,f1083])).

fof(f1081,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK3)
    | ~ spl6_4
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f1062,f285])).

fof(f1062,plain,
    ( k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_41 ),
    inference(superposition,[],[f1047,f67])).

fof(f1016,plain,
    ( spl6_42
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f1012,f176,f1014])).

fof(f1012,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f980,f34])).

fof(f980,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl6_12 ),
    inference(superposition,[],[f50,f177])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1011,plain,
    ( spl6_41
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f1007,f181,f1009])).

fof(f181,plain,
    ( spl6_13
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f1007,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f979,f34])).

fof(f979,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_13 ),
    inference(superposition,[],[f50,f182])).

fof(f182,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f744,plain,
    ( spl6_32
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f743,f164,f146,f723])).

fof(f723,plain,
    ( spl6_32
  <=> sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f146,plain,
    ( spl6_9
  <=> k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f164,plain,
    ( spl6_11
  <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f743,plain,
    ( sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2))
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f742,f34])).

fof(f742,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f689,f165])).

fof(f165,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f689,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2))
    | ~ spl6_9 ),
    inference(superposition,[],[f49,f147])).

fof(f147,plain,
    ( k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f740,plain,
    ( spl6_30
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f687,f509,f713])).

fof(f713,plain,
    ( spl6_30
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f509,plain,
    ( spl6_26
  <=> k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f687,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK0))
    | ~ spl6_26 ),
    inference(superposition,[],[f49,f510])).

fof(f510,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f509])).

fof(f511,plain,
    ( spl6_26
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f507,f476,f509])).

fof(f476,plain,
    ( spl6_23
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f507,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0)
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f497,f89])).

fof(f497,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)
    | ~ spl6_23 ),
    inference(superposition,[],[f89,f477])).

fof(f477,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f476])).

fof(f487,plain,
    ( spl6_23
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f450,f124,f476])).

fof(f124,plain,
    ( spl6_8
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f450,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))
    | ~ spl6_8 ),
    inference(superposition,[],[f125,f47])).

fof(f125,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f183,plain,
    ( spl6_13
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f179,f62,f181])).

fof(f62,plain,
    ( spl6_3
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f179,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl6_3 ),
    inference(resolution,[],[f173,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f173,plain,
    ( ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f171,f49])).

fof(f171,plain,
    ( ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))
    | ~ spl6_3 ),
    inference(resolution,[],[f51,f63])).

fof(f63,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f178,plain,
    ( spl6_12
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f174,f58,f176])).

fof(f58,plain,
    ( spl6_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f174,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl6_2 ),
    inference(resolution,[],[f172,f36])).

fof(f172,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f170,f49])).

fof(f170,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))
    | ~ spl6_2 ),
    inference(resolution,[],[f51,f59])).

fof(f59,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f166,plain,
    ( spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f162,f158,f164])).

fof(f158,plain,
    ( spl6_10
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f162,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f161,f77])).

fof(f161,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_10 ),
    inference(superposition,[],[f43,f159])).

fof(f159,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f160,plain,
    ( spl6_10
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f156,f146,f66,f158])).

fof(f156,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f155,f67])).

fof(f155,plain,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f154,f42])).

fof(f154,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))
    | ~ spl6_9 ),
    inference(superposition,[],[f42,f147])).

fof(f148,plain,
    ( spl6_9
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f137,f66,f146])).

fof(f137,plain,
    ( k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl6_4 ),
    inference(superposition,[],[f89,f67])).

fof(f126,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f122,f118,f124])).

fof(f118,plain,
    ( spl6_7
  <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f122,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f121,f35])).

fof(f121,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_7 ),
    inference(superposition,[],[f42,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f116,f112,f118])).

fof(f112,plain,
    ( spl6_6
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f116,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f115,f77])).

fof(f115,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(superposition,[],[f43,f113])).

fof(f113,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,
    ( spl6_6
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f110,f98,f66,f112])).

fof(f98,plain,
    ( spl6_5
  <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f110,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f109,f67])).

fof(f109,plain,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f108,f39])).

fof(f108,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f107,f42])).

fof(f107,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))
    | ~ spl6_5 ),
    inference(superposition,[],[f42,f99])).

fof(f99,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f88,f66,f98])).

fof(f88,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl6_4 ),
    inference(superposition,[],[f43,f67])).

fof(f68,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f64,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f54,plain,
    ( spl6_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f32,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (9263)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (9269)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (9271)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (9281)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (9279)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (9265)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (9277)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (9261)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (9273)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.57  % (9271)Refutation not found, incomplete strategy% (9271)------------------------------
% 0.22/0.57  % (9271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (9271)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (9271)Memory used [KB]: 10618
% 0.22/0.57  % (9271)Time elapsed: 0.131 s
% 0.22/0.57  % (9271)------------------------------
% 0.22/0.57  % (9271)------------------------------
% 0.22/0.57  % (9269)Refutation not found, incomplete strategy% (9269)------------------------------
% 0.22/0.57  % (9269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (9269)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (9269)Memory used [KB]: 6140
% 0.22/0.57  % (9269)Time elapsed: 0.003 s
% 0.22/0.57  % (9269)------------------------------
% 0.22/0.57  % (9269)------------------------------
% 0.22/0.60  % (9268)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.60  % (9270)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.60  % (9256)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.61  % (9272)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.61  % (9255)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.61  % (9264)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.61  % (9262)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.61  % (9260)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.62  % (9276)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.78/0.62  % (9278)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.78/0.62  % (9280)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.78/0.62  % (9257)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.78/0.62  % (9258)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.78/0.62  % (9282)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.78/0.62  % (9273)Refutation found. Thanks to Tanya!
% 1.78/0.62  % SZS status Theorem for theBenchmark
% 1.78/0.62  % SZS output start Proof for theBenchmark
% 1.78/0.62  fof(f1380,plain,(
% 1.78/0.62    $false),
% 1.78/0.62    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f100,f114,f120,f126,f148,f160,f166,f178,f183,f487,f511,f740,f744,f1011,f1016,f1085,f1103,f1119,f1189,f1238,f1250,f1311,f1316,f1378,f1379])).
% 1.78/0.62  fof(f1379,plain,(
% 1.78/0.62    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK3) | sK0 != sK3 | sK0 != k4_xboole_0(sK0,sK2) | sK2 != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) | k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) != k4_xboole_0(sK1,sK0) | sK1 != k4_xboole_0(sK1,sK0) | sK1 = sK2),
% 1.78/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.78/0.62  fof(f1378,plain,(
% 1.78/0.62    spl6_81 | ~spl6_50 | ~spl6_71),
% 1.78/0.62    inference(avatar_split_clause,[],[f1374,f1307,f1112,f1376])).
% 1.78/0.62  fof(f1376,plain,(
% 1.78/0.62    spl6_81 <=> sK0 = sK3),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 1.78/0.62  fof(f1112,plain,(
% 1.78/0.62    spl6_50 <=> sK3 = k2_xboole_0(sK0,sK3)),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 1.78/0.62  fof(f1307,plain,(
% 1.78/0.62    spl6_71 <=> k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 1.78/0.62  fof(f1374,plain,(
% 1.78/0.62    sK0 = sK3 | (~spl6_50 | ~spl6_71)),
% 1.78/0.62    inference(forward_demodulation,[],[f1373,f35])).
% 1.78/0.62  fof(f35,plain,(
% 1.78/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.78/0.62    inference(cnf_transformation,[],[f6])).
% 1.78/0.62  fof(f6,axiom,(
% 1.78/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.78/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.78/0.62  fof(f1373,plain,(
% 1.78/0.62    sK3 = k2_xboole_0(sK0,k1_xboole_0) | (~spl6_50 | ~spl6_71)),
% 1.78/0.62    inference(forward_demodulation,[],[f1367,f1113])).
% 1.78/0.62  fof(f1113,plain,(
% 1.78/0.62    sK3 = k2_xboole_0(sK0,sK3) | ~spl6_50),
% 1.78/0.62    inference(avatar_component_clause,[],[f1112])).
% 1.78/0.62  fof(f1367,plain,(
% 1.78/0.62    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) | ~spl6_71),
% 1.78/0.62    inference(superposition,[],[f42,f1308])).
% 1.78/0.62  fof(f1308,plain,(
% 1.78/0.62    k1_xboole_0 = k4_xboole_0(sK3,sK0) | ~spl6_71),
% 1.78/0.62    inference(avatar_component_clause,[],[f1307])).
% 1.78/0.62  fof(f42,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f8])).
% 1.78/0.62  fof(f8,axiom,(
% 1.78/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.78/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.78/0.62  fof(f1316,plain,(
% 1.78/0.62    spl6_72 | ~spl6_62),
% 1.78/0.62    inference(avatar_split_clause,[],[f1312,f1236,f1314])).
% 1.78/0.62  fof(f1314,plain,(
% 1.78/0.62    spl6_72 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 1.78/0.62  fof(f1236,plain,(
% 1.78/0.62    spl6_62 <=> sK0 = k4_xboole_0(sK3,sK1)),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 1.78/0.62  fof(f1312,plain,(
% 1.78/0.62    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) | ~spl6_62),
% 1.78/0.62    inference(forward_demodulation,[],[f1300,f39])).
% 1.78/0.62  fof(f39,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f1])).
% 1.78/0.62  fof(f1,axiom,(
% 1.78/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.78/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.78/0.62  fof(f1300,plain,(
% 1.78/0.62    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,sK3) | ~spl6_62),
% 1.78/0.62    inference(superposition,[],[f42,f1237])).
% 1.78/0.62  fof(f1237,plain,(
% 1.78/0.62    sK0 = k4_xboole_0(sK3,sK1) | ~spl6_62),
% 1.78/0.62    inference(avatar_component_clause,[],[f1236])).
% 1.78/0.62  fof(f1311,plain,(
% 1.78/0.62    spl6_71 | ~spl6_12 | ~spl6_62),
% 1.78/0.62    inference(avatar_split_clause,[],[f1310,f1236,f176,f1307])).
% 1.78/0.62  fof(f176,plain,(
% 1.78/0.62    spl6_12 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.78/0.62  fof(f1310,plain,(
% 1.78/0.62    k1_xboole_0 = k4_xboole_0(sK3,sK0) | (~spl6_12 | ~spl6_62)),
% 1.78/0.62    inference(forward_demodulation,[],[f1298,f177])).
% 1.78/0.62  fof(f177,plain,(
% 1.78/0.62    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl6_12),
% 1.78/0.62    inference(avatar_component_clause,[],[f176])).
% 1.78/0.62  fof(f1298,plain,(
% 1.78/0.62    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,sK0) | ~spl6_62),
% 1.78/0.62    inference(superposition,[],[f49,f1237])).
% 1.78/0.63  % (9274)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.78/0.63  % (9259)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.02/0.64  % (9283)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.02/0.64  % (9266)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.02/0.64  % (9275)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.02/0.65  % (9267)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.02/0.65  % (9254)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.02/0.66  fof(f49,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.02/0.66    inference(definition_unfolding,[],[f38,f40,f40])).
% 2.02/0.66  fof(f40,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f13])).
% 2.02/0.66  fof(f13,axiom,(
% 2.02/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.02/0.66  fof(f38,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f2])).
% 2.02/0.66  fof(f2,axiom,(
% 2.02/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.02/0.66  fof(f1250,plain,(
% 2.02/0.66    sK1 != k4_xboole_0(sK1,sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) != k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK0)) | k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK1)),
% 2.02/0.66    introduced(theory_tautology_sat_conflict,[])).
% 2.02/0.66  fof(f1238,plain,(
% 2.02/0.66    spl6_62 | ~spl6_4 | ~spl6_41 | ~spl6_57),
% 2.02/0.66    inference(avatar_split_clause,[],[f1234,f1209,f1009,f66,f1236])).
% 2.02/0.66  fof(f66,plain,(
% 2.02/0.66    spl6_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.02/0.66  fof(f1009,plain,(
% 2.02/0.66    spl6_41 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.02/0.66  fof(f1209,plain,(
% 2.02/0.66    spl6_57 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK1)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 2.02/0.66  fof(f1234,plain,(
% 2.02/0.66    sK0 = k4_xboole_0(sK3,sK1) | (~spl6_4 | ~spl6_41 | ~spl6_57)),
% 2.02/0.66    inference(forward_demodulation,[],[f1233,f34])).
% 2.02/0.66  fof(f34,plain,(
% 2.02/0.66    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.02/0.66    inference(cnf_transformation,[],[f9])).
% 2.02/0.66  fof(f9,axiom,(
% 2.02/0.66    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.02/0.66  fof(f1233,plain,(
% 2.02/0.66    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK0,k1_xboole_0) | (~spl6_4 | ~spl6_41 | ~spl6_57)),
% 2.02/0.66    inference(forward_demodulation,[],[f1232,f1087])).
% 2.02/0.66  fof(f1087,plain,(
% 2.02/0.66    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X1,sK3))) ) | (~spl6_4 | ~spl6_41)),
% 2.02/0.66    inference(forward_demodulation,[],[f1064,f285])).
% 2.02/0.66  fof(f285,plain,(
% 2.02/0.66    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.02/0.66    inference(forward_demodulation,[],[f284,f101])).
% 2.02/0.66  fof(f101,plain,(
% 2.02/0.66    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8)) )),
% 2.02/0.66    inference(forward_demodulation,[],[f92,f77])).
% 2.02/0.66  fof(f77,plain,(
% 2.02/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.02/0.66    inference(superposition,[],[f48,f34])).
% 2.02/0.66  fof(f48,plain,(
% 2.02/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.02/0.66    inference(definition_unfolding,[],[f33,f40])).
% 2.02/0.66  fof(f33,plain,(
% 2.02/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f7])).
% 2.02/0.66  fof(f7,axiom,(
% 2.02/0.66    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.02/0.66  fof(f92,plain,(
% 2.02/0.66    ( ! [X8] : (k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X8,X8)) )),
% 2.02/0.66    inference(superposition,[],[f43,f69])).
% 2.02/0.66  fof(f69,plain,(
% 2.02/0.66    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.02/0.66    inference(superposition,[],[f39,f35])).
% 2.02/0.66  fof(f43,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f10])).
% 2.02/0.66  fof(f10,axiom,(
% 2.02/0.66    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.02/0.66  fof(f284,plain,(
% 2.02/0.66    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.02/0.66    inference(forward_demodulation,[],[f264,f34])).
% 2.02/0.66  fof(f264,plain,(
% 2.02/0.66    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3))) )),
% 2.02/0.66    inference(superposition,[],[f46,f48])).
% 2.02/0.66  fof(f46,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f11])).
% 2.02/0.66  fof(f11,axiom,(
% 2.02/0.66    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.02/0.66  fof(f1064,plain,(
% 2.02/0.66    ( ! [X1] : (k4_xboole_0(sK0,k2_xboole_0(X1,sK3)) = k4_xboole_0(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,X1)))) ) | (~spl6_4 | ~spl6_41)),
% 2.02/0.66    inference(superposition,[],[f1047,f570])).
% 2.02/0.66  fof(f570,plain,(
% 2.02/0.66    ( ! [X0] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) ) | ~spl6_4),
% 2.02/0.66    inference(superposition,[],[f471,f39])).
% 2.02/0.66  fof(f471,plain,(
% 2.02/0.66    ( ! [X28] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X28)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X28))) ) | ~spl6_4),
% 2.02/0.66    inference(forward_demodulation,[],[f438,f47])).
% 2.02/0.66  fof(f47,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f14])).
% 2.02/0.66  fof(f14,axiom,(
% 2.02/0.66    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.02/0.66  fof(f438,plain,(
% 2.02/0.66    ( ! [X28] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X28)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X28)) ) | ~spl6_4),
% 2.02/0.66    inference(superposition,[],[f47,f67])).
% 2.02/0.66  fof(f67,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) | ~spl6_4),
% 2.02/0.66    inference(avatar_component_clause,[],[f66])).
% 2.02/0.66  fof(f1047,plain,(
% 2.02/0.66    ( ! [X7] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X7)) = k4_xboole_0(sK0,X7)) ) | ~spl6_41),
% 2.02/0.66    inference(superposition,[],[f46,f1010])).
% 2.02/0.66  fof(f1010,plain,(
% 2.02/0.66    sK0 = k4_xboole_0(sK0,sK2) | ~spl6_41),
% 2.02/0.66    inference(avatar_component_clause,[],[f1009])).
% 2.02/0.66  fof(f1232,plain,(
% 2.02/0.66    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) | ~spl6_57),
% 2.02/0.66    inference(forward_demodulation,[],[f1210,f89])).
% 2.02/0.66  fof(f89,plain,(
% 2.02/0.66    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 2.02/0.66    inference(superposition,[],[f43,f39])).
% 2.02/0.66  fof(f1210,plain,(
% 2.02/0.66    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK1) | ~spl6_57),
% 2.02/0.66    inference(avatar_component_clause,[],[f1209])).
% 2.02/0.66  fof(f1189,plain,(
% 2.02/0.66    spl6_52 | ~spl6_42 | ~spl6_49),
% 2.02/0.66    inference(avatar_split_clause,[],[f1185,f1101,f1014,f1187])).
% 2.02/0.66  fof(f1187,plain,(
% 2.02/0.66    spl6_52 <=> sK1 = k4_xboole_0(sK1,sK0)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 2.02/0.66  fof(f1014,plain,(
% 2.02/0.66    spl6_42 <=> sK1 = k4_xboole_0(sK1,sK3)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 2.02/0.66  fof(f1101,plain,(
% 2.02/0.66    spl6_49 <=> sK3 = k2_xboole_0(sK3,sK0)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 2.02/0.66  fof(f1185,plain,(
% 2.02/0.66    sK1 = k4_xboole_0(sK1,sK0) | (~spl6_42 | ~spl6_49)),
% 2.02/0.66    inference(forward_demodulation,[],[f1163,f1015])).
% 2.02/0.66  fof(f1015,plain,(
% 2.02/0.66    sK1 = k4_xboole_0(sK1,sK3) | ~spl6_42),
% 2.02/0.66    inference(avatar_component_clause,[],[f1014])).
% 2.02/0.66  fof(f1163,plain,(
% 2.02/0.66    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK0) | (~spl6_42 | ~spl6_49)),
% 2.02/0.66    inference(superposition,[],[f1060,f1102])).
% 2.02/0.66  fof(f1102,plain,(
% 2.02/0.66    sK3 = k2_xboole_0(sK3,sK0) | ~spl6_49),
% 2.02/0.66    inference(avatar_component_clause,[],[f1101])).
% 2.02/0.66  fof(f1060,plain,(
% 2.02/0.66    ( ! [X7] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X7)) = k4_xboole_0(sK1,X7)) ) | ~spl6_42),
% 2.02/0.66    inference(superposition,[],[f46,f1015])).
% 2.02/0.66  fof(f1119,plain,(
% 2.02/0.66    spl6_50 | ~spl6_49),
% 2.02/0.66    inference(avatar_split_clause,[],[f1110,f1101,f1112])).
% 2.02/0.66  fof(f1110,plain,(
% 2.02/0.66    sK3 = k2_xboole_0(sK0,sK3) | ~spl6_49),
% 2.02/0.66    inference(superposition,[],[f39,f1102])).
% 2.02/0.66  fof(f1103,plain,(
% 2.02/0.66    spl6_49 | ~spl6_48),
% 2.02/0.66    inference(avatar_split_clause,[],[f1099,f1083,f1101])).
% 2.02/0.66  fof(f1083,plain,(
% 2.02/0.66    spl6_48 <=> k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 2.02/0.66  fof(f1099,plain,(
% 2.02/0.66    sK3 = k2_xboole_0(sK3,sK0) | ~spl6_48),
% 2.02/0.66    inference(forward_demodulation,[],[f1097,f35])).
% 2.02/0.66  fof(f1097,plain,(
% 2.02/0.66    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0) | ~spl6_48),
% 2.02/0.66    inference(superposition,[],[f42,f1084])).
% 2.02/0.66  fof(f1084,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK0,sK3) | ~spl6_48),
% 2.02/0.66    inference(avatar_component_clause,[],[f1083])).
% 2.02/0.66  fof(f1085,plain,(
% 2.02/0.66    spl6_48 | ~spl6_4 | ~spl6_41),
% 2.02/0.66    inference(avatar_split_clause,[],[f1081,f1009,f66,f1083])).
% 2.02/0.66  fof(f1081,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK0,sK3) | (~spl6_4 | ~spl6_41)),
% 2.02/0.66    inference(forward_demodulation,[],[f1062,f285])).
% 2.02/0.66  fof(f1062,plain,(
% 2.02/0.66    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | (~spl6_4 | ~spl6_41)),
% 2.02/0.66    inference(superposition,[],[f1047,f67])).
% 2.02/0.66  fof(f1016,plain,(
% 2.02/0.66    spl6_42 | ~spl6_12),
% 2.02/0.66    inference(avatar_split_clause,[],[f1012,f176,f1014])).
% 2.02/0.66  fof(f1012,plain,(
% 2.02/0.66    sK1 = k4_xboole_0(sK1,sK3) | ~spl6_12),
% 2.02/0.66    inference(forward_demodulation,[],[f980,f34])).
% 2.02/0.66  fof(f980,plain,(
% 2.02/0.66    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) | ~spl6_12),
% 2.02/0.66    inference(superposition,[],[f50,f177])).
% 2.02/0.66  fof(f50,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.02/0.66    inference(definition_unfolding,[],[f41,f40])).
% 2.02/0.66  fof(f41,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f12])).
% 2.02/0.66  fof(f12,axiom,(
% 2.02/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.02/0.66  fof(f1011,plain,(
% 2.02/0.66    spl6_41 | ~spl6_13),
% 2.02/0.66    inference(avatar_split_clause,[],[f1007,f181,f1009])).
% 2.02/0.66  fof(f181,plain,(
% 2.02/0.66    spl6_13 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.02/0.66  fof(f1007,plain,(
% 2.02/0.66    sK0 = k4_xboole_0(sK0,sK2) | ~spl6_13),
% 2.02/0.66    inference(forward_demodulation,[],[f979,f34])).
% 2.02/0.66  fof(f979,plain,(
% 2.02/0.66    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | ~spl6_13),
% 2.02/0.66    inference(superposition,[],[f50,f182])).
% 2.02/0.66  fof(f182,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl6_13),
% 2.02/0.66    inference(avatar_component_clause,[],[f181])).
% 2.02/0.66  fof(f744,plain,(
% 2.02/0.66    spl6_32 | ~spl6_9 | ~spl6_11),
% 2.02/0.66    inference(avatar_split_clause,[],[f743,f164,f146,f723])).
% 2.02/0.66  fof(f723,plain,(
% 2.02/0.66    spl6_32 <=> sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 2.02/0.66  fof(f146,plain,(
% 2.02/0.66    spl6_9 <=> k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.02/0.66  fof(f164,plain,(
% 2.02/0.66    spl6_11 <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.02/0.66  fof(f743,plain,(
% 2.02/0.66    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) | (~spl6_9 | ~spl6_11)),
% 2.02/0.66    inference(forward_demodulation,[],[f742,f34])).
% 2.02/0.66  fof(f742,plain,(
% 2.02/0.66    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k1_xboole_0) | (~spl6_9 | ~spl6_11)),
% 2.02/0.66    inference(forward_demodulation,[],[f689,f165])).
% 2.02/0.66  fof(f165,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_11),
% 2.02/0.66    inference(avatar_component_clause,[],[f164])).
% 2.02/0.66  fof(f689,plain,(
% 2.02/0.66    k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) | ~spl6_9),
% 2.02/0.66    inference(superposition,[],[f49,f147])).
% 2.02/0.66  fof(f147,plain,(
% 2.02/0.66    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) | ~spl6_9),
% 2.02/0.66    inference(avatar_component_clause,[],[f146])).
% 2.02/0.66  fof(f740,plain,(
% 2.02/0.66    spl6_30 | ~spl6_26),
% 2.02/0.66    inference(avatar_split_clause,[],[f687,f509,f713])).
% 2.02/0.66  fof(f713,plain,(
% 2.02/0.66    spl6_30 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK0))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.02/0.66  fof(f509,plain,(
% 2.02/0.66    spl6_26 <=> k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.02/0.66  fof(f687,plain,(
% 2.02/0.66    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK0)) | ~spl6_26),
% 2.02/0.66    inference(superposition,[],[f49,f510])).
% 2.02/0.66  fof(f510,plain,(
% 2.02/0.66    k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0) | ~spl6_26),
% 2.02/0.66    inference(avatar_component_clause,[],[f509])).
% 2.02/0.66  fof(f511,plain,(
% 2.02/0.66    spl6_26 | ~spl6_23),
% 2.02/0.66    inference(avatar_split_clause,[],[f507,f476,f509])).
% 2.02/0.66  fof(f476,plain,(
% 2.02/0.66    spl6_23 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 2.02/0.66  fof(f507,plain,(
% 2.02/0.66    k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0) | ~spl6_23),
% 2.02/0.66    inference(forward_demodulation,[],[f497,f89])).
% 2.02/0.66  fof(f497,plain,(
% 2.02/0.66    k4_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) | ~spl6_23),
% 2.02/0.66    inference(superposition,[],[f89,f477])).
% 2.02/0.66  fof(f477,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) | ~spl6_23),
% 2.02/0.66    inference(avatar_component_clause,[],[f476])).
% 2.02/0.66  fof(f487,plain,(
% 2.02/0.66    spl6_23 | ~spl6_8),
% 2.02/0.66    inference(avatar_split_clause,[],[f450,f124,f476])).
% 2.02/0.66  fof(f124,plain,(
% 2.02/0.66    spl6_8 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.02/0.66  fof(f450,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) | ~spl6_8),
% 2.02/0.66    inference(superposition,[],[f125,f47])).
% 2.02/0.66  fof(f125,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl6_8),
% 2.02/0.66    inference(avatar_component_clause,[],[f124])).
% 2.02/0.66  fof(f183,plain,(
% 2.02/0.66    spl6_13 | ~spl6_3),
% 2.02/0.66    inference(avatar_split_clause,[],[f179,f62,f181])).
% 2.02/0.66  fof(f62,plain,(
% 2.02/0.66    spl6_3 <=> r1_xboole_0(sK2,sK0)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.02/0.66  fof(f179,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl6_3),
% 2.02/0.66    inference(resolution,[],[f173,f36])).
% 2.02/0.66  fof(f36,plain,(
% 2.02/0.66    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.02/0.66    inference(cnf_transformation,[],[f26])).
% 2.02/0.66  fof(f26,plain,(
% 2.02/0.66    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f25])).
% 2.02/0.66  fof(f25,plain,(
% 2.02/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f21,plain,(
% 2.02/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.02/0.66    inference(ennf_transformation,[],[f5])).
% 2.02/0.66  fof(f5,axiom,(
% 2.02/0.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.02/0.66  fof(f173,plain,(
% 2.02/0.66    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ) | ~spl6_3),
% 2.02/0.66    inference(forward_demodulation,[],[f171,f49])).
% 2.02/0.66  fof(f171,plain,(
% 2.02/0.66    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) ) | ~spl6_3),
% 2.02/0.66    inference(resolution,[],[f51,f63])).
% 2.02/0.66  fof(f63,plain,(
% 2.02/0.66    r1_xboole_0(sK2,sK0) | ~spl6_3),
% 2.02/0.66    inference(avatar_component_clause,[],[f62])).
% 2.02/0.66  fof(f51,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.02/0.66    inference(definition_unfolding,[],[f45,f40])).
% 2.02/0.66  fof(f45,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f28])).
% 2.02/0.66  fof(f28,plain,(
% 2.02/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f27])).
% 2.02/0.66  fof(f27,plain,(
% 2.02/0.66    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f22,plain,(
% 2.02/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.02/0.66    inference(ennf_transformation,[],[f18])).
% 2.02/0.66  fof(f18,plain,(
% 2.02/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.66    inference(rectify,[],[f4])).
% 2.02/0.66  fof(f4,axiom,(
% 2.02/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.02/0.66  fof(f178,plain,(
% 2.02/0.66    spl6_12 | ~spl6_2),
% 2.02/0.66    inference(avatar_split_clause,[],[f174,f58,f176])).
% 2.02/0.66  fof(f58,plain,(
% 2.02/0.66    spl6_2 <=> r1_xboole_0(sK3,sK1)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.02/0.66  fof(f174,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl6_2),
% 2.02/0.66    inference(resolution,[],[f172,f36])).
% 2.02/0.66  fof(f172,plain,(
% 2.02/0.66    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) ) | ~spl6_2),
% 2.02/0.66    inference(forward_demodulation,[],[f170,f49])).
% 2.02/0.66  fof(f170,plain,(
% 2.02/0.66    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) ) | ~spl6_2),
% 2.02/0.66    inference(resolution,[],[f51,f59])).
% 2.02/0.66  fof(f59,plain,(
% 2.02/0.66    r1_xboole_0(sK3,sK1) | ~spl6_2),
% 2.02/0.66    inference(avatar_component_clause,[],[f58])).
% 2.02/0.66  fof(f166,plain,(
% 2.02/0.66    spl6_11 | ~spl6_10),
% 2.02/0.66    inference(avatar_split_clause,[],[f162,f158,f164])).
% 2.02/0.66  fof(f158,plain,(
% 2.02/0.66    spl6_10 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.02/0.66  fof(f162,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_10),
% 2.02/0.66    inference(forward_demodulation,[],[f161,f77])).
% 2.02/0.66  fof(f161,plain,(
% 2.02/0.66    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_10),
% 2.02/0.66    inference(superposition,[],[f43,f159])).
% 2.02/0.66  fof(f159,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_10),
% 2.02/0.66    inference(avatar_component_clause,[],[f158])).
% 2.02/0.66  fof(f160,plain,(
% 2.02/0.66    spl6_10 | ~spl6_4 | ~spl6_9),
% 2.02/0.66    inference(avatar_split_clause,[],[f156,f146,f66,f158])).
% 2.02/0.66  fof(f156,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | (~spl6_4 | ~spl6_9)),
% 2.02/0.66    inference(forward_demodulation,[],[f155,f67])).
% 2.02/0.66  fof(f155,plain,(
% 2.02/0.66    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_9),
% 2.02/0.66    inference(forward_demodulation,[],[f154,f42])).
% 2.02/0.66  fof(f154,plain,(
% 2.02/0.66    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) | ~spl6_9),
% 2.02/0.66    inference(superposition,[],[f42,f147])).
% 2.02/0.66  fof(f148,plain,(
% 2.02/0.66    spl6_9 | ~spl6_4),
% 2.02/0.66    inference(avatar_split_clause,[],[f137,f66,f146])).
% 2.02/0.66  fof(f137,plain,(
% 2.02/0.66    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) | ~spl6_4),
% 2.02/0.66    inference(superposition,[],[f89,f67])).
% 2.02/0.66  fof(f126,plain,(
% 2.02/0.66    spl6_8 | ~spl6_7),
% 2.02/0.66    inference(avatar_split_clause,[],[f122,f118,f124])).
% 2.02/0.66  fof(f118,plain,(
% 2.02/0.66    spl6_7 <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.02/0.66  fof(f122,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl6_7),
% 2.02/0.66    inference(forward_demodulation,[],[f121,f35])).
% 2.02/0.66  fof(f121,plain,(
% 2.02/0.66    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) | ~spl6_7),
% 2.02/0.66    inference(superposition,[],[f42,f119])).
% 2.02/0.66  fof(f119,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_7),
% 2.02/0.66    inference(avatar_component_clause,[],[f118])).
% 2.02/0.66  fof(f120,plain,(
% 2.02/0.66    spl6_7 | ~spl6_6),
% 2.02/0.66    inference(avatar_split_clause,[],[f116,f112,f118])).
% 2.02/0.66  fof(f112,plain,(
% 2.02/0.66    spl6_6 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.02/0.66  fof(f116,plain,(
% 2.02/0.66    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_6),
% 2.02/0.66    inference(forward_demodulation,[],[f115,f77])).
% 2.02/0.66  fof(f115,plain,(
% 2.02/0.66    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | ~spl6_6),
% 2.02/0.66    inference(superposition,[],[f43,f113])).
% 2.02/0.66  fof(f113,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_6),
% 2.02/0.66    inference(avatar_component_clause,[],[f112])).
% 2.02/0.66  fof(f114,plain,(
% 2.02/0.66    spl6_6 | ~spl6_4 | ~spl6_5),
% 2.02/0.66    inference(avatar_split_clause,[],[f110,f98,f66,f112])).
% 2.02/0.66  fof(f98,plain,(
% 2.02/0.66    spl6_5 <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.02/0.66  fof(f110,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | (~spl6_4 | ~spl6_5)),
% 2.02/0.66    inference(forward_demodulation,[],[f109,f67])).
% 2.02/0.66  fof(f109,plain,(
% 2.02/0.66    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_5),
% 2.02/0.66    inference(forward_demodulation,[],[f108,f39])).
% 2.02/0.66  fof(f108,plain,(
% 2.02/0.66    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_5),
% 2.02/0.66    inference(forward_demodulation,[],[f107,f42])).
% 2.02/0.66  fof(f107,plain,(
% 2.02/0.66    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) | ~spl6_5),
% 2.02/0.66    inference(superposition,[],[f42,f99])).
% 2.02/0.66  fof(f99,plain,(
% 2.02/0.66    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl6_5),
% 2.02/0.66    inference(avatar_component_clause,[],[f98])).
% 2.02/0.66  fof(f100,plain,(
% 2.02/0.66    spl6_5 | ~spl6_4),
% 2.02/0.66    inference(avatar_split_clause,[],[f88,f66,f98])).
% 2.02/0.66  fof(f88,plain,(
% 2.02/0.66    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl6_4),
% 2.02/0.66    inference(superposition,[],[f43,f67])).
% 2.02/0.66  fof(f68,plain,(
% 2.02/0.66    spl6_4),
% 2.02/0.66    inference(avatar_split_clause,[],[f29,f66])).
% 2.02/0.66  fof(f29,plain,(
% 2.02/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.02/0.66    inference(cnf_transformation,[],[f24])).
% 2.02/0.66  fof(f24,plain,(
% 2.02/0.66    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f23])).
% 2.02/0.66  fof(f23,plain,(
% 2.02/0.66    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f20,plain,(
% 2.02/0.66    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.02/0.66    inference(flattening,[],[f19])).
% 2.02/0.66  fof(f19,plain,(
% 2.02/0.66    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.02/0.66    inference(ennf_transformation,[],[f16])).
% 2.02/0.66  fof(f16,negated_conjecture,(
% 2.02/0.66    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.02/0.66    inference(negated_conjecture,[],[f15])).
% 2.02/0.66  fof(f15,conjecture,(
% 2.02/0.66    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.02/0.66  fof(f64,plain,(
% 2.02/0.66    spl6_3),
% 2.02/0.66    inference(avatar_split_clause,[],[f30,f62])).
% 2.02/0.66  fof(f30,plain,(
% 2.02/0.66    r1_xboole_0(sK2,sK0)),
% 2.02/0.66    inference(cnf_transformation,[],[f24])).
% 2.02/0.66  fof(f60,plain,(
% 2.02/0.66    spl6_2),
% 2.02/0.66    inference(avatar_split_clause,[],[f31,f58])).
% 2.02/0.66  fof(f31,plain,(
% 2.02/0.66    r1_xboole_0(sK3,sK1)),
% 2.02/0.66    inference(cnf_transformation,[],[f24])).
% 2.02/0.66  fof(f56,plain,(
% 2.02/0.66    ~spl6_1),
% 2.02/0.66    inference(avatar_split_clause,[],[f32,f54])).
% 2.02/0.66  fof(f54,plain,(
% 2.02/0.66    spl6_1 <=> sK1 = sK2),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.02/0.66  fof(f32,plain,(
% 2.02/0.66    sK1 != sK2),
% 2.02/0.66    inference(cnf_transformation,[],[f24])).
% 2.02/0.66  % SZS output end Proof for theBenchmark
% 2.02/0.66  % (9273)------------------------------
% 2.02/0.66  % (9273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.66  % (9273)Termination reason: Refutation
% 2.02/0.66  
% 2.02/0.66  % (9273)Memory used [KB]: 11769
% 2.02/0.66  % (9273)Time elapsed: 0.185 s
% 2.02/0.66  % (9273)------------------------------
% 2.02/0.66  % (9273)------------------------------
% 2.02/0.66  % (9253)Success in time 0.29 s
%------------------------------------------------------------------------------
