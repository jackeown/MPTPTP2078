%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t74_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  233 (2598 expanded)
%              Number of leaves         :   28 ( 784 expanded)
%              Depth                    :   21
%              Number of atoms          :  552 (5331 expanded)
%              Number of equality atoms :  242 (2825 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1645,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f53,f60,f67,f1002,f1014,f1036,f1037,f1295,f1296,f1298,f1300,f1301,f1302,f1303,f1304,f1306,f1308,f1309,f1310,f1311,f1313,f1315,f1316,f1326,f1346,f1349,f1357,f1358,f1389,f1396,f1403,f1405,f1413,f1414,f1431,f1432,f1434,f1470,f1471,f1485,f1487,f1489,f1606,f1644])).

fof(f1644,plain,
    ( spl3_5
    | ~ spl3_12
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f1643])).

fof(f1643,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f1641,f59])).

fof(f59,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_5
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1641,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0)
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(resolution,[],[f1359,f1325])).

fof(f1325,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f1324])).

fof(f1324,plain,
    ( spl3_17
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1359,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | k4_xboole_0(k2_tarski(X0,sK1),sK2) = k1_tarski(X0) )
    | ~ spl3_12 ),
    inference(resolution,[],[f1010,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',l38_zfmisc_1)).

fof(f1010,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1009,plain,
    ( spl3_12
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1606,plain,
    ( spl3_34
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1599,f1009,f1604])).

fof(f1604,plain,
    ( spl3_34
  <=> k4_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f1599,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f1598,f99])).

fof(f99,plain,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(superposition,[],[f96,f30])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',t3_boole)).

fof(f96,plain,(
    ! [X0] : k4_xboole_0(k2_tarski(X0,X0),k1_xboole_0) = k1_tarski(X0) ),
    inference(resolution,[],[f93,f39])).

fof(f39,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) != k2_tarski(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f31,f30])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',t72_zfmisc_1)).

fof(f1598,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK1),sK2) = k1_xboole_0
    | ~ spl3_12 ),
    inference(resolution,[],[f1360,f1010])).

fof(f1360,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | k4_xboole_0(k2_tarski(X1,sK1),sK2) = k1_xboole_0 )
    | ~ spl3_12 ),
    inference(resolution,[],[f1010,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',t73_zfmisc_1)).

fof(f1489,plain,
    ( ~ spl3_29
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1488,f1411,f1009,f1465])).

fof(f1465,plain,
    ( spl3_29
  <=> k2_tarski(sK1,sK2) != k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f1411,plain,
    ( spl3_26
  <=> k4_xboole_0(k2_tarski(sK1,sK2),sK2) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1488,plain,
    ( k2_tarski(sK1,sK2) != k1_tarski(sK2)
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f1455,f1010])).

fof(f1455,plain,
    ( k2_tarski(sK1,sK2) != k1_tarski(sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ spl3_26 ),
    inference(superposition,[],[f31,f1412])).

fof(f1412,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK2),sK2) = k1_tarski(sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f1411])).

fof(f1487,plain,
    ( ~ spl3_33
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1486,f1411,f1009,f1483])).

fof(f1483,plain,
    ( spl3_33
  <=> k1_tarski(sK1) != k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1486,plain,
    ( k1_tarski(sK1) != k1_tarski(sK2)
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f1454,f1010])).

fof(f1454,plain,
    ( k1_tarski(sK1) != k1_tarski(sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ spl3_26 ),
    inference(superposition,[],[f28,f1412])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1485,plain,
    ( spl3_30
    | ~ spl3_33
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1472,f1411,f1483,f1477])).

fof(f1477,plain,
    ( spl3_30
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f1472,plain,
    ( k1_tarski(sK1) != k1_tarski(sK2)
    | sK1 = sK2
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f1453,f175])).

fof(f175,plain,(
    ! [X2] : ~ r2_hidden(X2,X2) ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,(
    ! [X2] :
      ( k1_tarski(X2) != k1_tarski(X2)
      | ~ r2_hidden(X2,X2) ) ),
    inference(superposition,[],[f113,f169])).

fof(f169,plain,(
    ! [X0] : k4_xboole_0(k1_tarski(X0),X0) = k1_tarski(X0) ),
    inference(trivial_inequality_removal,[],[f168])).

fof(f168,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(X0)
      | k4_xboole_0(k1_tarski(X0),X0) = k1_tarski(X0) ) ),
    inference(equality_factoring,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | k4_xboole_0(k1_tarski(X1),X0) = k1_tarski(X1) ) ),
    inference(resolution,[],[f111,f112])).

fof(f112,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(backward_demodulation,[],[f99,f39])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) ),
    inference(backward_demodulation,[],[f99,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(k2_tarski(X0,X0),X1) = k1_tarski(X0) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f113,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f28,f99])).

fof(f1453,plain,
    ( k1_tarski(sK1) != k1_tarski(sK2)
    | sK1 = sK2
    | r2_hidden(sK2,sK2)
    | ~ spl3_26 ),
    inference(superposition,[],[f27,f1412])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      | X0 = X1
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1471,plain,
    ( spl3_24
    | spl3_28
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1448,f1411,f1468,f1401])).

fof(f1401,plain,
    ( spl3_24
  <=> k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1468,plain,
    ( spl3_28
  <=> k2_tarski(sK1,sK2) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1448,plain,
    ( k2_tarski(sK1,sK2) = k1_tarski(sK2)
    | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK1)
    | ~ spl3_26 ),
    inference(superposition,[],[f193,f1412])).

fof(f193,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X0)
      | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X1) ) ),
    inference(resolution,[],[f182,f177])).

fof(f177,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X2) = k4_xboole_0(k2_tarski(X3,X2),X2) ) ),
    inference(resolution,[],[f175,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f182,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | k2_tarski(X8,X9) = k4_xboole_0(k2_tarski(X8,X9),X8) ) ),
    inference(resolution,[],[f176,f38])).

fof(f176,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X0) ) ),
    inference(resolution,[],[f175,f33])).

fof(f1470,plain,
    ( spl3_24
    | spl3_28
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1441,f1411,f1468,f1401])).

fof(f1441,plain,
    ( k2_tarski(sK1,sK2) = k1_tarski(sK2)
    | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK1)
    | ~ spl3_26 ),
    inference(superposition,[],[f1412,f193])).

fof(f1434,plain,
    ( spl3_24
    | spl3_21 ),
    inference(avatar_split_clause,[],[f1433,f1387,f1401])).

fof(f1387,plain,
    ( spl3_21
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1433,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK1)
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f1424,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',commutativity_k2_tarski)).

fof(f1424,plain,
    ( k2_tarski(sK2,sK1) = k4_xboole_0(k2_tarski(sK2,sK1),sK1)
    | ~ spl3_21 ),
    inference(resolution,[],[f1388,f177])).

fof(f1388,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f1387])).

fof(f1432,plain,
    ( spl3_24
    | spl3_21 ),
    inference(avatar_split_clause,[],[f1423,f1387,f1401])).

fof(f1423,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK1)
    | ~ spl3_21 ),
    inference(resolution,[],[f1388,f176])).

fof(f1431,plain,
    ( spl3_22
    | spl3_21 ),
    inference(avatar_split_clause,[],[f1417,f1387,f1394])).

fof(f1394,plain,
    ( spl3_22
  <=> k4_xboole_0(k1_tarski(sK2),sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1417,plain,
    ( k4_xboole_0(k1_tarski(sK2),sK1) = k1_tarski(sK2)
    | ~ spl3_21 ),
    inference(resolution,[],[f1388,f112])).

fof(f1414,plain,
    ( spl3_26
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1377,f1009,f1411])).

fof(f1377,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK2),sK2) = k1_tarski(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f1010,f646])).

fof(f646,plain,(
    ! [X24,X23] :
      ( ~ r2_hidden(X23,X24)
      | k4_xboole_0(k2_tarski(X23,X24),X24) = k1_tarski(X24) ) ),
    inference(trivial_inequality_removal,[],[f638])).

fof(f638,plain,(
    ! [X24,X23] :
      ( k2_tarski(X23,X24) != k2_tarski(X23,X24)
      | ~ r2_hidden(X23,X24)
      | k4_xboole_0(k2_tarski(X23,X24),X24) = k1_tarski(X24) ) ),
    inference(superposition,[],[f31,f565])).

fof(f565,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X0) = k4_xboole_0(k2_tarski(X1,X0),X0)
      | k4_xboole_0(k2_tarski(X1,X0),X0) = k1_tarski(X0) ) ),
    inference(superposition,[],[f522,f37])).

fof(f522,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X0) = k4_xboole_0(k2_tarski(X1,X0),X0)
      | k4_xboole_0(k2_tarski(X0,X1),X0) = k1_tarski(X0) ) ),
    inference(superposition,[],[f521,f37])).

fof(f521,plain,(
    ! [X59,X60] :
      ( k2_tarski(X59,X60) = k4_xboole_0(k2_tarski(X59,X60),X59)
      | k4_xboole_0(k2_tarski(X59,X60),X59) = k1_tarski(X59) ) ),
    inference(resolution,[],[f179,f175])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X0)
      | k4_xboole_0(k2_tarski(X2,X1),X0) = k1_tarski(X2) ) ),
    inference(resolution,[],[f176,f25])).

fof(f1413,plain,
    ( spl3_26
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1406,f1009,f1411])).

fof(f1406,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK2),sK2) = k1_tarski(sK2)
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f1376,f37])).

fof(f1376,plain,
    ( k4_xboole_0(k2_tarski(sK2,sK1),sK2) = k1_tarski(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f1010,f538])).

fof(f538,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X22,X21)
      | k4_xboole_0(k2_tarski(X21,X22),X21) = k1_tarski(X21) ) ),
    inference(trivial_inequality_removal,[],[f532])).

fof(f532,plain,(
    ! [X21,X22] :
      ( k2_tarski(X21,X22) != k2_tarski(X21,X22)
      | ~ r2_hidden(X22,X21)
      | k4_xboole_0(k2_tarski(X21,X22),X21) = k1_tarski(X21) ) ),
    inference(superposition,[],[f32,f521])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1405,plain,
    ( spl3_24
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1404,f1009,f1401])).

fof(f1404,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK1)
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f1371,f37])).

fof(f1371,plain,
    ( k2_tarski(sK2,sK1) = k4_xboole_0(k2_tarski(sK2,sK1),sK1)
    | ~ spl3_12 ),
    inference(resolution,[],[f1010,f189])).

fof(f189,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,X8)
      | k2_tarski(X8,X9) = k4_xboole_0(k2_tarski(X8,X9),X9) ) ),
    inference(resolution,[],[f177,f38])).

fof(f1403,plain,
    ( spl3_24
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1369,f1009,f1401])).

fof(f1369,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK1)
    | ~ spl3_12 ),
    inference(resolution,[],[f1010,f182])).

fof(f1396,plain,
    ( spl3_22
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1362,f1009,f1394])).

fof(f1362,plain,
    ( k4_xboole_0(k1_tarski(sK2),sK1) = k1_tarski(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f1010,f111])).

fof(f1389,plain,
    ( ~ spl3_21
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1361,f1009,f1387])).

fof(f1361,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl3_12 ),
    inference(resolution,[],[f1010,f38])).

fof(f1358,plain,
    ( spl3_18
    | spl3_17 ),
    inference(avatar_split_clause,[],[f1350,f1324,f1355])).

fof(f1355,plain,
    ( spl3_18
  <=> k2_tarski(sK0,sK2) = k4_xboole_0(k2_tarski(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f1350,plain,
    ( k2_tarski(sK0,sK2) = k4_xboole_0(k2_tarski(sK0,sK2),sK2)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f1337,f37])).

fof(f1337,plain,
    ( k2_tarski(sK2,sK0) = k4_xboole_0(k2_tarski(sK2,sK0),sK2)
    | ~ spl3_17 ),
    inference(resolution,[],[f1325,f176])).

fof(f1357,plain,
    ( spl3_18
    | spl3_17 ),
    inference(avatar_split_clause,[],[f1338,f1324,f1355])).

fof(f1338,plain,
    ( k2_tarski(sK0,sK2) = k4_xboole_0(k2_tarski(sK0,sK2),sK2)
    | ~ spl3_17 ),
    inference(resolution,[],[f1325,f177])).

fof(f1349,plain,
    ( spl3_1
    | spl3_13
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f1348])).

fof(f1348,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f1347,f45])).

fof(f45,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_1
  <=> k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1347,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f1328,f37])).

fof(f1328,plain,
    ( k2_tarski(sK1,sK0) = k4_xboole_0(k2_tarski(sK1,sK0),sK2)
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(resolution,[],[f1325,f1015])).

fof(f1015,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | k2_tarski(sK1,X0) = k4_xboole_0(k2_tarski(sK1,X0),sK2) )
    | ~ spl3_13 ),
    inference(resolution,[],[f1013,f33])).

fof(f1013,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f1012,plain,
    ( spl3_13
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1346,plain,
    ( spl3_1
    | spl3_13
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f1345])).

fof(f1345,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f1327,f45])).

fof(f1327,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(resolution,[],[f1325,f1016])).

fof(f1016,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK2)
        | k2_tarski(X1,sK1) = k4_xboole_0(k2_tarski(X1,sK1),sK2) )
    | ~ spl3_13 ),
    inference(resolution,[],[f1013,f33])).

fof(f1326,plain,
    ( ~ spl3_17
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f1319,f994,f1324])).

fof(f994,plain,
    ( spl3_8
  <=> k4_xboole_0(k1_tarski(sK0),sK2) = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1319,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f1317])).

fof(f1317,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f113,f995])).

fof(f995,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK2) = k1_tarski(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f994])).

fof(f1316,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1017,f1012,f1000])).

fof(f1000,plain,
    ( spl3_10
  <=> k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1017,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(resolution,[],[f1013,f112])).

fof(f1315,plain,
    ( spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1314,f1034,f1000])).

fof(f1034,plain,
    ( spl3_14
  <=> k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1314,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f1038,f285])).

fof(f285,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X0) != k1_tarski(X0)
      | k4_xboole_0(k1_tarski(X1),X0) = k1_tarski(X1) ) ),
    inference(superposition,[],[f281,f37])).

fof(f281,plain,(
    ! [X10,X9] :
      ( k2_tarski(X9,X10) != k1_tarski(X9)
      | k4_xboole_0(k1_tarski(X10),X9) = k1_tarski(X10) ) ),
    inference(subsumption_resolution,[],[f270,f112])).

fof(f270,plain,(
    ! [X10,X9] :
      ( k2_tarski(X9,X10) != k1_tarski(X9)
      | ~ r2_hidden(X10,X9)
      | k4_xboole_0(k1_tarski(X10),X9) = k1_tarski(X10) ) ),
    inference(superposition,[],[f32,f258])).

fof(f258,plain,(
    ! [X35,X34] :
      ( k4_xboole_0(k2_tarski(X34,X35),X34) = k1_tarski(X34)
      | k4_xboole_0(k1_tarski(X35),X34) = k1_tarski(X35) ) ),
    inference(resolution,[],[f135,f175])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
      | k4_xboole_0(k1_tarski(X2),X1) = k1_tarski(X2) ) ),
    inference(resolution,[],[f25,f112])).

fof(f1038,plain,
    ( k2_tarski(sK1,sK2) = k1_tarski(sK2)
    | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_14 ),
    inference(superposition,[],[f1035,f259])).

fof(f259,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X1,X0),X0) = k1_tarski(X0)
      | k4_xboole_0(k1_tarski(X1),X0) = k1_tarski(X1) ) ),
    inference(superposition,[],[f258,f37])).

fof(f1035,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f1313,plain,
    ( spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1312,f1034,f1000])).

fof(f1312,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f1041,f285])).

fof(f1041,plain,
    ( k2_tarski(sK1,sK2) = k1_tarski(sK2)
    | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_14 ),
    inference(superposition,[],[f259,f1035])).

fof(f1311,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1080,f1012,f1000])).

fof(f1080,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1079,f99])).

fof(f1079,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f1015,f1013])).

fof(f1310,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1163,f1012,f1000])).

fof(f1163,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1161,f99])).

fof(f1161,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f1016,f1013])).

fof(f1309,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1240,f1012,f1000])).

fof(f1240,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(duplicate_literal_removal,[],[f1205])).

fof(f1205,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f1018,f99])).

fof(f1018,plain,
    ( ! [X2] :
        ( k4_xboole_0(k2_tarski(sK1,X2),sK2) = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X2),sK2) = k1_tarski(X2) )
    | ~ spl3_13 ),
    inference(resolution,[],[f1013,f135])).

fof(f1308,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1307,f1012,f1000])).

fof(f1307,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1239,f108])).

fof(f108,plain,(
    ! [X3] : k1_xboole_0 != k1_tarski(X3) ),
    inference(subsumption_resolution,[],[f103,f93])).

fof(f103,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_tarski(X3)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f35,f96])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1239,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(condensation,[],[f1238])).

fof(f1238,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X1),sK2) = k1_tarski(X1)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1) )
    | ~ spl3_13 ),
    inference(duplicate_literal_removal,[],[f1215])).

fof(f1215,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X1),sK2) = k1_tarski(X1)
        | k4_xboole_0(k1_tarski(X1),sK2) = k1_tarski(X1)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1) )
    | ~ spl3_13 ),
    inference(superposition,[],[f1018,f247])).

fof(f247,plain,(
    ! [X14,X15,X16] :
      ( k4_xboole_0(k2_tarski(X14,X15),X16) = k1_xboole_0
      | k4_xboole_0(k1_tarski(X15),X16) = k1_tarski(X15)
      | k4_xboole_0(k1_tarski(X14),X16) = k1_tarski(X14) ) ),
    inference(resolution,[],[f134,f112])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k2_tarski(X0,X2),X1) = k1_xboole_0
      | k4_xboole_0(k1_tarski(X2),X1) = k1_tarski(X2) ) ),
    inference(resolution,[],[f36,f112])).

fof(f1306,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1305,f1012,f1000])).

fof(f1305,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1235,f108])).

fof(f1235,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(condensation,[],[f1234])).

fof(f1234,plain,
    ( ! [X8] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X8),sK2) = k1_tarski(X8)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1) )
    | ~ spl3_13 ),
    inference(duplicate_literal_removal,[],[f1233])).

fof(f1233,plain,
    ( ! [X8] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X8),sK2) = k1_tarski(X8)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X8),sK2) = k1_tarski(X8) )
    | ~ spl3_13 ),
    inference(superposition,[],[f247,f1018])).

fof(f1304,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1244,f1012,f1000])).

fof(f1244,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(equality_resolution,[],[f1242])).

fof(f1242,plain,
    ( ! [X6] :
        ( k1_tarski(sK1) != k1_tarski(X6)
        | k4_xboole_0(k1_tarski(X6),sK2) = k1_tarski(X6) )
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1231,f112])).

fof(f1231,plain,
    ( ! [X6] :
        ( k1_tarski(sK1) != k1_tarski(X6)
        | ~ r2_hidden(X6,sK2)
        | k4_xboole_0(k1_tarski(X6),sK2) = k1_tarski(X6) )
    | ~ spl3_13 ),
    inference(superposition,[],[f78,f1018])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X1,X0),X2) != k1_tarski(X0)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f28,f37])).

fof(f1303,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1248,f1012,f1000])).

fof(f1248,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(trivial_inequality_removal,[],[f1247])).

fof(f1247,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f1241,f99])).

fof(f1241,plain,
    ( ! [X3] :
        ( k2_tarski(sK1,X3) != k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X3),sK2) = k1_tarski(X3) )
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1228,f112])).

fof(f1228,plain,
    ( ! [X3] :
        ( k2_tarski(sK1,X3) != k1_tarski(sK1)
        | ~ r2_hidden(X3,sK2)
        | k4_xboole_0(k1_tarski(X3),sK2) = k1_tarski(X3) )
    | ~ spl3_13 ),
    inference(superposition,[],[f32,f1018])).

fof(f1302,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1252,f1012,f1000])).

fof(f1252,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(trivial_inequality_removal,[],[f1251])).

fof(f1251,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f1245,f99])).

fof(f1245,plain,
    ( ! [X0] :
        ( k2_tarski(X0,sK1) != k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X0),sK2) = k1_tarski(X0) )
    | ~ spl3_13 ),
    inference(superposition,[],[f1241,f37])).

fof(f1301,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1293,f1012,f1000])).

fof(f1293,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(duplicate_literal_removal,[],[f1255])).

fof(f1255,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f1203,f99])).

fof(f1203,plain,
    ( ! [X0] :
        ( k4_xboole_0(k2_tarski(X0,sK1),sK2) = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X0),sK2) = k1_tarski(X0) )
    | ~ spl3_13 ),
    inference(superposition,[],[f1018,f37])).

fof(f1300,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1299,f1012,f1000])).

fof(f1299,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1292,f108])).

fof(f1292,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(condensation,[],[f1291])).

fof(f1291,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X1),sK2) = k1_tarski(X1)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1) )
    | ~ spl3_13 ),
    inference(duplicate_literal_removal,[],[f1264])).

fof(f1264,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X1),sK2) = k1_tarski(X1)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X1),sK2) = k1_tarski(X1) )
    | ~ spl3_13 ),
    inference(superposition,[],[f1203,f247])).

fof(f1298,plain,
    ( spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1297,f1012,f1000])).

fof(f1297,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1287,f108])).

fof(f1287,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl3_13 ),
    inference(condensation,[],[f1286])).

fof(f1286,plain,
    ( ! [X8] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X8),sK2) = k1_tarski(X8) )
    | ~ spl3_13 ),
    inference(duplicate_literal_removal,[],[f1285])).

fof(f1285,plain,
    ( ! [X8] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
        | k4_xboole_0(k1_tarski(X8),sK2) = k1_tarski(X8)
        | k4_xboole_0(k1_tarski(X8),sK2) = k1_tarski(X8) )
    | ~ spl3_13 ),
    inference(superposition,[],[f247,f1203])).

fof(f1296,plain,
    ( spl3_8
    | spl3_3
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1290,f1012,f51,f994])).

fof(f51,plain,
    ( spl3_3
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1290,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK2) = k1_tarski(sK0)
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(trivial_inequality_removal,[],[f1267])).

fof(f1267,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | k4_xboole_0(k1_tarski(sK0),sK2) = k1_tarski(sK0)
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(superposition,[],[f52,f1203])).

fof(f52,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f1295,plain,
    ( spl3_3
    | spl3_9
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f1294])).

fof(f1294,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1290,f992])).

fof(f992,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK2) != k1_tarski(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f991])).

fof(f991,plain,
    ( spl3_9
  <=> k4_xboole_0(k1_tarski(sK0),sK2) != k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1037,plain,
    ( spl3_14
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1022,f1012,f1034])).

fof(f1022,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f1013,f177])).

fof(f1036,plain,
    ( spl3_14
    | spl3_13 ),
    inference(avatar_split_clause,[],[f1029,f1012,f1034])).

fof(f1029,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK2)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1021,f37])).

fof(f1021,plain,
    ( k2_tarski(sK2,sK1) = k4_xboole_0(k2_tarski(sK2,sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f1013,f176])).

fof(f1014,plain,
    ( ~ spl3_13
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f1007,f1000,f1012])).

fof(f1007,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f1005])).

fof(f1005,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | ~ r2_hidden(sK1,sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f113,f1001])).

fof(f1001,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1002,plain,
    ( spl3_8
    | spl3_10
    | spl3_7 ),
    inference(avatar_split_clause,[],[f974,f65,f1000,f994])).

fof(f65,plain,
    ( spl3_7
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f974,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | k4_xboole_0(k1_tarski(sK0),sK2) = k1_tarski(sK0)
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f972])).

fof(f972,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)
    | k4_xboole_0(k1_tarski(sK0),sK2) = k1_tarski(sK0)
    | ~ spl3_7 ),
    inference(superposition,[],[f66,f247])).

fof(f66,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f21,f65])).

fof(f21,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t74_zfmisc_1.p',t74_zfmisc_1)).

fof(f60,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
