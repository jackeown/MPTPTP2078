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
% DateTime   : Thu Dec  3 12:32:57 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 207 expanded)
%              Number of leaves         :   30 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  297 ( 560 expanded)
%              Number of equality atoms :   51 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f55,f59,f70,f74,f78,f86,f102,f131,f149,f157,f204,f218,f233,f377,f489,f564,f967,f1242,f1259])).

fof(f1259,plain,
    ( ~ spl4_12
    | ~ spl4_17
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_52
    | spl4_72 ),
    inference(avatar_contradiction_clause,[],[f1258])).

fof(f1258,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_52
    | spl4_72 ),
    inference(subsumption_resolution,[],[f101,f1257])).

fof(f1257,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ spl4_17
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_52
    | spl4_72 ),
    inference(trivial_inequality_removal,[],[f1256])).

fof(f1256,plain,
    ( sK3 != sK3
    | ~ r1_xboole_0(sK3,sK0)
    | ~ spl4_17
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_52
    | spl4_72 ),
    inference(forward_demodulation,[],[f1255,f966])).

fof(f966,plain,
    ( sK3 = k3_xboole_0(sK3,sK3)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f964])).

fof(f964,plain,
    ( spl4_52
  <=> sK3 = k3_xboole_0(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1255,plain,
    ( sK3 != k3_xboole_0(sK3,sK3)
    | ~ r1_xboole_0(sK3,sK0)
    | ~ spl4_17
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_39
    | spl4_72 ),
    inference(forward_demodulation,[],[f1254,f376])).

fof(f376,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl4_34
  <=> sK3 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f1254,plain,
    ( sK3 != k3_xboole_0(k4_xboole_0(sK3,sK1),sK3)
    | ~ r1_xboole_0(sK3,sK0)
    | ~ spl4_17
    | ~ spl4_38
    | ~ spl4_39
    | spl4_72 ),
    inference(forward_demodulation,[],[f1245,f508])).

fof(f508,plain,
    ( ! [X0] : k3_xboole_0(k4_xboole_0(sK3,X0),sK3) = k4_xboole_0(sK3,k2_xboole_0(X0,sK2))
    | ~ spl4_17
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f156,f488])).

fof(f488,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl4_38
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f156,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_17
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1245,plain,
    ( sK3 != k4_xboole_0(sK3,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK3,sK0)
    | ~ spl4_39
    | spl4_72 ),
    inference(superposition,[],[f1241,f563])).

fof(f563,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl4_39
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1241,plain,
    ( sK3 != k4_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f1239])).

fof(f1239,plain,
    ( spl4_72
  <=> sK3 = k4_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f101,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_12
  <=> r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1242,plain,
    ( ~ spl4_72
    | ~ spl4_8
    | spl4_21 ),
    inference(avatar_split_clause,[],[f205,f201,f72,f1239])).

fof(f72,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f201,plain,
    ( spl4_21
  <=> r1_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f205,plain,
    ( sK3 != k4_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl4_8
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f203,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f203,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f201])).

% (21455)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f967,plain,
    ( spl4_52
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f299,f230,f216,f964])).

fof(f216,plain,
    ( spl4_23
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f230,plain,
    ( spl4_25
  <=> sK3 = k4_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f299,plain,
    ( sK3 = k3_xboole_0(sK3,sK3)
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(superposition,[],[f217,f232])).

fof(f232,plain,
    ( sK3 = k4_xboole_0(sK3,sK0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f230])).

fof(f217,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f564,plain,
    ( spl4_39
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f139,f129,f84,f76,f68,f562])).

fof(f68,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f76,plain,
    ( spl4_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f84,plain,
    ( spl4_11
  <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f129,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f132,f97])).

fof(f97,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f93,f85])).

fof(f85,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f93,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl4_9 ),
    inference(superposition,[],[f77,f77])).

fof(f77,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(superposition,[],[f130,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f130,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f489,plain,
    ( spl4_38
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f135,f129,f68,f487])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(superposition,[],[f130,f69])).

fof(f377,plain,
    ( spl4_34
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f150,f146,f68,f374])).

fof(f146,plain,
    ( spl4_16
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f150,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f148,f69])).

fof(f148,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f233,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f142,f99,f68,f230])).

fof(f142,plain,
    ( sK3 = k4_xboole_0(sK3,sK0)
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f101,f69])).

fof(f218,plain,
    ( spl4_23
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f97,f84,f76,f216])).

fof(f204,plain,
    ( ~ spl4_21
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f60,f57,f52,f201])).

fof(f52,plain,
    ( spl4_5
  <=> r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f60,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f54,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f54,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f157,plain,
    ( spl4_17
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f63,f57,f41,f154])).

fof(f41,plain,
    ( spl4_3
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f63,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f43,f58])).

fof(f43,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f149,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f62,f57,f36,f146])).

fof(f36,plain,
    ( spl4_2
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f38,f58])).

fof(f38,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f131,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f29,f129])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f102,plain,
    ( spl4_12
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f61,f57,f31,f99])).

fof(f31,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f61,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f33,f58])).

fof(f33,plain,
    ( r1_xboole_0(sK0,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f86,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f23,f84])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f78,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f21,f76])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f74,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f72])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f70,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f55,plain,
    ( ~ spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f50,f46,f52])).

fof(f46,plain,
    ( spl4_4
  <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f50,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3)
    | spl4_4 ),
    inference(forward_demodulation,[],[f48,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f48,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f49,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

fof(f44,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (21452)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (21457)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (21447)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (21451)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (21458)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (21459)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (21449)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (21462)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (21450)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (21446)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (21456)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (21448)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (21454)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (21460)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.27/0.51  % (21451)Refutation found. Thanks to Tanya!
% 1.27/0.51  % SZS status Theorem for theBenchmark
% 1.27/0.51  % SZS output start Proof for theBenchmark
% 1.27/0.51  fof(f1263,plain,(
% 1.27/0.51    $false),
% 1.27/0.51    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f55,f59,f70,f74,f78,f86,f102,f131,f149,f157,f204,f218,f233,f377,f489,f564,f967,f1242,f1259])).
% 1.27/0.51  fof(f1259,plain,(
% 1.27/0.51    ~spl4_12 | ~spl4_17 | ~spl4_34 | ~spl4_38 | ~spl4_39 | ~spl4_52 | spl4_72),
% 1.27/0.51    inference(avatar_contradiction_clause,[],[f1258])).
% 1.27/0.51  fof(f1258,plain,(
% 1.27/0.51    $false | (~spl4_12 | ~spl4_17 | ~spl4_34 | ~spl4_38 | ~spl4_39 | ~spl4_52 | spl4_72)),
% 1.27/0.51    inference(subsumption_resolution,[],[f101,f1257])).
% 1.27/0.51  fof(f1257,plain,(
% 1.27/0.51    ~r1_xboole_0(sK3,sK0) | (~spl4_17 | ~spl4_34 | ~spl4_38 | ~spl4_39 | ~spl4_52 | spl4_72)),
% 1.27/0.51    inference(trivial_inequality_removal,[],[f1256])).
% 1.27/0.51  fof(f1256,plain,(
% 1.27/0.51    sK3 != sK3 | ~r1_xboole_0(sK3,sK0) | (~spl4_17 | ~spl4_34 | ~spl4_38 | ~spl4_39 | ~spl4_52 | spl4_72)),
% 1.27/0.51    inference(forward_demodulation,[],[f1255,f966])).
% 1.27/0.51  fof(f966,plain,(
% 1.27/0.51    sK3 = k3_xboole_0(sK3,sK3) | ~spl4_52),
% 1.27/0.51    inference(avatar_component_clause,[],[f964])).
% 1.27/0.51  fof(f964,plain,(
% 1.27/0.51    spl4_52 <=> sK3 = k3_xboole_0(sK3,sK3)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.27/0.51  fof(f1255,plain,(
% 1.27/0.51    sK3 != k3_xboole_0(sK3,sK3) | ~r1_xboole_0(sK3,sK0) | (~spl4_17 | ~spl4_34 | ~spl4_38 | ~spl4_39 | spl4_72)),
% 1.27/0.51    inference(forward_demodulation,[],[f1254,f376])).
% 1.27/0.51  fof(f376,plain,(
% 1.27/0.51    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_34),
% 1.27/0.51    inference(avatar_component_clause,[],[f374])).
% 1.27/0.51  fof(f374,plain,(
% 1.27/0.51    spl4_34 <=> sK3 = k4_xboole_0(sK3,sK1)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.27/0.51  fof(f1254,plain,(
% 1.27/0.51    sK3 != k3_xboole_0(k4_xboole_0(sK3,sK1),sK3) | ~r1_xboole_0(sK3,sK0) | (~spl4_17 | ~spl4_38 | ~spl4_39 | spl4_72)),
% 1.27/0.51    inference(forward_demodulation,[],[f1245,f508])).
% 1.27/0.51  fof(f508,plain,(
% 1.27/0.51    ( ! [X0] : (k3_xboole_0(k4_xboole_0(sK3,X0),sK3) = k4_xboole_0(sK3,k2_xboole_0(X0,sK2))) ) | (~spl4_17 | ~spl4_38)),
% 1.27/0.51    inference(unit_resulting_resolution,[],[f156,f488])).
% 1.27/0.51  fof(f488,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X0) | ~r1_xboole_0(X0,X1)) ) | ~spl4_38),
% 1.27/0.51    inference(avatar_component_clause,[],[f487])).
% 1.27/0.51  fof(f487,plain,(
% 1.27/0.51    spl4_38 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X0) | ~r1_xboole_0(X0,X1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.27/0.51  fof(f156,plain,(
% 1.27/0.51    r1_xboole_0(sK3,sK2) | ~spl4_17),
% 1.27/0.51    inference(avatar_component_clause,[],[f154])).
% 1.27/0.51  fof(f154,plain,(
% 1.27/0.51    spl4_17 <=> r1_xboole_0(sK3,sK2)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.27/0.51  fof(f1245,plain,(
% 1.27/0.51    sK3 != k4_xboole_0(sK3,k2_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK3,sK0) | (~spl4_39 | spl4_72)),
% 1.27/0.51    inference(superposition,[],[f1241,f563])).
% 1.27/0.51  fof(f563,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) ) | ~spl4_39),
% 1.27/0.51    inference(avatar_component_clause,[],[f562])).
% 1.27/0.51  fof(f562,plain,(
% 1.27/0.51    spl4_39 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.27/0.51  fof(f1241,plain,(
% 1.27/0.51    sK3 != k4_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl4_72),
% 1.27/0.51    inference(avatar_component_clause,[],[f1239])).
% 1.27/0.51  fof(f1239,plain,(
% 1.27/0.51    spl4_72 <=> sK3 = k4_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 1.27/0.51  fof(f101,plain,(
% 1.27/0.51    r1_xboole_0(sK3,sK0) | ~spl4_12),
% 1.27/0.51    inference(avatar_component_clause,[],[f99])).
% 1.27/0.51  fof(f99,plain,(
% 1.27/0.51    spl4_12 <=> r1_xboole_0(sK3,sK0)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.27/0.51  fof(f1242,plain,(
% 1.27/0.51    ~spl4_72 | ~spl4_8 | spl4_21),
% 1.27/0.51    inference(avatar_split_clause,[],[f205,f201,f72,f1239])).
% 1.27/0.51  fof(f72,plain,(
% 1.27/0.51    spl4_8 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.27/0.51  fof(f201,plain,(
% 1.27/0.51    spl4_21 <=> r1_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.27/0.51  fof(f205,plain,(
% 1.27/0.51    sK3 != k4_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | (~spl4_8 | spl4_21)),
% 1.27/0.51    inference(unit_resulting_resolution,[],[f203,f73])).
% 1.27/0.51  fof(f73,plain,(
% 1.27/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl4_8),
% 1.27/0.51    inference(avatar_component_clause,[],[f72])).
% 1.27/0.51  fof(f203,plain,(
% 1.27/0.51    ~r1_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl4_21),
% 1.27/0.51    inference(avatar_component_clause,[],[f201])).
% 1.27/0.51  % (21455)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.27/0.51  fof(f967,plain,(
% 1.27/0.51    spl4_52 | ~spl4_23 | ~spl4_25),
% 1.27/0.51    inference(avatar_split_clause,[],[f299,f230,f216,f964])).
% 1.27/0.51  fof(f216,plain,(
% 1.27/0.51    spl4_23 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.27/0.51  fof(f230,plain,(
% 1.27/0.51    spl4_25 <=> sK3 = k4_xboole_0(sK3,sK0)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.27/0.51  fof(f299,plain,(
% 1.27/0.51    sK3 = k3_xboole_0(sK3,sK3) | (~spl4_23 | ~spl4_25)),
% 1.27/0.51    inference(superposition,[],[f217,f232])).
% 1.27/0.51  fof(f232,plain,(
% 1.27/0.51    sK3 = k4_xboole_0(sK3,sK0) | ~spl4_25),
% 1.27/0.51    inference(avatar_component_clause,[],[f230])).
% 1.27/0.51  fof(f217,plain,(
% 1.27/0.51    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) ) | ~spl4_23),
% 1.27/0.51    inference(avatar_component_clause,[],[f216])).
% 1.27/0.51  fof(f564,plain,(
% 1.27/0.51    spl4_39 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_15),
% 1.27/0.51    inference(avatar_split_clause,[],[f139,f129,f84,f76,f68,f562])).
% 1.27/0.51  fof(f68,plain,(
% 1.27/0.51    spl4_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.27/0.51  fof(f76,plain,(
% 1.27/0.51    spl4_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.27/0.51  fof(f84,plain,(
% 1.27/0.51    spl4_11 <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.27/0.51  fof(f129,plain,(
% 1.27/0.51    spl4_15 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.27/0.51  fof(f139,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) ) | (~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_15)),
% 1.27/0.51    inference(forward_demodulation,[],[f132,f97])).
% 1.27/0.51  fof(f97,plain,(
% 1.27/0.51    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) ) | (~spl4_9 | ~spl4_11)),
% 1.27/0.51    inference(forward_demodulation,[],[f93,f85])).
% 1.27/0.51  fof(f85,plain,(
% 1.27/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) ) | ~spl4_11),
% 1.27/0.51    inference(avatar_component_clause,[],[f84])).
% 1.27/0.51  fof(f93,plain,(
% 1.27/0.51    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) ) | ~spl4_9),
% 1.27/0.51    inference(superposition,[],[f77,f77])).
% 1.27/0.51  fof(f77,plain,(
% 1.27/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_9),
% 1.27/0.51    inference(avatar_component_clause,[],[f76])).
% 1.27/0.51  fof(f132,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,X1)) ) | (~spl4_7 | ~spl4_15)),
% 1.27/0.51    inference(superposition,[],[f130,f69])).
% 1.27/0.51  fof(f69,plain,(
% 1.27/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl4_7),
% 1.27/0.51    inference(avatar_component_clause,[],[f68])).
% 1.27/0.51  fof(f130,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ) | ~spl4_15),
% 1.27/0.51    inference(avatar_component_clause,[],[f129])).
% 1.27/0.51  fof(f489,plain,(
% 1.27/0.51    spl4_38 | ~spl4_7 | ~spl4_15),
% 1.27/0.51    inference(avatar_split_clause,[],[f135,f129,f68,f487])).
% 1.27/0.51  fof(f135,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X0) | ~r1_xboole_0(X0,X1)) ) | (~spl4_7 | ~spl4_15)),
% 1.27/0.51    inference(superposition,[],[f130,f69])).
% 1.27/0.51  fof(f377,plain,(
% 1.27/0.51    spl4_34 | ~spl4_7 | ~spl4_16),
% 1.27/0.51    inference(avatar_split_clause,[],[f150,f146,f68,f374])).
% 1.27/0.51  fof(f146,plain,(
% 1.27/0.51    spl4_16 <=> r1_xboole_0(sK3,sK1)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.27/0.51  fof(f150,plain,(
% 1.27/0.51    sK3 = k4_xboole_0(sK3,sK1) | (~spl4_7 | ~spl4_16)),
% 1.27/0.51    inference(unit_resulting_resolution,[],[f148,f69])).
% 1.27/0.51  fof(f148,plain,(
% 1.27/0.51    r1_xboole_0(sK3,sK1) | ~spl4_16),
% 1.27/0.51    inference(avatar_component_clause,[],[f146])).
% 1.27/0.51  fof(f233,plain,(
% 1.27/0.51    spl4_25 | ~spl4_7 | ~spl4_12),
% 1.27/0.51    inference(avatar_split_clause,[],[f142,f99,f68,f230])).
% 1.27/0.51  fof(f142,plain,(
% 1.27/0.51    sK3 = k4_xboole_0(sK3,sK0) | (~spl4_7 | ~spl4_12)),
% 1.27/0.51    inference(unit_resulting_resolution,[],[f101,f69])).
% 1.27/0.51  fof(f218,plain,(
% 1.27/0.51    spl4_23 | ~spl4_9 | ~spl4_11),
% 1.27/0.51    inference(avatar_split_clause,[],[f97,f84,f76,f216])).
% 1.27/0.51  fof(f204,plain,(
% 1.27/0.51    ~spl4_21 | spl4_5 | ~spl4_6),
% 1.27/0.51    inference(avatar_split_clause,[],[f60,f57,f52,f201])).
% 1.27/0.51  fof(f52,plain,(
% 1.27/0.51    spl4_5 <=> r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.27/0.52  fof(f57,plain,(
% 1.27/0.52    spl4_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.27/0.52  fof(f60,plain,(
% 1.27/0.52    ~r1_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | (spl4_5 | ~spl4_6)),
% 1.27/0.52    inference(unit_resulting_resolution,[],[f54,f58])).
% 1.27/0.52  fof(f58,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_6),
% 1.27/0.52    inference(avatar_component_clause,[],[f57])).
% 1.27/0.52  fof(f54,plain,(
% 1.27/0.52    ~r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3) | spl4_5),
% 1.27/0.52    inference(avatar_component_clause,[],[f52])).
% 1.27/0.52  fof(f157,plain,(
% 1.27/0.52    spl4_17 | ~spl4_3 | ~spl4_6),
% 1.27/0.52    inference(avatar_split_clause,[],[f63,f57,f41,f154])).
% 1.27/0.52  fof(f41,plain,(
% 1.27/0.52    spl4_3 <=> r1_xboole_0(sK2,sK3)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.27/0.52  fof(f63,plain,(
% 1.27/0.52    r1_xboole_0(sK3,sK2) | (~spl4_3 | ~spl4_6)),
% 1.27/0.52    inference(unit_resulting_resolution,[],[f43,f58])).
% 1.27/0.52  fof(f43,plain,(
% 1.27/0.52    r1_xboole_0(sK2,sK3) | ~spl4_3),
% 1.27/0.52    inference(avatar_component_clause,[],[f41])).
% 1.27/0.52  fof(f149,plain,(
% 1.27/0.52    spl4_16 | ~spl4_2 | ~spl4_6),
% 1.27/0.52    inference(avatar_split_clause,[],[f62,f57,f36,f146])).
% 1.27/0.52  fof(f36,plain,(
% 1.27/0.52    spl4_2 <=> r1_xboole_0(sK1,sK3)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.27/0.52  fof(f62,plain,(
% 1.27/0.52    r1_xboole_0(sK3,sK1) | (~spl4_2 | ~spl4_6)),
% 1.27/0.52    inference(unit_resulting_resolution,[],[f38,f58])).
% 1.27/0.52  fof(f38,plain,(
% 1.27/0.52    r1_xboole_0(sK1,sK3) | ~spl4_2),
% 1.27/0.52    inference(avatar_component_clause,[],[f36])).
% 1.27/0.52  fof(f131,plain,(
% 1.27/0.52    spl4_15),
% 1.27/0.52    inference(avatar_split_clause,[],[f29,f129])).
% 1.27/0.52  fof(f29,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f5])).
% 1.27/0.52  fof(f5,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 1.27/0.52  fof(f102,plain,(
% 1.27/0.52    spl4_12 | ~spl4_1 | ~spl4_6),
% 1.27/0.52    inference(avatar_split_clause,[],[f61,f57,f31,f99])).
% 1.27/0.52  fof(f31,plain,(
% 1.27/0.52    spl4_1 <=> r1_xboole_0(sK0,sK3)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.27/0.52  fof(f61,plain,(
% 1.27/0.52    r1_xboole_0(sK3,sK0) | (~spl4_1 | ~spl4_6)),
% 1.27/0.52    inference(unit_resulting_resolution,[],[f33,f58])).
% 1.27/0.52  fof(f33,plain,(
% 1.27/0.52    r1_xboole_0(sK0,sK3) | ~spl4_1),
% 1.27/0.52    inference(avatar_component_clause,[],[f31])).
% 1.27/0.52  fof(f86,plain,(
% 1.27/0.52    spl4_11),
% 1.27/0.52    inference(avatar_split_clause,[],[f23,f84])).
% 1.27/0.52  fof(f23,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f2])).
% 1.27/0.52  fof(f2,axiom,(
% 1.27/0.52    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.27/0.52  fof(f78,plain,(
% 1.27/0.52    spl4_9),
% 1.27/0.52    inference(avatar_split_clause,[],[f21,f76])).
% 1.27/0.52  fof(f21,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f3])).
% 1.27/0.52  fof(f3,axiom,(
% 1.27/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.27/0.52  fof(f74,plain,(
% 1.27/0.52    spl4_8),
% 1.27/0.52    inference(avatar_split_clause,[],[f26,f72])).
% 1.27/0.52  fof(f26,plain,(
% 1.27/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f16])).
% 1.27/0.52  fof(f16,plain,(
% 1.27/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.27/0.52    inference(nnf_transformation,[],[f6])).
% 1.27/0.52  fof(f6,axiom,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.27/0.52  fof(f70,plain,(
% 1.27/0.52    spl4_7),
% 1.27/0.52    inference(avatar_split_clause,[],[f25,f68])).
% 1.27/0.52  fof(f25,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f16])).
% 1.27/0.52  fof(f59,plain,(
% 1.27/0.52    spl4_6),
% 1.27/0.52    inference(avatar_split_clause,[],[f24,f57])).
% 1.27/0.52  fof(f24,plain,(
% 1.27/0.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f13])).
% 1.27/0.52  fof(f13,plain,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f1])).
% 1.27/0.52  fof(f1,axiom,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.27/0.52  fof(f55,plain,(
% 1.27/0.52    ~spl4_5 | spl4_4),
% 1.27/0.52    inference(avatar_split_clause,[],[f50,f46,f52])).
% 1.27/0.52  fof(f46,plain,(
% 1.27/0.52    spl4_4 <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.27/0.52  fof(f50,plain,(
% 1.27/0.52    ~r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3) | spl4_4),
% 1.27/0.52    inference(forward_demodulation,[],[f48,f28])).
% 1.27/0.52  fof(f28,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f4])).
% 1.27/0.52  fof(f4,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.27/0.52  fof(f48,plain,(
% 1.27/0.52    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) | spl4_4),
% 1.27/0.52    inference(avatar_component_clause,[],[f46])).
% 1.27/0.52  fof(f49,plain,(
% 1.27/0.52    ~spl4_4),
% 1.27/0.52    inference(avatar_split_clause,[],[f20,f46])).
% 1.27/0.52  fof(f20,plain,(
% 1.27/0.52    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 1.27/0.52    inference(cnf_transformation,[],[f15])).
% 1.27/0.52  fof(f15,plain,(
% 1.27/0.52    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f14])).
% 1.27/0.52  fof(f14,plain,(
% 1.27/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f12,plain,(
% 1.27/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 1.27/0.52    inference(flattening,[],[f11])).
% 1.27/0.52  fof(f11,plain,(
% 1.27/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 1.27/0.52    inference(ennf_transformation,[],[f10])).
% 1.27/0.52  fof(f10,negated_conjecture,(
% 1.27/0.52    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 1.27/0.52    inference(negated_conjecture,[],[f9])).
% 1.27/0.52  fof(f9,conjecture,(
% 1.27/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).
% 1.27/0.52  fof(f44,plain,(
% 1.27/0.52    spl4_3),
% 1.27/0.52    inference(avatar_split_clause,[],[f19,f41])).
% 1.27/0.52  fof(f19,plain,(
% 1.27/0.52    r1_xboole_0(sK2,sK3)),
% 1.27/0.52    inference(cnf_transformation,[],[f15])).
% 1.27/0.52  fof(f39,plain,(
% 1.27/0.52    spl4_2),
% 1.27/0.52    inference(avatar_split_clause,[],[f18,f36])).
% 1.27/0.52  fof(f18,plain,(
% 1.27/0.52    r1_xboole_0(sK1,sK3)),
% 1.27/0.52    inference(cnf_transformation,[],[f15])).
% 1.27/0.52  fof(f34,plain,(
% 1.27/0.52    spl4_1),
% 1.27/0.52    inference(avatar_split_clause,[],[f17,f31])).
% 1.27/0.52  fof(f17,plain,(
% 1.27/0.52    r1_xboole_0(sK0,sK3)),
% 1.27/0.52    inference(cnf_transformation,[],[f15])).
% 1.27/0.52  % SZS output end Proof for theBenchmark
% 1.27/0.52  % (21451)------------------------------
% 1.27/0.52  % (21451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (21451)Termination reason: Refutation
% 1.27/0.52  
% 1.27/0.52  % (21451)Memory used [KB]: 7164
% 1.27/0.52  % (21451)Time elapsed: 0.109 s
% 1.27/0.52  % (21451)------------------------------
% 1.27/0.52  % (21451)------------------------------
% 1.27/0.52  % (21445)Success in time 0.156 s
%------------------------------------------------------------------------------
