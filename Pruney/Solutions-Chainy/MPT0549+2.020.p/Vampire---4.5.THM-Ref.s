%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 223 expanded)
%              Number of leaves         :   34 ( 104 expanded)
%              Depth                    :    8
%              Number of atoms          :  365 ( 620 expanded)
%              Number of equality atoms :  102 ( 180 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f425,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f46,f51,f55,f59,f63,f71,f75,f79,f83,f87,f91,f96,f112,f123,f143,f152,f158,f170,f175,f187,f233,f237,f286,f300,f412,f421])).

fof(f421,plain,
    ( ~ spl2_1
    | spl2_27
    | ~ spl2_60 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl2_1
    | spl2_27
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f418,f168])).

fof(f168,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl2_27 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_27
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f418,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_60 ),
    inference(trivial_inequality_removal,[],[f414])).

fof(f414,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_60 ),
    inference(superposition,[],[f411,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f411,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl2_60
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,X0)
        | k1_xboole_0 != k9_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f412,plain,
    ( spl2_60
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f408,f150,f73,f48,f410])).

fof(f48,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f73,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f150,plain,
    ( spl2_24
  <=> ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0)
        | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

% (6873)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
fof(f408,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,X0)
        | k1_xboole_0 != k9_relat_1(sK1,X0) )
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f405,f50])).

fof(f50,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f405,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,X0)
        | k1_xboole_0 != k9_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_9
    | ~ spl2_24 ),
    inference(resolution,[],[f151,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X0))
        | k1_xboole_0 = k7_relat_1(sK1,X0)
        | k1_xboole_0 != k9_relat_1(sK1,X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f150])).

fof(f300,plain,
    ( ~ spl2_27
    | spl2_2
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f296,f284,f42,f167])).

fof(f42,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f284,plain,
    ( spl2_42
  <=> ! [X0] :
        ( k1_xboole_0 != k7_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f296,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl2_2
    | ~ spl2_42 ),
    inference(resolution,[],[f285,f44])).

fof(f44,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f285,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 != k7_relat_1(sK1,X0) )
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f284])).

fof(f286,plain,
    ( spl2_42
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f280,f85,f48,f284])).

fof(f85,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f280,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k7_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(resolution,[],[f86,f50])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 != k7_relat_1(X1,X0)
        | r1_xboole_0(k1_relat_1(X1),X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f237,plain,
    ( spl2_1
    | ~ spl2_30
    | ~ spl2_36 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl2_1
    | ~ spl2_30
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f235,f232])).

fof(f232,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl2_36
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f235,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl2_1
    | ~ spl2_30 ),
    inference(superposition,[],[f40,f186])).

fof(f186,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl2_30
  <=> k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f40,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f233,plain,
    ( spl2_36
    | ~ spl2_18
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f228,f172,f141,f120,f230])).

fof(f120,plain,
    ( spl2_18
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f141,plain,
    ( spl2_22
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f172,plain,
    ( spl2_28
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f228,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_18
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f225,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f225,plain,
    ( k9_relat_1(sK1,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(superposition,[],[f142,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f172])).

fof(f142,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f141])).

fof(f187,plain,
    ( spl2_30
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f180,f167,f141,f184])).

fof(f180,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0)
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(superposition,[],[f142,f169])).

fof(f169,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f167])).

fof(f175,plain,
    ( spl2_28
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f164,f156,f110,f172])).

fof(f110,plain,
    ( spl2_17
  <=> ! [X2] : r1_xboole_0(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f156,plain,
    ( spl2_25
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f164,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(resolution,[],[f157,f111])).

fof(f111,plain,
    ( ! [X2] : r1_xboole_0(X2,k1_xboole_0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f110])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f156])).

fof(f170,plain,
    ( spl2_27
    | ~ spl2_2
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f163,f156,f42,f167])).

fof(f163,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_25 ),
    inference(resolution,[],[f157,f43])).

fof(f43,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f158,plain,
    ( spl2_25
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f153,f81,f48,f156])).

fof(f81,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f82,f50])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f152,plain,
    ( spl2_24
    | ~ spl2_6
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f148,f141,f61,f150])).

fof(f61,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f148,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0)
        | ~ v1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl2_6
    | ~ spl2_22 ),
    inference(superposition,[],[f62,f142])).

fof(f62,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f143,plain,
    ( spl2_22
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f138,f77,f48,f141])).

fof(f77,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f138,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f78,f50])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f123,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f117,f57,f48,f120])).

fof(f57,plain,
    ( spl2_5
  <=> ! [X0] :
        ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f117,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f112,plain,
    ( spl2_17
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f99,f94,f89,f110])).

fof(f89,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f94,plain,
    ( spl2_14
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f99,plain,
    ( ! [X2] : r1_xboole_0(X2,k1_xboole_0)
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(resolution,[],[f90,f95])).

fof(f95,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f96,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f92,f69,f53,f94])).

fof(f53,plain,
    ( spl2_4
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f69,plain,
    ( spl2_8
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f92,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f70,f54])).

fof(f54,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f70,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f91,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f87,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f34,f85])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f83,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f75,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f71,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f63,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f59,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f46,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f25,f42,f38])).

fof(f25,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f26,f42,f38])).

fof(f26,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 19:47:49 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.40  % (6881)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.40  % (6877)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (6877)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f425,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f45,f46,f51,f55,f59,f63,f71,f75,f79,f83,f87,f91,f96,f112,f123,f143,f152,f158,f170,f175,f187,f233,f237,f286,f300,f412,f421])).
% 0.20/0.41  fof(f421,plain,(
% 0.20/0.41    ~spl2_1 | spl2_27 | ~spl2_60),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f420])).
% 0.20/0.41  fof(f420,plain,(
% 0.20/0.41    $false | (~spl2_1 | spl2_27 | ~spl2_60)),
% 0.20/0.41    inference(subsumption_resolution,[],[f418,f168])).
% 0.20/0.41  fof(f168,plain,(
% 0.20/0.41    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl2_27),
% 0.20/0.41    inference(avatar_component_clause,[],[f167])).
% 0.20/0.41  fof(f167,plain,(
% 0.20/0.41    spl2_27 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.41  fof(f418,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_1 | ~spl2_60)),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f414])).
% 0.20/0.41  fof(f414,plain,(
% 0.20/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_1 | ~spl2_60)),
% 0.20/0.41    inference(superposition,[],[f411,f39])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f38])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    spl2_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.41  fof(f411,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | ~spl2_60),
% 0.20/0.41    inference(avatar_component_clause,[],[f410])).
% 0.20/0.41  fof(f410,plain,(
% 0.20/0.41    spl2_60 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,X0) | k1_xboole_0 != k9_relat_1(sK1,X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 0.20/0.41  fof(f412,plain,(
% 0.20/0.41    spl2_60 | ~spl2_3 | ~spl2_9 | ~spl2_24),
% 0.20/0.41    inference(avatar_split_clause,[],[f408,f150,f73,f48,f410])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    spl2_3 <=> v1_relat_1(sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    spl2_9 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.41  fof(f150,plain,(
% 0.20/0.41    spl2_24 <=> ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k7_relat_1(sK1,X0) | ~v1_relat_1(k7_relat_1(sK1,X0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.41  % (6873)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.41  fof(f408,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,X0) | k1_xboole_0 != k9_relat_1(sK1,X0)) ) | (~spl2_3 | ~spl2_9 | ~spl2_24)),
% 0.20/0.41    inference(subsumption_resolution,[],[f405,f50])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    v1_relat_1(sK1) | ~spl2_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f48])).
% 0.20/0.41  fof(f405,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,X0) | k1_xboole_0 != k9_relat_1(sK1,X0) | ~v1_relat_1(sK1)) ) | (~spl2_9 | ~spl2_24)),
% 0.20/0.41    inference(resolution,[],[f151,f74])).
% 0.20/0.41  fof(f74,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f73])).
% 0.20/0.41  fof(f151,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK1,X0)) | k1_xboole_0 = k7_relat_1(sK1,X0) | k1_xboole_0 != k9_relat_1(sK1,X0)) ) | ~spl2_24),
% 0.20/0.41    inference(avatar_component_clause,[],[f150])).
% 0.20/0.41  fof(f300,plain,(
% 0.20/0.41    ~spl2_27 | spl2_2 | ~spl2_42),
% 0.20/0.41    inference(avatar_split_clause,[],[f296,f284,f42,f167])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    spl2_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.41  fof(f284,plain,(
% 0.20/0.41    spl2_42 <=> ! [X0] : (k1_xboole_0 != k7_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.20/0.41  fof(f296,plain,(
% 0.20/0.41    k1_xboole_0 != k7_relat_1(sK1,sK0) | (spl2_2 | ~spl2_42)),
% 0.20/0.41    inference(resolution,[],[f285,f44])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f42])).
% 0.20/0.41  fof(f285,plain,(
% 0.20/0.41    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 != k7_relat_1(sK1,X0)) ) | ~spl2_42),
% 0.20/0.41    inference(avatar_component_clause,[],[f284])).
% 0.20/0.41  fof(f286,plain,(
% 0.20/0.41    spl2_42 | ~spl2_3 | ~spl2_12),
% 0.20/0.41    inference(avatar_split_clause,[],[f280,f85,f48,f284])).
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    spl2_12 <=> ! [X1,X0] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.41  fof(f280,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 != k7_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),X0)) ) | (~spl2_3 | ~spl2_12)),
% 0.20/0.41    inference(resolution,[],[f86,f50])).
% 0.20/0.41  fof(f86,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) ) | ~spl2_12),
% 0.20/0.41    inference(avatar_component_clause,[],[f85])).
% 0.20/0.41  fof(f237,plain,(
% 0.20/0.41    spl2_1 | ~spl2_30 | ~spl2_36),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f236])).
% 0.20/0.41  fof(f236,plain,(
% 0.20/0.41    $false | (spl2_1 | ~spl2_30 | ~spl2_36)),
% 0.20/0.41    inference(subsumption_resolution,[],[f235,f232])).
% 0.20/0.41  fof(f232,plain,(
% 0.20/0.41    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_36),
% 0.20/0.41    inference(avatar_component_clause,[],[f230])).
% 0.20/0.41  fof(f230,plain,(
% 0.20/0.41    spl2_36 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.20/0.41  fof(f235,plain,(
% 0.20/0.41    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl2_1 | ~spl2_30)),
% 0.20/0.41    inference(superposition,[],[f40,f186])).
% 0.20/0.41  fof(f186,plain,(
% 0.20/0.41    k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0) | ~spl2_30),
% 0.20/0.41    inference(avatar_component_clause,[],[f184])).
% 0.20/0.41  fof(f184,plain,(
% 0.20/0.41    spl2_30 <=> k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl2_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f38])).
% 0.20/0.41  fof(f233,plain,(
% 0.20/0.41    spl2_36 | ~spl2_18 | ~spl2_22 | ~spl2_28),
% 0.20/0.41    inference(avatar_split_clause,[],[f228,f172,f141,f120,f230])).
% 0.20/0.41  fof(f120,plain,(
% 0.20/0.41    spl2_18 <=> k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.41  fof(f141,plain,(
% 0.20/0.41    spl2_22 <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.41  fof(f172,plain,(
% 0.20/0.41    spl2_28 <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.20/0.41  fof(f228,plain,(
% 0.20/0.41    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl2_18 | ~spl2_22 | ~spl2_28)),
% 0.20/0.41    inference(forward_demodulation,[],[f225,f122])).
% 0.20/0.41  fof(f122,plain,(
% 0.20/0.41    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) | ~spl2_18),
% 0.20/0.41    inference(avatar_component_clause,[],[f120])).
% 0.20/0.41  fof(f225,plain,(
% 0.20/0.41    k9_relat_1(sK1,k1_xboole_0) = k2_relat_1(k1_xboole_0) | (~spl2_22 | ~spl2_28)),
% 0.20/0.41    inference(superposition,[],[f142,f174])).
% 0.20/0.41  fof(f174,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) | ~spl2_28),
% 0.20/0.41    inference(avatar_component_clause,[],[f172])).
% 0.20/0.41  fof(f142,plain,(
% 0.20/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_22),
% 0.20/0.41    inference(avatar_component_clause,[],[f141])).
% 0.20/0.41  fof(f187,plain,(
% 0.20/0.41    spl2_30 | ~spl2_22 | ~spl2_27),
% 0.20/0.41    inference(avatar_split_clause,[],[f180,f167,f141,f184])).
% 0.20/0.41  fof(f180,plain,(
% 0.20/0.41    k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0) | (~spl2_22 | ~spl2_27)),
% 0.20/0.41    inference(superposition,[],[f142,f169])).
% 0.20/0.41  fof(f169,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_27),
% 0.20/0.41    inference(avatar_component_clause,[],[f167])).
% 0.20/0.41  fof(f175,plain,(
% 0.20/0.41    spl2_28 | ~spl2_17 | ~spl2_25),
% 0.20/0.41    inference(avatar_split_clause,[],[f164,f156,f110,f172])).
% 0.20/0.41  fof(f110,plain,(
% 0.20/0.41    spl2_17 <=> ! [X2] : r1_xboole_0(X2,k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.41  fof(f156,plain,(
% 0.20/0.41    spl2_25 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.41  fof(f164,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) | (~spl2_17 | ~spl2_25)),
% 0.20/0.41    inference(resolution,[],[f157,f111])).
% 0.20/0.41  fof(f111,plain,(
% 0.20/0.41    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) ) | ~spl2_17),
% 0.20/0.41    inference(avatar_component_clause,[],[f110])).
% 0.20/0.41  fof(f157,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | ~spl2_25),
% 0.20/0.41    inference(avatar_component_clause,[],[f156])).
% 0.20/0.41  fof(f170,plain,(
% 0.20/0.41    spl2_27 | ~spl2_2 | ~spl2_25),
% 0.20/0.41    inference(avatar_split_clause,[],[f163,f156,f42,f167])).
% 0.20/0.41  fof(f163,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_2 | ~spl2_25)),
% 0.20/0.41    inference(resolution,[],[f157,f43])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f42])).
% 0.20/0.41  fof(f158,plain,(
% 0.20/0.41    spl2_25 | ~spl2_3 | ~spl2_11),
% 0.20/0.41    inference(avatar_split_clause,[],[f153,f81,f48,f156])).
% 0.20/0.41  fof(f81,plain,(
% 0.20/0.41    spl2_11 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.41  fof(f153,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | (~spl2_3 | ~spl2_11)),
% 0.20/0.41    inference(resolution,[],[f82,f50])).
% 0.20/0.41  fof(f82,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | ~spl2_11),
% 0.20/0.41    inference(avatar_component_clause,[],[f81])).
% 0.20/0.41  fof(f152,plain,(
% 0.20/0.41    spl2_24 | ~spl2_6 | ~spl2_22),
% 0.20/0.41    inference(avatar_split_clause,[],[f148,f141,f61,f150])).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    spl2_6 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.41  fof(f148,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k7_relat_1(sK1,X0) | ~v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl2_6 | ~spl2_22)),
% 0.20/0.41    inference(superposition,[],[f62,f142])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f61])).
% 0.20/0.41  fof(f143,plain,(
% 0.20/0.41    spl2_22 | ~spl2_3 | ~spl2_10),
% 0.20/0.41    inference(avatar_split_clause,[],[f138,f77,f48,f141])).
% 0.20/0.41  fof(f77,plain,(
% 0.20/0.41    spl2_10 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.41  fof(f138,plain,(
% 0.20/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | (~spl2_3 | ~spl2_10)),
% 0.20/0.41    inference(resolution,[],[f78,f50])).
% 0.20/0.41  fof(f78,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_10),
% 0.20/0.41    inference(avatar_component_clause,[],[f77])).
% 0.20/0.41  fof(f123,plain,(
% 0.20/0.41    spl2_18 | ~spl2_3 | ~spl2_5),
% 0.20/0.41    inference(avatar_split_clause,[],[f117,f57,f48,f120])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    spl2_5 <=> ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.41  fof(f117,plain,(
% 0.20/0.41    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) | (~spl2_3 | ~spl2_5)),
% 0.20/0.41    inference(resolution,[],[f58,f50])).
% 0.20/0.41  fof(f58,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) ) | ~spl2_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f57])).
% 0.20/0.41  fof(f112,plain,(
% 0.20/0.41    spl2_17 | ~spl2_13 | ~spl2_14),
% 0.20/0.41    inference(avatar_split_clause,[],[f99,f94,f89,f110])).
% 0.20/0.41  fof(f89,plain,(
% 0.20/0.41    spl2_13 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.41  fof(f94,plain,(
% 0.20/0.41    spl2_14 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.41  fof(f99,plain,(
% 0.20/0.41    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) ) | (~spl2_13 | ~spl2_14)),
% 0.20/0.41    inference(resolution,[],[f90,f95])).
% 0.20/0.41  fof(f95,plain,(
% 0.20/0.41    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl2_14),
% 0.20/0.41    inference(avatar_component_clause,[],[f94])).
% 0.20/0.41  fof(f90,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl2_13),
% 0.20/0.41    inference(avatar_component_clause,[],[f89])).
% 0.20/0.41  fof(f96,plain,(
% 0.20/0.41    spl2_14 | ~spl2_4 | ~spl2_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f92,f69,f53,f94])).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    spl2_4 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.41  fof(f69,plain,(
% 0.20/0.41    spl2_8 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.41  fof(f92,plain,(
% 0.20/0.41    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl2_4 | ~spl2_8)),
% 0.20/0.41    inference(superposition,[],[f70,f54])).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f53])).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f69])).
% 0.20/0.41  fof(f91,plain,(
% 0.20/0.41    spl2_13),
% 0.20/0.41    inference(avatar_split_clause,[],[f36,f89])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.41  fof(f87,plain,(
% 0.20/0.41    spl2_12),
% 0.20/0.41    inference(avatar_split_clause,[],[f34,f85])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(nnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    spl2_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f35,f81])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    spl2_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f33,f77])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f32,f73])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f31,f69])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f30,f61])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f57])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f53])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f48])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.42    inference(flattening,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f9])).
% 0.20/0.42  fof(f9,conjecture,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl2_1 | spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f42,f38])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f22])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ~spl2_1 | ~spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f42,f38])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f22])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (6877)------------------------------
% 0.20/0.42  % (6877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (6877)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (6877)Memory used [KB]: 10746
% 0.20/0.42  % (6877)Time elapsed: 0.012 s
% 0.20/0.42  % (6877)------------------------------
% 0.20/0.42  % (6877)------------------------------
% 0.21/0.42  % (6883)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.42  % (6871)Success in time 0.069 s
%------------------------------------------------------------------------------
