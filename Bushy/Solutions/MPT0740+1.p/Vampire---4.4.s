%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t30_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 316 expanded)
%              Number of leaves         :   48 ( 128 expanded)
%              Depth                    :    8
%              Number of atoms          :  481 ( 779 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f116,f132,f146,f156,f166,f209,f216,f266,f375,f385,f393,f604,f611,f793,f823,f1017,f1067,f1404,f1591,f1663,f1687,f1692,f1708,f1892,f1929,f1934,f4347,f4361,f4376,f4474])).

fof(f4474,plain,
    ( spl8_7
    | ~ spl8_526 ),
    inference(avatar_contradiction_clause,[],[f4473])).

fof(f4473,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_526 ),
    inference(subsumption_resolution,[],[f4461,f131])).

fof(f131,plain,
    ( ~ v2_ordinal1(k3_tarski(sK0))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_7
  <=> ~ v2_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f4461,plain,
    ( v2_ordinal1(k3_tarski(sK0))
    | ~ spl8_526 ),
    inference(trivial_inequality_removal,[],[f4446])).

fof(f4446,plain,
    ( sK2(k3_tarski(sK0)) != sK2(k3_tarski(sK0))
    | v2_ordinal1(k3_tarski(sK0))
    | ~ spl8_526 ),
    inference(superposition,[],[f72,f4340])).

fof(f4340,plain,
    ( sK2(k3_tarski(sK0)) = sK3(k3_tarski(sK0))
    | ~ spl8_526 ),
    inference(avatar_component_clause,[],[f4339])).

fof(f4339,plain,
    ( spl8_526
  <=> sK2(k3_tarski(sK0)) = sK3(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_526])])).

fof(f72,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',d3_ordinal1)).

fof(f4376,plain,
    ( spl8_7
    | ~ spl8_528 ),
    inference(avatar_contradiction_clause,[],[f4375])).

fof(f4375,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_528 ),
    inference(subsumption_resolution,[],[f4364,f131])).

fof(f4364,plain,
    ( v2_ordinal1(k3_tarski(sK0))
    | ~ spl8_528 ),
    inference(resolution,[],[f4346,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4346,plain,
    ( r2_hidden(sK2(k3_tarski(sK0)),sK3(k3_tarski(sK0)))
    | ~ spl8_528 ),
    inference(avatar_component_clause,[],[f4345])).

fof(f4345,plain,
    ( spl8_528
  <=> r2_hidden(sK2(k3_tarski(sK0)),sK3(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_528])])).

fof(f4361,plain,
    ( spl8_7
    | ~ spl8_524 ),
    inference(avatar_contradiction_clause,[],[f4360])).

fof(f4360,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_524 ),
    inference(subsumption_resolution,[],[f4349,f131])).

fof(f4349,plain,
    ( v2_ordinal1(k3_tarski(sK0))
    | ~ spl8_524 ),
    inference(resolution,[],[f4334,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4334,plain,
    ( r2_hidden(sK3(k3_tarski(sK0)),sK2(k3_tarski(sK0)))
    | ~ spl8_524 ),
    inference(avatar_component_clause,[],[f4333])).

fof(f4333,plain,
    ( spl8_524
  <=> r2_hidden(sK3(k3_tarski(sK0)),sK2(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_524])])).

fof(f4347,plain,
    ( spl8_524
    | spl8_526
    | spl8_528
    | ~ spl8_70
    | ~ spl8_118 ),
    inference(avatar_split_clause,[],[f2106,f924,f667,f4345,f4339,f4333])).

fof(f667,plain,
    ( spl8_70
  <=> v3_ordinal1(sK2(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f924,plain,
    ( spl8_118
  <=> v3_ordinal1(sK3(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f2106,plain,
    ( r2_hidden(sK2(k3_tarski(sK0)),sK3(k3_tarski(sK0)))
    | sK2(k3_tarski(sK0)) = sK3(k3_tarski(sK0))
    | r2_hidden(sK3(k3_tarski(sK0)),sK2(k3_tarski(sK0)))
    | ~ spl8_70
    | ~ spl8_118 ),
    inference(resolution,[],[f1938,f925])).

fof(f925,plain,
    ( v3_ordinal1(sK3(k3_tarski(sK0)))
    | ~ spl8_118 ),
    inference(avatar_component_clause,[],[f924])).

fof(f1938,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_hidden(sK2(k3_tarski(sK0)),X1)
        | sK2(k3_tarski(sK0)) = X1
        | r2_hidden(X1,sK2(k3_tarski(sK0))) )
    | ~ spl8_70 ),
    inference(resolution,[],[f668,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',t24_ordinal1)).

fof(f668,plain,
    ( v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f667])).

fof(f1934,plain,
    ( spl8_71
    | ~ spl8_256
    | ~ spl8_262 ),
    inference(avatar_contradiction_clause,[],[f1933])).

fof(f1933,plain,
    ( $false
    | ~ spl8_71
    | ~ spl8_256
    | ~ spl8_262 ),
    inference(subsumption_resolution,[],[f1904,f1928])).

fof(f1928,plain,
    ( v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0))))
    | ~ spl8_262 ),
    inference(avatar_component_clause,[],[f1927])).

fof(f1927,plain,
    ( spl8_262
  <=> v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_262])])).

fof(f1904,plain,
    ( ~ v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0))))
    | ~ spl8_71
    | ~ spl8_256 ),
    inference(subsumption_resolution,[],[f1896,f671])).

fof(f671,plain,
    ( ~ v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ spl8_71 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl8_71
  <=> ~ v3_ordinal1(sK2(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f1896,plain,
    ( ~ v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0))))
    | v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ spl8_256 ),
    inference(resolution,[],[f1891,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',t23_ordinal1)).

fof(f1891,plain,
    ( r2_hidden(sK2(k3_tarski(sK0)),sK7(sK0,sK2(k3_tarski(sK0))))
    | ~ spl8_256 ),
    inference(avatar_component_clause,[],[f1890])).

fof(f1890,plain,
    ( spl8_256
  <=> r2_hidden(sK2(k3_tarski(sK0)),sK7(sK0,sK2(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_256])])).

fof(f1929,plain,
    ( spl8_262
    | ~ spl8_0
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f1808,f373,f107,f1927])).

fof(f107,plain,
    ( spl8_0
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f373,plain,
    ( spl8_36
  <=> r2_hidden(sK7(sK0,sK2(k3_tarski(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f1808,plain,
    ( v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0))))
    | ~ spl8_0
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f1797,f108])).

fof(f108,plain,
    ( v3_ordinal1(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f107])).

fof(f1797,plain,
    ( ~ v3_ordinal1(sK0)
    | v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0))))
    | ~ spl8_36 ),
    inference(resolution,[],[f374,f78])).

fof(f374,plain,
    ( r2_hidden(sK7(sK0,sK2(k3_tarski(sK0))),sK0)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f373])).

fof(f1892,plain,
    ( spl8_256
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f1740,f207,f1890])).

fof(f207,plain,
    ( spl8_16
  <=> sP6(sK2(k3_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f1740,plain,
    ( r2_hidden(sK2(k3_tarski(sK0)),sK7(sK0,sK2(k3_tarski(sK0))))
    | ~ spl8_16 ),
    inference(resolution,[],[f208,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,sK7(X0,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',d4_tarski)).

fof(f208,plain,
    ( sP6(sK2(k3_tarski(sK0)),sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f207])).

fof(f1708,plain,
    ( ~ spl8_40
    | ~ spl8_44 ),
    inference(avatar_contradiction_clause,[],[f1707])).

fof(f1707,plain,
    ( $false
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f545,f468])).

fof(f468,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl8_44
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f545,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_40 ),
    inference(resolution,[],[f392,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',t7_boole)).

fof(f392,plain,
    ( r2_hidden(sK7(sK0,sK1(k3_tarski(sK0))),sK0)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl8_40
  <=> r2_hidden(sK7(sK0,sK1(k3_tarski(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f1692,plain,
    ( spl8_5
    | ~ spl8_34 ),
    inference(avatar_contradiction_clause,[],[f1691])).

fof(f1691,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f1688,f125])).

fof(f125,plain,
    ( ~ v1_ordinal1(k3_tarski(sK0))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_5
  <=> ~ v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1688,plain,
    ( v1_ordinal1(k3_tarski(sK0))
    | ~ spl8_34 ),
    inference(resolution,[],[f364,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',d2_ordinal1)).

fof(f364,plain,
    ( r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl8_34
  <=> r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f1687,plain,
    ( spl8_35
    | ~ spl8_234 ),
    inference(avatar_contradiction_clause,[],[f1686])).

fof(f1686,plain,
    ( $false
    | ~ spl8_35
    | ~ spl8_234 ),
    inference(subsumption_resolution,[],[f1677,f361])).

fof(f361,plain,
    ( ~ r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl8_35
  <=> ~ r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1677,plain,
    ( r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_234 ),
    inference(resolution,[],[f1662,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',t92_zfmisc_1)).

fof(f1662,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | ~ spl8_234 ),
    inference(avatar_component_clause,[],[f1661])).

fof(f1661,plain,
    ( spl8_234
  <=> r2_hidden(sK1(k3_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_234])])).

fof(f1663,plain,
    ( spl8_234
    | spl8_45
    | ~ spl8_218 ),
    inference(avatar_split_clause,[],[f1592,f1589,f470,f1661])).

fof(f470,plain,
    ( spl8_45
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f1589,plain,
    ( spl8_218
  <=> m1_subset_1(sK1(k3_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_218])])).

fof(f1592,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | ~ spl8_45
    | ~ spl8_218 ),
    inference(resolution,[],[f1590,f538])).

fof(f538,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r2_hidden(X0,sK0) )
    | ~ spl8_45 ),
    inference(resolution,[],[f471,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',t2_subset)).

fof(f471,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f470])).

fof(f1590,plain,
    ( m1_subset_1(sK1(k3_tarski(sK0)),sK0)
    | ~ spl8_218 ),
    inference(avatar_component_clause,[],[f1589])).

fof(f1591,plain,
    ( spl8_218
    | ~ spl8_62
    | ~ spl8_198 ),
    inference(avatar_split_clause,[],[f1580,f1402,f609,f1589])).

fof(f609,plain,
    ( spl8_62
  <=> r2_hidden(sK1(k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f1402,plain,
    ( spl8_198
  <=> m1_subset_1(sK7(sK0,sK1(k3_tarski(sK0))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_198])])).

fof(f1580,plain,
    ( m1_subset_1(sK1(k3_tarski(sK0)),sK0)
    | ~ spl8_62
    | ~ spl8_198 ),
    inference(resolution,[],[f1403,f648])).

fof(f648,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK7(sK0,sK1(k3_tarski(sK0))),k1_zfmisc_1(X2))
        | m1_subset_1(sK1(k3_tarski(sK0)),X2) )
    | ~ spl8_62 ),
    inference(resolution,[],[f610,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',t4_subset)).

fof(f610,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0))))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f609])).

fof(f1403,plain,
    ( m1_subset_1(sK7(sK0,sK1(k3_tarski(sK0))),k1_zfmisc_1(sK0))
    | ~ spl8_198 ),
    inference(avatar_component_clause,[],[f1402])).

fof(f1404,plain,
    ( spl8_198
    | ~ spl8_136 ),
    inference(avatar_split_clause,[],[f1025,f1015,f1402])).

fof(f1015,plain,
    ( spl8_136
  <=> r1_tarski(sK7(sK0,sK1(k3_tarski(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_136])])).

fof(f1025,plain,
    ( m1_subset_1(sK7(sK0,sK1(k3_tarski(sK0))),k1_zfmisc_1(sK0))
    | ~ spl8_136 ),
    inference(resolution,[],[f1016,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',t3_subset)).

fof(f1016,plain,
    ( r1_tarski(sK7(sK0,sK1(k3_tarski(sK0))),sK0)
    | ~ spl8_136 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f1067,plain,
    ( ~ spl8_60
    | ~ spl8_90
    | spl8_119 ),
    inference(avatar_contradiction_clause,[],[f1066])).

fof(f1066,plain,
    ( $false
    | ~ spl8_60
    | ~ spl8_90
    | ~ spl8_119 ),
    inference(subsumption_resolution,[],[f1065,f922])).

fof(f922,plain,
    ( ~ v3_ordinal1(sK3(k3_tarski(sK0)))
    | ~ spl8_119 ),
    inference(avatar_component_clause,[],[f921])).

fof(f921,plain,
    ( spl8_119
  <=> ~ v3_ordinal1(sK3(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f1065,plain,
    ( v3_ordinal1(sK3(k3_tarski(sK0)))
    | ~ spl8_60
    | ~ spl8_90 ),
    inference(subsumption_resolution,[],[f621,f792])).

fof(f792,plain,
    ( v3_ordinal1(sK7(sK0,sK3(k3_tarski(sK0))))
    | ~ spl8_90 ),
    inference(avatar_component_clause,[],[f791])).

fof(f791,plain,
    ( spl8_90
  <=> v3_ordinal1(sK7(sK0,sK3(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f621,plain,
    ( ~ v3_ordinal1(sK7(sK0,sK3(k3_tarski(sK0))))
    | v3_ordinal1(sK3(k3_tarski(sK0)))
    | ~ spl8_60 ),
    inference(resolution,[],[f603,f78])).

fof(f603,plain,
    ( r2_hidden(sK3(k3_tarski(sK0)),sK7(sK0,sK3(k3_tarski(sK0))))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f602])).

fof(f602,plain,
    ( spl8_60
  <=> r2_hidden(sK3(k3_tarski(sK0)),sK7(sK0,sK3(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f1017,plain,
    ( spl8_136
    | ~ spl8_40
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f1003,f798,f391,f1015])).

fof(f798,plain,
    ( spl8_92
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f1003,plain,
    ( r1_tarski(sK7(sK0,sK1(k3_tarski(sK0))),sK0)
    | ~ spl8_40
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f539,f799])).

fof(f799,plain,
    ( v1_ordinal1(sK0)
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f798])).

fof(f539,plain,
    ( r1_tarski(sK7(sK0,sK1(k3_tarski(sK0))),sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl8_40 ),
    inference(resolution,[],[f392,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f823,plain,
    ( ~ spl8_0
    | spl8_93 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_93 ),
    inference(subsumption_resolution,[],[f819,f108])).

fof(f819,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl8_93 ),
    inference(resolution,[],[f802,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',cc1_ordinal1)).

fof(f802,plain,
    ( ~ v1_ordinal1(sK0)
    | ~ spl8_93 ),
    inference(avatar_component_clause,[],[f801])).

fof(f801,plain,
    ( spl8_93
  <=> ~ v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f793,plain,
    ( spl8_90
    | ~ spl8_0
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f535,f383,f107,f791])).

fof(f383,plain,
    ( spl8_38
  <=> r2_hidden(sK7(sK0,sK3(k3_tarski(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f535,plain,
    ( v3_ordinal1(sK7(sK0,sK3(k3_tarski(sK0))))
    | ~ spl8_0
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f528,f108])).

fof(f528,plain,
    ( ~ v3_ordinal1(sK0)
    | v3_ordinal1(sK7(sK0,sK3(k3_tarski(sK0))))
    | ~ spl8_38 ),
    inference(resolution,[],[f384,f78])).

fof(f384,plain,
    ( r2_hidden(sK7(sK0,sK3(k3_tarski(sK0))),sK0)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f383])).

fof(f611,plain,
    ( spl8_62
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f450,f264,f609])).

fof(f264,plain,
    ( spl8_26
  <=> sP6(sK1(k3_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f450,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0))))
    | ~ spl8_26 ),
    inference(resolution,[],[f265,f88])).

fof(f265,plain,
    ( sP6(sK1(k3_tarski(sK0)),sK0)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f264])).

fof(f604,plain,
    ( spl8_60
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f423,f214,f602])).

fof(f214,plain,
    ( spl8_18
  <=> sP6(sK3(k3_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f423,plain,
    ( r2_hidden(sK3(k3_tarski(sK0)),sK7(sK0,sK3(k3_tarski(sK0))))
    | ~ spl8_18 ),
    inference(resolution,[],[f215,f88])).

fof(f215,plain,
    ( sP6(sK3(k3_tarski(sK0)),sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f393,plain,
    ( spl8_40
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f306,f264,f391])).

fof(f306,plain,
    ( r2_hidden(sK7(sK0,sK1(k3_tarski(sK0))),sK0)
    | ~ spl8_26 ),
    inference(resolution,[],[f265,f89])).

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(sK7(X0,X2),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f385,plain,
    ( spl8_38
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f221,f214,f383])).

fof(f221,plain,
    ( r2_hidden(sK7(sK0,sK3(k3_tarski(sK0))),sK0)
    | ~ spl8_18 ),
    inference(resolution,[],[f215,f89])).

fof(f375,plain,
    ( spl8_36
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f218,f207,f373])).

fof(f218,plain,
    ( r2_hidden(sK7(sK0,sK2(k3_tarski(sK0))),sK0)
    | ~ spl8_16 ),
    inference(resolution,[],[f208,f89])).

fof(f266,plain,
    ( spl8_26
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f249,f144,f264])).

fof(f144,plain,
    ( spl8_8
  <=> r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f249,plain,
    ( sP6(sK1(k3_tarski(sK0)),sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f145,f100])).

fof(f100,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_tarski(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f145,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f216,plain,
    ( spl8_18
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f178,f164,f214])).

fof(f164,plain,
    ( spl8_12
  <=> r2_hidden(sK3(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f178,plain,
    ( sP6(sK3(k3_tarski(sK0)),sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f165,f100])).

fof(f165,plain,
    ( r2_hidden(sK3(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f209,plain,
    ( spl8_16
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f167,f154,f207])).

fof(f154,plain,
    ( spl8_10
  <=> r2_hidden(sK2(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f167,plain,
    ( sP6(sK2(k3_tarski(sK0)),sK0)
    | ~ spl8_10 ),
    inference(resolution,[],[f155,f100])).

fof(f155,plain,
    ( r2_hidden(sK2(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f166,plain,
    ( spl8_12
    | spl8_7 ),
    inference(avatar_split_clause,[],[f138,f130,f164])).

fof(f138,plain,
    ( r2_hidden(sK3(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_7 ),
    inference(resolution,[],[f131,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f156,plain,
    ( spl8_10
    | spl8_7 ),
    inference(avatar_split_clause,[],[f137,f130,f154])).

fof(f137,plain,
    ( r2_hidden(sK2(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_7 ),
    inference(resolution,[],[f131,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f146,plain,
    ( spl8_8
    | spl8_5 ),
    inference(avatar_split_clause,[],[f134,f124,f144])).

fof(f134,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl8_5 ),
    inference(resolution,[],[f125,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f132,plain,
    ( ~ spl8_5
    | ~ spl8_7
    | spl8_3 ),
    inference(avatar_split_clause,[],[f119,f114,f130,f124])).

fof(f114,plain,
    ( spl8_3
  <=> ~ v3_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f119,plain,
    ( ~ v2_ordinal1(k3_tarski(sK0))
    | ~ v1_ordinal1(k3_tarski(sK0))
    | ~ spl8_3 ),
    inference(resolution,[],[f115,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',d4_ordinal1)).

fof(f115,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f58,f114])).

fof(f58,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t30_ordinal1.p',t30_ordinal1)).

fof(f109,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f57,f107])).

fof(f57,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
