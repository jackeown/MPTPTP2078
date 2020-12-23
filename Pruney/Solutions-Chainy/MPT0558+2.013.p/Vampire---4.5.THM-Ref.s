%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 186 expanded)
%              Number of leaves         :   30 (  87 expanded)
%              Depth                    :    6
%              Number of atoms          :  327 ( 527 expanded)
%              Number of equality atoms :   70 ( 112 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f730,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f67,f71,f75,f88,f107,f174,f200,f219,f393,f427,f447,f452,f715,f729])).

fof(f729,plain,
    ( spl2_1
    | ~ spl2_12
    | ~ spl2_75
    | ~ spl2_120 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | spl2_1
    | ~ spl2_12
    | ~ spl2_75
    | ~ spl2_120 ),
    inference(subsumption_resolution,[],[f727,f36])).

fof(f36,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_1
  <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f727,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ spl2_12
    | ~ spl2_75
    | ~ spl2_120 ),
    inference(forward_demodulation,[],[f717,f87])).

fof(f87,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_12
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f717,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl2_75
    | ~ spl2_120 ),
    inference(superposition,[],[f446,f714])).

fof(f714,plain,
    ( k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))
    | ~ spl2_120 ),
    inference(avatar_component_clause,[],[f712])).

fof(f712,plain,
    ( spl2_120
  <=> k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f446,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X1)) = k9_relat_1(sK1,k9_relat_1(sK0,X1))
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl2_75
  <=> ! [X1] : k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X1)) = k9_relat_1(sK1,k9_relat_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f715,plain,
    ( spl2_120
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f710,f450,f53,f44,f39,f712])).

fof(f39,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f450,plain,
    ( spl2_76
  <=> ! [X2] :
        ( k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X2)
        | ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f710,plain,
    ( k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_76 ),
    inference(subsumption_resolution,[],[f709,f46])).

fof(f46,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f709,plain,
    ( k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_76 ),
    inference(subsumption_resolution,[],[f708,f41])).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f708,plain,
    ( k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_5
    | ~ spl2_76 ),
    inference(resolution,[],[f451,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f53])).

% (18247)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
fof(f451,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X2)
        | k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X2) )
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f450])).

fof(f452,plain,
    ( spl2_76
    | ~ spl2_8
    | ~ spl2_66
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f448,f413,f391,f65,f450])).

fof(f65,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f391,plain,
    ( spl2_66
  <=> ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f413,plain,
    ( spl2_71
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f448,plain,
    ( ! [X2] :
        ( k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X2)
        | ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X2) )
    | ~ spl2_8
    | ~ spl2_66
    | ~ spl2_71 ),
    inference(forward_demodulation,[],[f431,f392])).

fof(f392,plain,
    ( ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK0,sK1))
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f391])).

fof(f431,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X2)
        | k5_relat_1(sK0,sK1) = k5_relat_1(k6_relat_1(X2),k5_relat_1(sK0,sK1)) )
    | ~ spl2_8
    | ~ spl2_71 ),
    inference(resolution,[],[f414,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f414,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f413])).

fof(f447,plain,
    ( spl2_75
    | ~ spl2_7
    | ~ spl2_33
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f443,f413,f198,f61,f445])).

fof(f61,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f198,plain,
    ( spl2_33
  <=> ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f443,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X1)) = k9_relat_1(sK1,k9_relat_1(sK0,X1))
    | ~ spl2_7
    | ~ spl2_33
    | ~ spl2_71 ),
    inference(forward_demodulation,[],[f430,f199])).

fof(f199,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f198])).

fof(f430,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X1)) = k9_relat_1(k5_relat_1(sK0,sK1),X1)
    | ~ spl2_7
    | ~ spl2_71 ),
    inference(resolution,[],[f414,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f427,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10
    | spl2_71 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10
    | spl2_71 ),
    inference(subsumption_resolution,[],[f425,f46])).

fof(f425,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_10
    | spl2_71 ),
    inference(subsumption_resolution,[],[f424,f41])).

fof(f424,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_10
    | spl2_71 ),
    inference(resolution,[],[f415,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f415,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl2_71 ),
    inference(avatar_component_clause,[],[f413])).

fof(f393,plain,
    ( spl2_66
    | ~ spl2_2
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f385,f217,f39,f391])).

fof(f217,plain,
    ( spl2_37
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k6_relat_1(X3),k5_relat_1(sK0,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f385,plain,
    ( ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_37 ),
    inference(resolution,[],[f218,f41])).

fof(f218,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k6_relat_1(X3),k5_relat_1(sK0,X2)) )
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl2_37
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f210,f105,f44,f217])).

fof(f105,plain,
    ( spl2_16
  <=> ! [X3,X2,X4] :
        ( k7_relat_1(k5_relat_1(X2,X3),X4) = k5_relat_1(k6_relat_1(X4),k5_relat_1(X2,X3))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f210,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k6_relat_1(X3),k5_relat_1(sK0,X2)) )
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(resolution,[],[f106,f46])).

fof(f106,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | k7_relat_1(k5_relat_1(X2,X3),X4) = k5_relat_1(k6_relat_1(X4),k5_relat_1(X2,X3)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f200,plain,
    ( spl2_33
    | ~ spl2_2
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f194,f172,f39,f198])).

fof(f172,plain,
    ( spl2_28
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f194,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))
    | ~ spl2_2
    | ~ spl2_28 ),
    inference(resolution,[],[f173,f41])).

fof(f173,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( spl2_28
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f165,f69,f44,f172])).

fof(f69,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f165,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) )
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f70,f46])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f107,plain,
    ( spl2_16
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f95,f73,f57,f105])).

fof(f57,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f95,plain,
    ( ! [X4,X2,X3] :
        ( k7_relat_1(k5_relat_1(X2,X3),X4) = k5_relat_1(k6_relat_1(X4),k5_relat_1(X2,X3))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(resolution,[],[f58,f74])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f88,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f77,f49,f44,f85])).

fof(f49,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f77,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f50,f46])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f75,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f71,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f67,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f63,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f59,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f55,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f51,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f34])).

fof(f25,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:34:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.42  % (18252)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (18257)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.43  % (18251)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (18250)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (18249)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.44  % (18251)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f730,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f67,f71,f75,f88,f107,f174,f200,f219,f393,f427,f447,f452,f715,f729])).
% 0.22/0.44  fof(f729,plain,(
% 0.22/0.44    spl2_1 | ~spl2_12 | ~spl2_75 | ~spl2_120),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f728])).
% 0.22/0.44  fof(f728,plain,(
% 0.22/0.44    $false | (spl2_1 | ~spl2_12 | ~spl2_75 | ~spl2_120)),
% 0.22/0.44    inference(subsumption_resolution,[],[f727,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) | spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl2_1 <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f727,plain,(
% 0.22/0.44    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) | (~spl2_12 | ~spl2_75 | ~spl2_120)),
% 0.22/0.44    inference(forward_demodulation,[],[f717,f87])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl2_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f85])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    spl2_12 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.44  fof(f717,plain,(
% 0.22/0.44    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0))) | (~spl2_75 | ~spl2_120)),
% 0.22/0.44    inference(superposition,[],[f446,f714])).
% 0.22/0.44  fof(f714,plain,(
% 0.22/0.44    k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) | ~spl2_120),
% 0.22/0.44    inference(avatar_component_clause,[],[f712])).
% 0.22/0.44  fof(f712,plain,(
% 0.22/0.44    spl2_120 <=> k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).
% 0.22/0.44  fof(f446,plain,(
% 0.22/0.44    ( ! [X1] : (k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X1)) = k9_relat_1(sK1,k9_relat_1(sK0,X1))) ) | ~spl2_75),
% 0.22/0.44    inference(avatar_component_clause,[],[f445])).
% 0.22/0.44  fof(f445,plain,(
% 0.22/0.44    spl2_75 <=> ! [X1] : k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X1)) = k9_relat_1(sK1,k9_relat_1(sK0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 0.22/0.44  fof(f715,plain,(
% 0.22/0.44    spl2_120 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_76),
% 0.22/0.44    inference(avatar_split_clause,[],[f710,f450,f53,f44,f39,f712])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    spl2_2 <=> v1_relat_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl2_3 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl2_5 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f450,plain,(
% 0.22/0.44    spl2_76 <=> ! [X2] : (k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X2) | ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 0.22/0.44  fof(f710,plain,(
% 0.22/0.44    k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_76)),
% 0.22/0.44    inference(subsumption_resolution,[],[f709,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    v1_relat_1(sK0) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f44])).
% 0.22/0.44  fof(f709,plain,(
% 0.22/0.44    k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_2 | ~spl2_5 | ~spl2_76)),
% 0.22/0.44    inference(subsumption_resolution,[],[f708,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    v1_relat_1(sK1) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f39])).
% 0.22/0.44  fof(f708,plain,(
% 0.22/0.44    k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | (~spl2_5 | ~spl2_76)),
% 0.22/0.44    inference(resolution,[],[f451,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  % (18247)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.44  fof(f451,plain,(
% 0.22/0.44    ( ! [X2] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X2) | k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X2)) ) | ~spl2_76),
% 0.22/0.44    inference(avatar_component_clause,[],[f450])).
% 0.22/0.44  fof(f452,plain,(
% 0.22/0.44    spl2_76 | ~spl2_8 | ~spl2_66 | ~spl2_71),
% 0.22/0.44    inference(avatar_split_clause,[],[f448,f413,f391,f65,f450])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    spl2_8 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.44  fof(f391,plain,(
% 0.22/0.44    spl2_66 <=> ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 0.22/0.44  fof(f413,plain,(
% 0.22/0.44    spl2_71 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.22/0.44  fof(f448,plain,(
% 0.22/0.44    ( ! [X2] : (k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X2) | ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X2)) ) | (~spl2_8 | ~spl2_66 | ~spl2_71)),
% 0.22/0.44    inference(forward_demodulation,[],[f431,f392])).
% 0.22/0.44  fof(f392,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK0,sK1))) ) | ~spl2_66),
% 0.22/0.44    inference(avatar_component_clause,[],[f391])).
% 0.22/0.44  fof(f431,plain,(
% 0.22/0.44    ( ! [X2] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X2) | k5_relat_1(sK0,sK1) = k5_relat_1(k6_relat_1(X2),k5_relat_1(sK0,sK1))) ) | (~spl2_8 | ~spl2_71)),
% 0.22/0.44    inference(resolution,[],[f414,f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) ) | ~spl2_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f65])).
% 0.22/0.44  fof(f414,plain,(
% 0.22/0.44    v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl2_71),
% 0.22/0.44    inference(avatar_component_clause,[],[f413])).
% 0.22/0.44  fof(f447,plain,(
% 0.22/0.44    spl2_75 | ~spl2_7 | ~spl2_33 | ~spl2_71),
% 0.22/0.44    inference(avatar_split_clause,[],[f443,f413,f198,f61,f445])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl2_7 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.45  fof(f198,plain,(
% 0.22/0.45    spl2_33 <=> ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.22/0.45  fof(f443,plain,(
% 0.22/0.45    ( ! [X1] : (k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X1)) = k9_relat_1(sK1,k9_relat_1(sK0,X1))) ) | (~spl2_7 | ~spl2_33 | ~spl2_71)),
% 0.22/0.45    inference(forward_demodulation,[],[f430,f199])).
% 0.22/0.45  fof(f199,plain,(
% 0.22/0.45    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) ) | ~spl2_33),
% 0.22/0.45    inference(avatar_component_clause,[],[f198])).
% 0.22/0.45  fof(f430,plain,(
% 0.22/0.45    ( ! [X1] : (k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X1)) = k9_relat_1(k5_relat_1(sK0,sK1),X1)) ) | (~spl2_7 | ~spl2_71)),
% 0.22/0.45    inference(resolution,[],[f414,f62])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f61])).
% 0.22/0.45  fof(f427,plain,(
% 0.22/0.45    ~spl2_2 | ~spl2_3 | ~spl2_10 | spl2_71),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f426])).
% 0.22/0.45  fof(f426,plain,(
% 0.22/0.45    $false | (~spl2_2 | ~spl2_3 | ~spl2_10 | spl2_71)),
% 0.22/0.45    inference(subsumption_resolution,[],[f425,f46])).
% 0.22/0.45  fof(f425,plain,(
% 0.22/0.45    ~v1_relat_1(sK0) | (~spl2_2 | ~spl2_10 | spl2_71)),
% 0.22/0.45    inference(subsumption_resolution,[],[f424,f41])).
% 0.22/0.45  fof(f424,plain,(
% 0.22/0.45    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | (~spl2_10 | spl2_71)),
% 0.22/0.45    inference(resolution,[],[f415,f74])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f73])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    spl2_10 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.45  fof(f415,plain,(
% 0.22/0.45    ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl2_71),
% 0.22/0.45    inference(avatar_component_clause,[],[f413])).
% 0.22/0.45  fof(f393,plain,(
% 0.22/0.45    spl2_66 | ~spl2_2 | ~spl2_37),
% 0.22/0.45    inference(avatar_split_clause,[],[f385,f217,f39,f391])).
% 0.22/0.45  fof(f217,plain,(
% 0.22/0.45    spl2_37 <=> ! [X3,X2] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k6_relat_1(X3),k5_relat_1(sK0,X2)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.22/0.45  fof(f385,plain,(
% 0.22/0.45    ( ! [X0] : (k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK0,sK1))) ) | (~spl2_2 | ~spl2_37)),
% 0.22/0.45    inference(resolution,[],[f218,f41])).
% 0.22/0.45  fof(f218,plain,(
% 0.22/0.45    ( ! [X2,X3] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k6_relat_1(X3),k5_relat_1(sK0,X2))) ) | ~spl2_37),
% 0.22/0.45    inference(avatar_component_clause,[],[f217])).
% 0.22/0.45  fof(f219,plain,(
% 0.22/0.45    spl2_37 | ~spl2_3 | ~spl2_16),
% 0.22/0.45    inference(avatar_split_clause,[],[f210,f105,f44,f217])).
% 0.22/0.45  fof(f105,plain,(
% 0.22/0.45    spl2_16 <=> ! [X3,X2,X4] : (k7_relat_1(k5_relat_1(X2,X3),X4) = k5_relat_1(k6_relat_1(X4),k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.45  fof(f210,plain,(
% 0.22/0.45    ( ! [X2,X3] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k6_relat_1(X3),k5_relat_1(sK0,X2))) ) | (~spl2_3 | ~spl2_16)),
% 0.22/0.45    inference(resolution,[],[f106,f46])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k7_relat_1(k5_relat_1(X2,X3),X4) = k5_relat_1(k6_relat_1(X4),k5_relat_1(X2,X3))) ) | ~spl2_16),
% 0.22/0.45    inference(avatar_component_clause,[],[f105])).
% 0.22/0.45  fof(f200,plain,(
% 0.22/0.45    spl2_33 | ~spl2_2 | ~spl2_28),
% 0.22/0.45    inference(avatar_split_clause,[],[f194,f172,f39,f198])).
% 0.22/0.45  fof(f172,plain,(
% 0.22/0.45    spl2_28 <=> ! [X3,X2] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.45  fof(f194,plain,(
% 0.22/0.45    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) ) | (~spl2_2 | ~spl2_28)),
% 0.22/0.45    inference(resolution,[],[f173,f41])).
% 0.22/0.45  fof(f173,plain,(
% 0.22/0.45    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3))) ) | ~spl2_28),
% 0.22/0.45    inference(avatar_component_clause,[],[f172])).
% 0.22/0.45  fof(f174,plain,(
% 0.22/0.45    spl2_28 | ~spl2_3 | ~spl2_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f165,f69,f44,f172])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    spl2_9 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.45  fof(f165,plain,(
% 0.22/0.45    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3))) ) | (~spl2_3 | ~spl2_9)),
% 0.22/0.45    inference(resolution,[],[f70,f46])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) ) | ~spl2_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f69])).
% 0.22/0.45  fof(f107,plain,(
% 0.22/0.45    spl2_16 | ~spl2_6 | ~spl2_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f95,f73,f57,f105])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    spl2_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.45  fof(f95,plain,(
% 0.22/0.45    ( ! [X4,X2,X3] : (k7_relat_1(k5_relat_1(X2,X3),X4) = k5_relat_1(k6_relat_1(X4),k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | (~spl2_6 | ~spl2_10)),
% 0.22/0.45    inference(resolution,[],[f58,f74])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f57])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    spl2_12 | ~spl2_3 | ~spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f77,f49,f44,f85])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl2_4 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl2_3 | ~spl2_4)),
% 0.22/0.45    inference(resolution,[],[f50,f46])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) ) | ~spl2_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f49])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    spl2_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f32,f73])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    spl2_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f31,f69])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    spl2_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f65])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    spl2_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f29,f61])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    spl2_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f57])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f53])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f49])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    v1_relat_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f39])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    v1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ~spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f34])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (18251)------------------------------
% 0.22/0.45  % (18251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (18251)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (18251)Memory used [KB]: 11001
% 0.22/0.45  % (18251)Time elapsed: 0.018 s
% 0.22/0.45  % (18251)------------------------------
% 0.22/0.45  % (18251)------------------------------
% 0.22/0.45  % (18243)Success in time 0.088 s
%------------------------------------------------------------------------------
