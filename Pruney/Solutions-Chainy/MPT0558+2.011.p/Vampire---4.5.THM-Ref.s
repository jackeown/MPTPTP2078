%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 164 expanded)
%              Number of leaves         :   26 (  80 expanded)
%              Depth                    :    6
%              Number of atoms          :  266 ( 451 expanded)
%              Number of equality atoms :   65 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f44,f48,f52,f56,f60,f72,f88,f92,f104,f115,f141,f160,f186,f330,f388,f403])).

fof(f403,plain,
    ( spl2_1
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_66 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | spl2_1
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_66 ),
    inference(subsumption_resolution,[],[f401,f29])).

fof(f29,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f401,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_66 ),
    inference(forward_demodulation,[],[f399,f103])).

fof(f103,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_16
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f399,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl2_10
    | ~ spl2_66 ),
    inference(superposition,[],[f387,f71])).

fof(f71,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_10
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f387,plain,
    ( ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl2_66
  <=> ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f388,plain,
    ( spl2_66
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_32
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f384,f328,f184,f139,f32,f386])).

fof(f32,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f139,plain,
    ( spl2_23
  <=> ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k7_relat_1(sK0,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f184,plain,
    ( spl2_32
  <=> ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f328,plain,
    ( spl2_57
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f384,plain,
    ( ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_32
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f383,f185])).

fof(f185,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f184])).

fof(f383,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f380,f140])).

fof(f140,plain,
    ( ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k7_relat_1(sK0,X0),sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f139])).

fof(f380,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))
    | ~ spl2_2
    | ~ spl2_57 ),
    inference(resolution,[],[f329,f34])).

fof(f34,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f329,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3)) )
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f328])).

fof(f330,plain,
    ( spl2_57
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f321,f90,f37,f328])).

fof(f37,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f90,plain,
    ( spl2_14
  <=> ! [X3,X2,X4] :
        ( k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f321,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3)) )
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(resolution,[],[f91,f39])).

fof(f39,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f91,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f186,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f180,f158,f32,f184])).

fof(f158,plain,
    ( spl2_27
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f180,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(resolution,[],[f159,f34])).

fof(f159,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f158])).

fof(f160,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f151,f54,f37,f158])).

fof(f54,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f151,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) )
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f55,f39])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f141,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f135,f113,f32,f139])).

fof(f113,plain,
    ( spl2_18
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k7_relat_1(sK0,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f135,plain,
    ( ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k7_relat_1(sK0,X0),sK1)
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f114,f34])).

fof(f114,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k7_relat_1(sK0,X3),X2) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f106,f50,f37,f113])).

fof(f50,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f106,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k7_relat_1(sK0,X3),X2) )
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f51,f39])).

% (23759)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
fof(f51,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f104,plain,
    ( spl2_16
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f99,f86,f69,f101])).

fof(f86,plain,
    ( spl2_13
  <=> ! [X1] : k2_relat_1(k7_relat_1(sK0,X1)) = k9_relat_1(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f99,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(superposition,[],[f87,f71])).

fof(f87,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(sK0,X1)) = k9_relat_1(sK0,X1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f92,plain,
    ( spl2_14
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f80,f58,f46,f90])).

fof(f46,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f58,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f80,plain,
    ( ! [X4,X2,X3] :
        ( k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f47,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f46])).

% (23757)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
fof(f88,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f79,f46,f37,f86])).

fof(f79,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(sK0,X1)) = k9_relat_1(sK0,X1)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f47,f39])).

fof(f72,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f62,f42,f37,f69])).

fof(f42,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f62,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_relat_1(X0)) = X0 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f60,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f56,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f52,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f48,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f44,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).

fof(f15,plain,
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

fof(f16,plain,
    ( ? [X1] :
        ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f27])).

fof(f20,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (23764)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.41  % (23762)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (23761)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (23765)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (23761)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f404,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f30,f35,f40,f44,f48,f52,f56,f60,f72,f88,f92,f104,f115,f141,f160,f186,f330,f388,f403])).
% 0.20/0.43  fof(f403,plain,(
% 0.20/0.43    spl2_1 | ~spl2_10 | ~spl2_16 | ~spl2_66),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f402])).
% 0.20/0.43  fof(f402,plain,(
% 0.20/0.43    $false | (spl2_1 | ~spl2_10 | ~spl2_16 | ~spl2_66)),
% 0.20/0.43    inference(subsumption_resolution,[],[f401,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) | spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    spl2_1 <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f401,plain,(
% 0.20/0.43    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) | (~spl2_10 | ~spl2_16 | ~spl2_66)),
% 0.20/0.43    inference(forward_demodulation,[],[f399,f103])).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl2_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f101])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    spl2_16 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.43  fof(f399,plain,(
% 0.20/0.43    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0))) | (~spl2_10 | ~spl2_66)),
% 0.20/0.43    inference(superposition,[],[f387,f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl2_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f69])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl2_10 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.43  fof(f387,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))) ) | ~spl2_66),
% 0.20/0.43    inference(avatar_component_clause,[],[f386])).
% 0.20/0.43  fof(f386,plain,(
% 0.20/0.43    spl2_66 <=> ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 0.20/0.43  fof(f388,plain,(
% 0.20/0.43    spl2_66 | ~spl2_2 | ~spl2_23 | ~spl2_32 | ~spl2_57),
% 0.20/0.43    inference(avatar_split_clause,[],[f384,f328,f184,f139,f32,f386])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    spl2_23 <=> ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k7_relat_1(sK0,X0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.43  fof(f184,plain,(
% 0.20/0.43    spl2_32 <=> ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.20/0.43  fof(f328,plain,(
% 0.20/0.43    spl2_57 <=> ! [X3,X2] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 0.20/0.43  fof(f384,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))) ) | (~spl2_2 | ~spl2_23 | ~spl2_32 | ~spl2_57)),
% 0.20/0.43    inference(forward_demodulation,[],[f383,f185])).
% 0.20/0.43  fof(f185,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) ) | ~spl2_32),
% 0.20/0.43    inference(avatar_component_clause,[],[f184])).
% 0.20/0.43  fof(f383,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))) ) | (~spl2_2 | ~spl2_23 | ~spl2_57)),
% 0.20/0.43    inference(forward_demodulation,[],[f380,f140])).
% 0.20/0.43  fof(f140,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k7_relat_1(sK0,X0),sK1)) ) | ~spl2_23),
% 0.20/0.43    inference(avatar_component_clause,[],[f139])).
% 0.20/0.43  fof(f380,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))) ) | (~spl2_2 | ~spl2_57)),
% 0.20/0.43    inference(resolution,[],[f329,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f32])).
% 0.20/0.43  fof(f329,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3))) ) | ~spl2_57),
% 0.20/0.43    inference(avatar_component_clause,[],[f328])).
% 0.20/0.43  fof(f330,plain,(
% 0.20/0.43    spl2_57 | ~spl2_3 | ~spl2_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f321,f90,f37,f328])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl2_3 <=> v1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    spl2_14 <=> ! [X3,X2,X4] : (k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4) | ~v1_relat_1(X3) | ~v1_relat_1(X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.43  fof(f321,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3))) ) | (~spl2_3 | ~spl2_14)),
% 0.20/0.43    inference(resolution,[],[f91,f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    v1_relat_1(sK0) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f37])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4)) ) | ~spl2_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f90])).
% 0.20/0.43  fof(f186,plain,(
% 0.20/0.43    spl2_32 | ~spl2_2 | ~spl2_27),
% 0.20/0.43    inference(avatar_split_clause,[],[f180,f158,f32,f184])).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    spl2_27 <=> ! [X3,X2] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.43  fof(f180,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) ) | (~spl2_2 | ~spl2_27)),
% 0.20/0.43    inference(resolution,[],[f159,f34])).
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3))) ) | ~spl2_27),
% 0.20/0.43    inference(avatar_component_clause,[],[f158])).
% 0.20/0.43  fof(f160,plain,(
% 0.20/0.43    spl2_27 | ~spl2_3 | ~spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f151,f54,f37,f158])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl2_7 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3))) ) | (~spl2_3 | ~spl2_7)),
% 0.20/0.43    inference(resolution,[],[f55,f39])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f54])).
% 0.20/0.43  fof(f141,plain,(
% 0.20/0.43    spl2_23 | ~spl2_2 | ~spl2_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f135,f113,f32,f139])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    spl2_18 <=> ! [X3,X2] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k7_relat_1(sK0,X3),X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k7_relat_1(sK0,X0),sK1)) ) | (~spl2_2 | ~spl2_18)),
% 0.20/0.43    inference(resolution,[],[f114,f34])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k7_relat_1(sK0,X3),X2)) ) | ~spl2_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f113])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    spl2_18 | ~spl2_3 | ~spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f106,f50,f37,f113])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl2_6 <=> ! [X1,X0,X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(sK0,X2),X3) = k5_relat_1(k7_relat_1(sK0,X3),X2)) ) | (~spl2_3 | ~spl2_6)),
% 0.20/0.43    inference(resolution,[],[f51,f39])).
% 0.20/0.43  % (23759)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) ) | ~spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f50])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    spl2_16 | ~spl2_10 | ~spl2_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f99,f86,f69,f101])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    spl2_13 <=> ! [X1] : k2_relat_1(k7_relat_1(sK0,X1)) = k9_relat_1(sK0,X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl2_10 | ~spl2_13)),
% 0.20/0.43    inference(superposition,[],[f87,f71])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    ( ! [X1] : (k2_relat_1(k7_relat_1(sK0,X1)) = k9_relat_1(sK0,X1)) ) | ~spl2_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f86])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    spl2_14 | ~spl2_5 | ~spl2_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f80,f58,f46,f90])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl2_5 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl2_8 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X4,X2,X3] : (k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | (~spl2_5 | ~spl2_8)),
% 0.20/0.43    inference(resolution,[],[f47,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f58])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f46])).
% 0.20/0.43  % (23757)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    spl2_13 | ~spl2_3 | ~spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f79,f46,f37,f86])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X1] : (k2_relat_1(k7_relat_1(sK0,X1)) = k9_relat_1(sK0,X1)) ) | (~spl2_3 | ~spl2_5)),
% 0.20/0.43    inference(resolution,[],[f47,f39])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl2_10 | ~spl2_3 | ~spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f62,f42,f37,f69])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl2_4 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | (~spl2_3 | ~spl2_4)),
% 0.20/0.43    inference(resolution,[],[f43,f39])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f42])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl2_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f58])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(flattening,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f54])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f50])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f46])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f42])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f18,f37])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.43    inference(negated_conjecture,[],[f6])).
% 0.20/0.43  fof(f6,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f19,f32])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    v1_relat_1(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f27])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (23761)------------------------------
% 0.20/0.43  % (23761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (23761)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (23761)Memory used [KB]: 10746
% 0.20/0.43  % (23761)Time elapsed: 0.033 s
% 0.20/0.43  % (23761)------------------------------
% 0.20/0.43  % (23761)------------------------------
% 0.20/0.44  % (23755)Success in time 0.086 s
%------------------------------------------------------------------------------
