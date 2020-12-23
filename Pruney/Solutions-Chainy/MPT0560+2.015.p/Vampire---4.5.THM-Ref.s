%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:01 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 172 expanded)
%              Number of leaves         :   29 (  84 expanded)
%              Depth                    :    6
%              Number of atoms          :  266 ( 443 expanded)
%              Number of equality atoms :   75 ( 126 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f61,f65,f69,f73,f77,f87,f93,f98,f109,f120,f126,f133,f143,f161,f171])).

fof(f171,plain,
    ( spl3_1
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_1
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f167,f34])).

fof(f34,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f167,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(superposition,[],[f160,f132])).

fof(f132,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK2),sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_21
  <=> sK1 = k9_relat_1(k6_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f160,plain,
    ( ! [X0,X1] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_26
  <=> ! [X1,X0] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f161,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f157,f141,f91,f42,f159])).

fof(f42,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f91,plain,
    ( spl3_14
  <=> ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f141,plain,
    ( spl3_23
  <=> ! [X3,X2,X4] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f157,plain,
    ( ! [X0,X1] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f155,f92])).

fof(f92,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f155,plain,
    ( ! [X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1))
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(resolution,[],[f142,f44])).

fof(f44,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f142,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl3_23
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f135,f75,f47,f141])).

fof(f47,plain,
    ( spl3_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f135,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4)) )
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f76,f48])).

fof(f48,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f133,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f128,f123,f107,f51,f130])).

fof(f51,plain,
    ( spl3_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,
    ( spl3_17
  <=> ! [X1,X2] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f123,plain,
    ( spl3_20
  <=> k6_relat_1(sK1) = k8_relat_1(sK2,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f128,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK2),sK1)
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f127,f52])).

fof(f52,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f127,plain,
    ( k9_relat_1(k6_relat_1(sK2),sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(superposition,[],[f108,f125])).

fof(f125,plain,
    ( k6_relat_1(sK1) = k8_relat_1(sK2,k6_relat_1(sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f123])).

fof(f108,plain,
    ( ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f107])).

fof(f126,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f121,f118,f37,f123])).

fof(f37,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f118,plain,
    ( spl3_19
  <=> ! [X1,X2] :
        ( ~ r1_tarski(X1,X2)
        | k6_relat_1(X1) = k8_relat_1(X2,k6_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f121,plain,
    ( k6_relat_1(sK1) = k8_relat_1(sK2,k6_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f119,f39])).

fof(f39,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f119,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X1,X2)
        | k6_relat_1(X1) = k8_relat_1(X2,k6_relat_1(X1)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f116,f71,f51,f47,f118])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f116,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X1,X2)
        | k6_relat_1(X1) = k8_relat_1(X2,k6_relat_1(X1)) )
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f111,f52])).

fof(f111,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X1)),X2)
        | k6_relat_1(X1) = k8_relat_1(X2,k6_relat_1(X1)) )
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(resolution,[],[f72,f48])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f109,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f105,f96,f67,f47,f107])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f96,plain,
    ( spl3_15
  <=> ! [X1,X2] : k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f105,plain,
    ( ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f100,f97])).

fof(f97,plain,
    ( ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f100,plain,
    ( ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f68,f48])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f98,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f94,f85,f63,f47,f96])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f85,plain,
    ( spl3_13
  <=> ! [X1,X2] : k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f94,plain,
    ( ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f89,f86])).

fof(f86,plain,
    ( ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f89,plain,
    ( ! [X2,X1] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f64,f48])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f93,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f88,f63,f42,f91])).

fof(f88,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f64,f44])).

fof(f87,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f79,f59,f47,f85])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f79,plain,
    ( ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f60,f48])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f77,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f73,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f69,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f61,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f32])).

fof(f22,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.41  % (772)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.42  % (773)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.42  % (772)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f172,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f61,f65,f69,f73,f77,f87,f93,f98,f109,f120,f126,f133,f143,f161,f171])).
% 0.14/0.42  fof(f171,plain,(
% 0.14/0.42    spl3_1 | ~spl3_21 | ~spl3_26),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f170])).
% 0.14/0.42  fof(f170,plain,(
% 0.14/0.42    $false | (spl3_1 | ~spl3_21 | ~spl3_26)),
% 0.14/0.42    inference(subsumption_resolution,[],[f167,f34])).
% 0.14/0.42  fof(f34,plain,(
% 0.14/0.42    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) | spl3_1),
% 0.14/0.42    inference(avatar_component_clause,[],[f32])).
% 0.14/0.42  fof(f32,plain,(
% 0.14/0.42    spl3_1 <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.14/0.42  fof(f167,plain,(
% 0.14/0.42    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) | (~spl3_21 | ~spl3_26)),
% 0.14/0.42    inference(superposition,[],[f160,f132])).
% 0.14/0.42  fof(f132,plain,(
% 0.14/0.42    sK1 = k9_relat_1(k6_relat_1(sK2),sK1) | ~spl3_21),
% 0.14/0.42    inference(avatar_component_clause,[],[f130])).
% 0.14/0.42  fof(f130,plain,(
% 0.14/0.42    spl3_21 <=> sK1 = k9_relat_1(k6_relat_1(sK2),sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.14/0.42  fof(f160,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)) ) | ~spl3_26),
% 0.14/0.42    inference(avatar_component_clause,[],[f159])).
% 0.14/0.42  fof(f159,plain,(
% 0.14/0.42    spl3_26 <=> ! [X1,X0] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.14/0.42  fof(f161,plain,(
% 0.14/0.42    spl3_26 | ~spl3_3 | ~spl3_14 | ~spl3_23),
% 0.14/0.42    inference(avatar_split_clause,[],[f157,f141,f91,f42,f159])).
% 0.14/0.42  fof(f42,plain,(
% 0.14/0.42    spl3_3 <=> v1_relat_1(sK0)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.14/0.42  fof(f91,plain,(
% 0.14/0.42    spl3_14 <=> ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.14/0.42  fof(f141,plain,(
% 0.14/0.42    spl3_23 <=> ! [X3,X2,X4] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4)))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.14/0.42  fof(f157,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)) ) | (~spl3_3 | ~spl3_14 | ~spl3_23)),
% 0.14/0.42    inference(forward_demodulation,[],[f155,f92])).
% 0.14/0.42  fof(f92,plain,(
% 0.14/0.42    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) ) | ~spl3_14),
% 0.14/0.42    inference(avatar_component_clause,[],[f91])).
% 0.14/0.42  fof(f155,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1))) ) | (~spl3_3 | ~spl3_23)),
% 0.14/0.42    inference(resolution,[],[f142,f44])).
% 0.14/0.42  fof(f44,plain,(
% 0.14/0.42    v1_relat_1(sK0) | ~spl3_3),
% 0.14/0.42    inference(avatar_component_clause,[],[f42])).
% 0.14/0.42  fof(f142,plain,(
% 0.14/0.42    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4))) ) | ~spl3_23),
% 0.14/0.42    inference(avatar_component_clause,[],[f141])).
% 0.14/0.42  fof(f143,plain,(
% 0.14/0.42    spl3_23 | ~spl3_4 | ~spl3_11),
% 0.14/0.42    inference(avatar_split_clause,[],[f135,f75,f47,f141])).
% 0.14/0.42  fof(f47,plain,(
% 0.14/0.42    spl3_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.14/0.42  fof(f75,plain,(
% 0.14/0.42    spl3_11 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.14/0.42  fof(f135,plain,(
% 0.14/0.42    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4))) ) | (~spl3_4 | ~spl3_11)),
% 0.14/0.42    inference(resolution,[],[f76,f48])).
% 0.14/0.42  fof(f48,plain,(
% 0.14/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_4),
% 0.14/0.42    inference(avatar_component_clause,[],[f47])).
% 0.14/0.42  fof(f76,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) ) | ~spl3_11),
% 0.14/0.42    inference(avatar_component_clause,[],[f75])).
% 0.14/0.42  fof(f133,plain,(
% 0.14/0.42    spl3_21 | ~spl3_5 | ~spl3_17 | ~spl3_20),
% 0.14/0.42    inference(avatar_split_clause,[],[f128,f123,f107,f51,f130])).
% 0.14/0.42  fof(f51,plain,(
% 0.14/0.42    spl3_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.14/0.42  fof(f107,plain,(
% 0.14/0.42    spl3_17 <=> ! [X1,X2] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.14/0.42  fof(f123,plain,(
% 0.14/0.42    spl3_20 <=> k6_relat_1(sK1) = k8_relat_1(sK2,k6_relat_1(sK1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.14/0.42  fof(f128,plain,(
% 0.14/0.42    sK1 = k9_relat_1(k6_relat_1(sK2),sK1) | (~spl3_5 | ~spl3_17 | ~spl3_20)),
% 0.14/0.42    inference(forward_demodulation,[],[f127,f52])).
% 0.14/0.42  fof(f52,plain,(
% 0.14/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_5),
% 0.14/0.42    inference(avatar_component_clause,[],[f51])).
% 0.14/0.42  fof(f127,plain,(
% 0.14/0.42    k9_relat_1(k6_relat_1(sK2),sK1) = k2_relat_1(k6_relat_1(sK1)) | (~spl3_17 | ~spl3_20)),
% 0.14/0.42    inference(superposition,[],[f108,f125])).
% 0.14/0.42  fof(f125,plain,(
% 0.14/0.42    k6_relat_1(sK1) = k8_relat_1(sK2,k6_relat_1(sK1)) | ~spl3_20),
% 0.14/0.42    inference(avatar_component_clause,[],[f123])).
% 0.14/0.42  fof(f108,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) ) | ~spl3_17),
% 0.14/0.42    inference(avatar_component_clause,[],[f107])).
% 0.14/0.42  fof(f126,plain,(
% 0.14/0.42    spl3_20 | ~spl3_2 | ~spl3_19),
% 0.14/0.42    inference(avatar_split_clause,[],[f121,f118,f37,f123])).
% 0.14/0.42  fof(f37,plain,(
% 0.14/0.42    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.14/0.42  fof(f118,plain,(
% 0.14/0.42    spl3_19 <=> ! [X1,X2] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k8_relat_1(X2,k6_relat_1(X1)))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.14/0.42  fof(f121,plain,(
% 0.14/0.42    k6_relat_1(sK1) = k8_relat_1(sK2,k6_relat_1(sK1)) | (~spl3_2 | ~spl3_19)),
% 0.14/0.42    inference(resolution,[],[f119,f39])).
% 0.14/0.42  fof(f39,plain,(
% 0.14/0.42    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.14/0.42    inference(avatar_component_clause,[],[f37])).
% 0.14/0.42  fof(f119,plain,(
% 0.14/0.42    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k8_relat_1(X2,k6_relat_1(X1))) ) | ~spl3_19),
% 0.14/0.42    inference(avatar_component_clause,[],[f118])).
% 0.14/0.42  fof(f120,plain,(
% 0.14/0.42    spl3_19 | ~spl3_4 | ~spl3_5 | ~spl3_10),
% 0.14/0.42    inference(avatar_split_clause,[],[f116,f71,f51,f47,f118])).
% 0.14/0.42  fof(f71,plain,(
% 0.14/0.42    spl3_10 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.14/0.42  fof(f116,plain,(
% 0.14/0.42    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k8_relat_1(X2,k6_relat_1(X1))) ) | (~spl3_4 | ~spl3_5 | ~spl3_10)),
% 0.14/0.42    inference(forward_demodulation,[],[f111,f52])).
% 0.14/0.42  fof(f111,plain,(
% 0.14/0.42    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k8_relat_1(X2,k6_relat_1(X1))) ) | (~spl3_4 | ~spl3_10)),
% 0.14/0.42    inference(resolution,[],[f72,f48])).
% 0.14/0.42  fof(f72,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) ) | ~spl3_10),
% 0.14/0.42    inference(avatar_component_clause,[],[f71])).
% 0.14/0.42  fof(f109,plain,(
% 0.14/0.42    spl3_17 | ~spl3_4 | ~spl3_9 | ~spl3_15),
% 0.14/0.42    inference(avatar_split_clause,[],[f105,f96,f67,f47,f107])).
% 0.14/0.42  fof(f67,plain,(
% 0.14/0.42    spl3_9 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.14/0.42  fof(f96,plain,(
% 0.14/0.42    spl3_15 <=> ! [X1,X2] : k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.14/0.42  fof(f105,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) ) | (~spl3_4 | ~spl3_9 | ~spl3_15)),
% 0.14/0.42    inference(forward_demodulation,[],[f100,f97])).
% 0.14/0.42  fof(f97,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)) ) | ~spl3_15),
% 0.14/0.42    inference(avatar_component_clause,[],[f96])).
% 0.14/0.42  fof(f100,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) ) | (~spl3_4 | ~spl3_9)),
% 0.14/0.42    inference(resolution,[],[f68,f48])).
% 0.14/0.42  fof(f68,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_9),
% 0.14/0.42    inference(avatar_component_clause,[],[f67])).
% 0.14/0.42  fof(f98,plain,(
% 0.14/0.42    spl3_15 | ~spl3_4 | ~spl3_8 | ~spl3_13),
% 0.14/0.42    inference(avatar_split_clause,[],[f94,f85,f63,f47,f96])).
% 0.14/0.42  fof(f63,plain,(
% 0.14/0.42    spl3_8 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.14/0.42  fof(f85,plain,(
% 0.14/0.42    spl3_13 <=> ! [X1,X2] : k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.14/0.42  fof(f94,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)) ) | (~spl3_4 | ~spl3_8 | ~spl3_13)),
% 0.14/0.42    inference(forward_demodulation,[],[f89,f86])).
% 0.14/0.42  fof(f86,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ) | ~spl3_13),
% 0.14/0.42    inference(avatar_component_clause,[],[f85])).
% 0.14/0.42  fof(f89,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2)) ) | (~spl3_4 | ~spl3_8)),
% 0.14/0.42    inference(resolution,[],[f64,f48])).
% 0.14/0.42  fof(f64,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_8),
% 0.14/0.42    inference(avatar_component_clause,[],[f63])).
% 0.14/0.42  fof(f93,plain,(
% 0.14/0.42    spl3_14 | ~spl3_3 | ~spl3_8),
% 0.14/0.42    inference(avatar_split_clause,[],[f88,f63,f42,f91])).
% 0.14/0.42  fof(f88,plain,(
% 0.14/0.42    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) ) | (~spl3_3 | ~spl3_8)),
% 0.14/0.42    inference(resolution,[],[f64,f44])).
% 0.14/0.42  fof(f87,plain,(
% 0.14/0.42    spl3_13 | ~spl3_4 | ~spl3_7),
% 0.14/0.42    inference(avatar_split_clause,[],[f79,f59,f47,f85])).
% 0.14/0.42  fof(f59,plain,(
% 0.14/0.42    spl3_7 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.14/0.42  fof(f79,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ) | (~spl3_4 | ~spl3_7)),
% 0.14/0.42    inference(resolution,[],[f60,f48])).
% 0.14/0.42  fof(f60,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl3_7),
% 0.14/0.42    inference(avatar_component_clause,[],[f59])).
% 0.14/0.42  fof(f77,plain,(
% 0.14/0.42    spl3_11),
% 0.14/0.42    inference(avatar_split_clause,[],[f30,f75])).
% 0.14/0.42  fof(f30,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f16])).
% 0.14/0.42  fof(f16,plain,(
% 0.14/0.42    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f5])).
% 0.14/0.42  fof(f5,axiom,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.14/0.42  fof(f73,plain,(
% 0.14/0.42    spl3_10),
% 0.14/0.42    inference(avatar_split_clause,[],[f29,f71])).
% 0.14/0.42  fof(f29,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f15])).
% 0.14/0.42  fof(f15,plain,(
% 0.14/0.42    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(flattening,[],[f14])).
% 0.14/0.42  fof(f14,plain,(
% 0.14/0.42    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f3])).
% 0.14/0.42  fof(f3,axiom,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.14/0.42  fof(f69,plain,(
% 0.14/0.42    spl3_9),
% 0.14/0.42    inference(avatar_split_clause,[],[f28,f67])).
% 0.14/0.42  fof(f28,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f13])).
% 0.14/0.42  fof(f13,plain,(
% 0.14/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f4])).
% 0.14/0.42  fof(f4,axiom,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.14/0.42  fof(f65,plain,(
% 0.14/0.42    spl3_8),
% 0.14/0.42    inference(avatar_split_clause,[],[f27,f63])).
% 0.14/0.42  fof(f27,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f12])).
% 0.14/0.42  fof(f12,plain,(
% 0.14/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f7])).
% 0.14/0.42  fof(f7,axiom,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.14/0.42  fof(f61,plain,(
% 0.14/0.42    spl3_7),
% 0.14/0.42    inference(avatar_split_clause,[],[f26,f59])).
% 0.14/0.42  fof(f26,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f11])).
% 0.14/0.42  fof(f11,plain,(
% 0.14/0.42    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f2])).
% 0.14/0.42  fof(f2,axiom,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.14/0.42  fof(f53,plain,(
% 0.14/0.42    spl3_5),
% 0.14/0.42    inference(avatar_split_clause,[],[f25,f51])).
% 0.14/0.42  fof(f25,plain,(
% 0.14/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.14/0.42    inference(cnf_transformation,[],[f6])).
% 0.14/0.42  fof(f6,axiom,(
% 0.14/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.14/0.42  fof(f49,plain,(
% 0.14/0.42    spl3_4),
% 0.14/0.42    inference(avatar_split_clause,[],[f23,f47])).
% 0.14/0.42  fof(f23,plain,(
% 0.14/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f1])).
% 0.14/0.42  fof(f1,axiom,(
% 0.14/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.14/0.42  fof(f45,plain,(
% 0.14/0.42    spl3_3),
% 0.14/0.42    inference(avatar_split_clause,[],[f20,f42])).
% 0.14/0.42  fof(f20,plain,(
% 0.14/0.42    v1_relat_1(sK0)),
% 0.14/0.42    inference(cnf_transformation,[],[f19])).
% 0.14/0.42  fof(f19,plain,(
% 0.14/0.42    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 0.14/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).
% 0.14/0.42  fof(f17,plain,(
% 0.14/0.42    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f18,plain,(
% 0.14/0.42    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f10,plain,(
% 0.14/0.42    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 0.14/0.42    inference(ennf_transformation,[],[f9])).
% 0.14/0.42  fof(f9,negated_conjecture,(
% 0.14/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.14/0.42    inference(negated_conjecture,[],[f8])).
% 0.14/0.42  fof(f8,conjecture,(
% 0.14/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 0.14/0.42  fof(f40,plain,(
% 0.14/0.42    spl3_2),
% 0.14/0.42    inference(avatar_split_clause,[],[f21,f37])).
% 0.14/0.42  fof(f21,plain,(
% 0.14/0.42    r1_tarski(sK1,sK2)),
% 0.14/0.42    inference(cnf_transformation,[],[f19])).
% 0.14/0.42  fof(f35,plain,(
% 0.14/0.42    ~spl3_1),
% 0.14/0.42    inference(avatar_split_clause,[],[f22,f32])).
% 0.14/0.42  fof(f22,plain,(
% 0.14/0.42    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 0.14/0.42    inference(cnf_transformation,[],[f19])).
% 0.14/0.42  % SZS output end Proof for theBenchmark
% 0.14/0.42  % (772)------------------------------
% 0.14/0.42  % (772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.42  % (772)Termination reason: Refutation
% 0.14/0.42  
% 0.14/0.42  % (772)Memory used [KB]: 10618
% 0.14/0.42  % (772)Time elapsed: 0.009 s
% 0.14/0.42  % (772)------------------------------
% 0.14/0.42  % (772)------------------------------
% 0.14/0.42  % (764)Success in time 0.067 s
%------------------------------------------------------------------------------
