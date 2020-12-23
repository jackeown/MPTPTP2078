%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 158 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  260 ( 468 expanded)
%              Number of equality atoms :   64 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f53,f57,f61,f65,f69,f73,f80,f95,f111,f130,f138,f157,f197,f201])).

fof(f201,plain,
    ( spl3_1
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl3_1
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f199,f33])).

fof(f33,plain,
    ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f199,plain,
    ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0))
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f198,f110])).

fof(f110,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_17
  <=> ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f198,plain,
    ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK0))))
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(superposition,[],[f196,f129])).

fof(f129,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0))))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_20
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f196,plain,
    ( ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl3_32
  <=> ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f197,plain,
    ( spl3_32
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f193,f155,f78,f51,f195])).

fof(f51,plain,
    ( spl3_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f78,plain,
    ( spl3_11
  <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f155,plain,
    ( spl3_25
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(sK1,X1),sK2) = k5_relat_1(sK1,k5_relat_1(X1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f193,plain,
    ( ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f182,f79])).

fof(f79,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f182,plain,
    ( ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),sK2))
    | ~ spl3_5
    | ~ spl3_25 ),
    inference(resolution,[],[f156,f52])).

fof(f52,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f156,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(sK1,X1),sK2) = k5_relat_1(sK1,k5_relat_1(X1,sK2)) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl3_25
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f148,f136,f46,f155])).

fof(f46,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f136,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( k5_relat_1(k5_relat_1(X0,X1),sK2) = k5_relat_1(X0,k5_relat_1(X1,sK2))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f148,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(sK1,X1),sK2) = k5_relat_1(sK1,k5_relat_1(X1,sK2)) )
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(resolution,[],[f137,f48])).

fof(f48,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(X0,X1),sK2) = k5_relat_1(X0,k5_relat_1(X1,sK2)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl3_21
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f132,f55,f41,f136])).

fof(f41,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f55,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(k5_relat_1(X0,X1),sK2) = k5_relat_1(X0,k5_relat_1(X1,sK2))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f56,f43])).

fof(f43,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f130,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f125,f71,f46,f36,f127])).

fof(f36,plain,
    ( spl3_2
  <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f125,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0))))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f124,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0))))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f111,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f107,f93,f67,f41,f109])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f93,plain,
    ( spl3_14
  <=> ! [X0] : k3_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f107,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f104,f94])).

fof(f94,plain,
    ( ! [X0] : k3_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f104,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(k1_relat_1(sK2),X0))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f68,f43])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f95,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f89,f63,f41,f93])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f89,plain,
    ( ! [X0] : k3_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f80,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f59,f41,f78])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f73,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f69,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f61,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f57,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))
    & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
            & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0))
          & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0))
        & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0)))
        & v1_relat_1(X2) )
   => ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))
      & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
             => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f31])).

fof(f23,plain,(
    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (24846)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (24849)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.44  % (24845)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (24846)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f202,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f53,f57,f61,f65,f69,f73,f80,f95,f111,f130,f138,f157,f197,f201])).
% 0.21/0.44  fof(f201,plain,(
% 0.21/0.44    spl3_1 | ~spl3_17 | ~spl3_20 | ~spl3_32),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f200])).
% 0.21/0.44  fof(f200,plain,(
% 0.21/0.44    $false | (spl3_1 | ~spl3_17 | ~spl3_20 | ~spl3_32)),
% 0.21/0.44    inference(subsumption_resolution,[],[f199,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl3_1 <=> k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f199,plain,(
% 0.21/0.44    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0)) | (~spl3_17 | ~spl3_20 | ~spl3_32)),
% 0.21/0.44    inference(forward_demodulation,[],[f198,f110])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) ) | ~spl3_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f109])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl3_17 <=> ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.44  fof(f198,plain,(
% 0.21/0.44    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK0)))) | (~spl3_20 | ~spl3_32)),
% 0.21/0.44    inference(superposition,[],[f196,f129])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0)))) | ~spl3_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f127])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    spl3_20 <=> sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.44  fof(f196,plain,(
% 0.21/0.44    ( ! [X0] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0))) ) | ~spl3_32),
% 0.21/0.44    inference(avatar_component_clause,[],[f195])).
% 0.21/0.44  fof(f195,plain,(
% 0.21/0.44    spl3_32 <=> ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.44  fof(f197,plain,(
% 0.21/0.44    spl3_32 | ~spl3_5 | ~spl3_11 | ~spl3_25),
% 0.21/0.44    inference(avatar_split_clause,[],[f193,f155,f78,f51,f195])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl3_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    spl3_11 <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    spl3_25 <=> ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X1),sK2) = k5_relat_1(sK1,k5_relat_1(X1,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.44  fof(f193,plain,(
% 0.21/0.44    ( ! [X0] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0))) ) | (~spl3_5 | ~spl3_11 | ~spl3_25)),
% 0.21/0.44    inference(forward_demodulation,[],[f182,f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f78])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    ( ! [X0] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),sK2))) ) | (~spl3_5 | ~spl3_25)),
% 0.21/0.44    inference(resolution,[],[f156,f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f51])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X1),sK2) = k5_relat_1(sK1,k5_relat_1(X1,sK2))) ) | ~spl3_25),
% 0.21/0.44    inference(avatar_component_clause,[],[f155])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    spl3_25 | ~spl3_4 | ~spl3_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f148,f136,f46,f155])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_4 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    spl3_21 <=> ! [X1,X0] : (k5_relat_1(k5_relat_1(X0,X1),sK2) = k5_relat_1(X0,k5_relat_1(X1,sK2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X1),sK2) = k5_relat_1(sK1,k5_relat_1(X1,sK2))) ) | (~spl3_4 | ~spl3_21)),
% 0.21/0.44    inference(resolution,[],[f137,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    v1_relat_1(sK1) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f46])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),sK2) = k5_relat_1(X0,k5_relat_1(X1,sK2))) ) | ~spl3_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f136])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    spl3_21 | ~spl3_3 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f132,f55,f41,f136])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl3_6 <=> ! [X1,X0,X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),sK2) = k5_relat_1(X0,k5_relat_1(X1,sK2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | (~spl3_3 | ~spl3_6)),
% 0.21/0.44    inference(resolution,[],[f56,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f41])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f55])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    spl3_20 | ~spl3_2 | ~spl3_4 | ~spl3_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f125,f71,f46,f36,f127])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl3_2 <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl3_10 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0)))) | (~spl3_2 | ~spl3_4 | ~spl3_10)),
% 0.21/0.44    inference(subsumption_resolution,[],[f124,f48])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0)))) | ~v1_relat_1(sK1) | (~spl3_2 | ~spl3_10)),
% 0.21/0.44    inference(resolution,[],[f72,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f36])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) ) | ~spl3_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f71])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    spl3_17 | ~spl3_3 | ~spl3_9 | ~spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f107,f93,f67,f41,f109])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl3_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl3_14 <=> ! [X0] : k3_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) ) | (~spl3_3 | ~spl3_9 | ~spl3_14)),
% 0.21/0.44    inference(forward_demodulation,[],[f104,f94])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f93])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(k1_relat_1(sK2),X0))) ) | (~spl3_3 | ~spl3_9)),
% 0.21/0.44    inference(resolution,[],[f68,f43])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) ) | ~spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl3_14 | ~spl3_3 | ~spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f89,f63,f41,f93])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_3 | ~spl3_8)),
% 0.21/0.44    inference(resolution,[],[f64,f43])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) ) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f63])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    spl3_11 | ~spl3_3 | ~spl3_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f74,f59,f41,f78])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl3_7 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | (~spl3_3 | ~spl3_7)),
% 0.21/0.44    inference(resolution,[],[f60,f43])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f59])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    spl3_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f29,f71])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f67])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl3_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f59])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f55])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f51])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f46])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    (k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X2] : (k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0))) & v1_relat_1(X2)) => (k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f41])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f36])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f31])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (24846)------------------------------
% 0.21/0.44  % (24846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (24846)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (24846)Memory used [KB]: 10618
% 0.21/0.44  % (24846)Time elapsed: 0.008 s
% 0.21/0.44  % (24846)------------------------------
% 0.21/0.44  % (24846)------------------------------
% 0.21/0.45  % (24840)Success in time 0.079 s
%------------------------------------------------------------------------------
