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
% DateTime   : Thu Dec  3 12:49:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 169 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :    7
%              Number of atoms          :  291 ( 565 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (19006)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f1021,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f61,f65,f69,f73,f77,f81,f98,f119,f133,f186,f223,f289,f297,f1003,f1020])).

fof(f1020,plain,
    ( ~ spl4_3
    | ~ spl4_21
    | spl4_169 ),
    inference(avatar_contradiction_clause,[],[f1019])).

fof(f1019,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_21
    | spl4_169 ),
    inference(subsumption_resolution,[],[f1013,f46])).

fof(f46,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1013,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ spl4_21
    | spl4_169 ),
    inference(resolution,[],[f1002,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,sK2),X1)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK2,X1)
        | r1_tarski(k8_relat_1(X0,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1002,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK3)
    | spl4_169 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1000,plain,
    ( spl4_169
  <=> r1_tarski(k8_relat_1(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_169])])).

fof(f1003,plain,
    ( ~ spl4_169
    | spl4_1
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f998,f287,f49,f34,f1000])).

fof(f34,plain,
    ( spl4_1
  <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f49,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f287,plain,
    ( spl4_50
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f998,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f989,f51])).

fof(f51,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f989,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(k8_relat_1(sK0,sK2),sK3)
    | spl4_1
    | ~ spl4_50 ),
    inference(resolution,[],[f288,f36])).

fof(f36,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f288,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X1) )
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f287])).

fof(f297,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_48 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6
    | spl4_48 ),
    inference(subsumption_resolution,[],[f295,f56])).

fof(f56,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f295,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_6
    | spl4_48 ),
    inference(resolution,[],[f281,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f281,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl4_48 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl4_48
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f289,plain,
    ( ~ spl4_48
    | spl4_50
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f275,f220,f67,f287,f279])).

fof(f67,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f220,plain,
    ( spl4_38
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f275,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1))
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK0,sK2)) )
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(superposition,[],[f68,f222])).

fof(f222,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f220])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f223,plain,
    ( spl4_38
    | ~ spl4_5
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f212,f184,f54,f220])).

fof(f184,plain,
    ( spl4_30
  <=> ! [X0] :
        ( k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f212,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl4_5
    | ~ spl4_30 ),
    inference(resolution,[],[f185,f56])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0)) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f184])).

fof(f186,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f176,f75,f39,f184])).

fof(f39,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f75,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f176,plain,
    ( ! [X0] :
        ( k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(resolution,[],[f76,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
        | ~ v1_relat_1(X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f133,plain,
    ( spl4_21
    | ~ spl4_11
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f129,f117,f79,f131])).

fof(f79,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f117,plain,
    ( spl4_18
  <=> ! [X1] : sK2 = k2_xboole_0(k8_relat_1(X1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,X1)
        | r1_tarski(k8_relat_1(X0,sK2),X1) )
    | ~ spl4_11
    | ~ spl4_18 ),
    inference(superposition,[],[f80,f118])).

fof(f118,plain,
    ( ! [X1] : sK2 = k2_xboole_0(k8_relat_1(X1,sK2),sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f119,plain,
    ( spl4_18
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f110,f96,f54,f117])).

fof(f96,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( k2_xboole_0(k8_relat_1(X0,X1),X1) = X1
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f110,plain,
    ( ! [X1] : sK2 = k2_xboole_0(k8_relat_1(X1,sK2),sK2)
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(resolution,[],[f97,f56])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_xboole_0(k8_relat_1(X0,X1),X1) = X1 )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl4_14
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f84,f71,f63,f96])).

fof(f63,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f71,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(k8_relat_1(X0,X1),X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f72,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f81,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f77,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f73,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f69,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f65,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f61,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f57,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f52,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f39])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f34])).

fof(f26,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (19008)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (19012)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.44  % (19005)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.45  % (19011)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.45  % (19013)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.46  % (19012)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  % (19006)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.46  fof(f1021,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f61,f65,f69,f73,f77,f81,f98,f119,f133,f186,f223,f289,f297,f1003,f1020])).
% 0.22/0.46  fof(f1020,plain,(
% 0.22/0.46    ~spl4_3 | ~spl4_21 | spl4_169),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f1019])).
% 0.22/0.46  fof(f1019,plain,(
% 0.22/0.46    $false | (~spl4_3 | ~spl4_21 | spl4_169)),
% 0.22/0.46    inference(subsumption_resolution,[],[f1013,f46])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    r1_tarski(sK2,sK3) | ~spl4_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f44])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    spl4_3 <=> r1_tarski(sK2,sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.46  fof(f1013,plain,(
% 0.22/0.46    ~r1_tarski(sK2,sK3) | (~spl4_21 | spl4_169)),
% 0.22/0.46    inference(resolution,[],[f1002,f132])).
% 0.22/0.46  fof(f132,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,sK2),X1) | ~r1_tarski(sK2,X1)) ) | ~spl4_21),
% 0.22/0.46    inference(avatar_component_clause,[],[f131])).
% 0.22/0.46  fof(f131,plain,(
% 0.22/0.46    spl4_21 <=> ! [X1,X0] : (~r1_tarski(sK2,X1) | r1_tarski(k8_relat_1(X0,sK2),X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.46  fof(f1002,plain,(
% 0.22/0.46    ~r1_tarski(k8_relat_1(sK0,sK2),sK3) | spl4_169),
% 0.22/0.46    inference(avatar_component_clause,[],[f1000])).
% 0.22/0.46  fof(f1000,plain,(
% 0.22/0.46    spl4_169 <=> r1_tarski(k8_relat_1(sK0,sK2),sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_169])])).
% 0.22/0.46  fof(f1003,plain,(
% 0.22/0.46    ~spl4_169 | spl4_1 | ~spl4_4 | ~spl4_50),
% 0.22/0.46    inference(avatar_split_clause,[],[f998,f287,f49,f34,f1000])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    spl4_1 <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    spl4_4 <=> v1_relat_1(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.46  fof(f287,plain,(
% 0.22/0.46    spl4_50 <=> ! [X1] : (r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK0,sK2),X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.22/0.46  fof(f998,plain,(
% 0.22/0.46    ~r1_tarski(k8_relat_1(sK0,sK2),sK3) | (spl4_1 | ~spl4_4 | ~spl4_50)),
% 0.22/0.46    inference(subsumption_resolution,[],[f989,f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    v1_relat_1(sK3) | ~spl4_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f49])).
% 0.22/0.46  fof(f989,plain,(
% 0.22/0.46    ~v1_relat_1(sK3) | ~r1_tarski(k8_relat_1(sK0,sK2),sK3) | (spl4_1 | ~spl4_50)),
% 0.22/0.46    inference(resolution,[],[f288,f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | spl4_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f34])).
% 0.22/0.46  fof(f288,plain,(
% 0.22/0.46    ( ! [X1] : (r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK0,sK2),X1)) ) | ~spl4_50),
% 0.22/0.46    inference(avatar_component_clause,[],[f287])).
% 0.22/0.46  fof(f297,plain,(
% 0.22/0.46    ~spl4_5 | ~spl4_6 | spl4_48),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f296])).
% 0.22/0.46  fof(f296,plain,(
% 0.22/0.46    $false | (~spl4_5 | ~spl4_6 | spl4_48)),
% 0.22/0.46    inference(subsumption_resolution,[],[f295,f56])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    v1_relat_1(sK2) | ~spl4_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    spl4_5 <=> v1_relat_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.46  fof(f295,plain,(
% 0.22/0.46    ~v1_relat_1(sK2) | (~spl4_6 | spl4_48)),
% 0.22/0.46    inference(resolution,[],[f281,f60])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl4_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f59])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    spl4_6 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.46  fof(f281,plain,(
% 0.22/0.46    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl4_48),
% 0.22/0.46    inference(avatar_component_clause,[],[f279])).
% 0.22/0.46  fof(f279,plain,(
% 0.22/0.46    spl4_48 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.22/0.46  fof(f289,plain,(
% 0.22/0.46    ~spl4_48 | spl4_50 | ~spl4_8 | ~spl4_38),
% 0.22/0.46    inference(avatar_split_clause,[],[f275,f220,f67,f287,f279])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    spl4_8 <=> ! [X1,X0,X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.46  fof(f220,plain,(
% 0.22/0.46    spl4_38 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.46  fof(f275,plain,(
% 0.22/0.46    ( ! [X1] : (r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1)) | ~r1_tarski(k8_relat_1(sK0,sK2),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK0,sK2))) ) | (~spl4_8 | ~spl4_38)),
% 0.22/0.46    inference(superposition,[],[f68,f222])).
% 0.22/0.46  fof(f222,plain,(
% 0.22/0.46    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | ~spl4_38),
% 0.22/0.46    inference(avatar_component_clause,[],[f220])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl4_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f67])).
% 0.22/0.46  fof(f223,plain,(
% 0.22/0.46    spl4_38 | ~spl4_5 | ~spl4_30),
% 0.22/0.46    inference(avatar_split_clause,[],[f212,f184,f54,f220])).
% 0.22/0.46  fof(f184,plain,(
% 0.22/0.46    spl4_30 <=> ! [X0] : (k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0)) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.46  fof(f212,plain,(
% 0.22/0.46    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl4_5 | ~spl4_30)),
% 0.22/0.46    inference(resolution,[],[f185,f56])).
% 0.22/0.46  fof(f185,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0))) ) | ~spl4_30),
% 0.22/0.46    inference(avatar_component_clause,[],[f184])).
% 0.22/0.46  fof(f186,plain,(
% 0.22/0.46    spl4_30 | ~spl4_2 | ~spl4_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f176,f75,f39,f184])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    spl4_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    spl4_10 <=> ! [X1,X0,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.46  fof(f176,plain,(
% 0.22/0.46    ( ! [X0] : (k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0)) | ~v1_relat_1(X0)) ) | (~spl4_2 | ~spl4_10)),
% 0.22/0.46    inference(resolution,[],[f76,f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    r1_tarski(sK0,sK1) | ~spl4_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f39])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) ) | ~spl4_10),
% 0.22/0.46    inference(avatar_component_clause,[],[f75])).
% 0.22/0.46  fof(f133,plain,(
% 0.22/0.46    spl4_21 | ~spl4_11 | ~spl4_18),
% 0.22/0.46    inference(avatar_split_clause,[],[f129,f117,f79,f131])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    spl4_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.46  fof(f117,plain,(
% 0.22/0.46    spl4_18 <=> ! [X1] : sK2 = k2_xboole_0(k8_relat_1(X1,sK2),sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.46  fof(f129,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(sK2,X1) | r1_tarski(k8_relat_1(X0,sK2),X1)) ) | (~spl4_11 | ~spl4_18)),
% 0.22/0.46    inference(superposition,[],[f80,f118])).
% 0.22/0.46  fof(f118,plain,(
% 0.22/0.46    ( ! [X1] : (sK2 = k2_xboole_0(k8_relat_1(X1,sK2),sK2)) ) | ~spl4_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f117])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl4_11),
% 0.22/0.46    inference(avatar_component_clause,[],[f79])).
% 0.22/0.46  fof(f119,plain,(
% 0.22/0.46    spl4_18 | ~spl4_5 | ~spl4_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f110,f96,f54,f117])).
% 0.22/0.46  fof(f96,plain,(
% 0.22/0.46    spl4_14 <=> ! [X1,X0] : (k2_xboole_0(k8_relat_1(X0,X1),X1) = X1 | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.46  fof(f110,plain,(
% 0.22/0.46    ( ! [X1] : (sK2 = k2_xboole_0(k8_relat_1(X1,sK2),sK2)) ) | (~spl4_5 | ~spl4_14)),
% 0.22/0.46    inference(resolution,[],[f97,f56])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_xboole_0(k8_relat_1(X0,X1),X1) = X1) ) | ~spl4_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f96])).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    spl4_14 | ~spl4_7 | ~spl4_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f84,f71,f63,f96])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    spl4_7 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    spl4_9 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(k8_relat_1(X0,X1),X1) = X1 | ~v1_relat_1(X1)) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.46    inference(resolution,[],[f72,f64])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) ) | ~spl4_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f63])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f71])).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    spl4_11),
% 0.22/0.46    inference(avatar_split_clause,[],[f32,f79])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    spl4_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f31,f75])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(flattening,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    spl4_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f30,f71])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    spl4_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f29,f67])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(flattening,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    spl4_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f28,f63])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    spl4_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f27,f59])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    spl4_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f22,f54])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    v1_relat_1(sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.46    inference(flattening,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.22/0.46    inference(negated_conjecture,[],[f7])).
% 0.22/0.46  fof(f7,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    spl4_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f23,f49])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    v1_relat_1(sK3)),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    spl4_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f24,f44])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    r1_tarski(sK2,sK3)),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    spl4_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f25,f39])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    r1_tarski(sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ~spl4_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f26,f34])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (19012)------------------------------
% 0.22/0.46  % (19012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (19012)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (19012)Memory used [KB]: 6780
% 0.22/0.46  % (19012)Time elapsed: 0.040 s
% 0.22/0.46  % (19012)------------------------------
% 0.22/0.46  % (19012)------------------------------
% 0.22/0.46  % (19001)Success in time 0.098 s
%------------------------------------------------------------------------------
