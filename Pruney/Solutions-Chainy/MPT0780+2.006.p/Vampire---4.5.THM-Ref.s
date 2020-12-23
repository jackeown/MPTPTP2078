%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:57 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 244 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  251 ( 459 expanded)
%              Number of equality atoms :   55 ( 139 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f224,f372,f552,f581,f601,f608,f654,f1235])).

fof(f1235,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f1234,f651,f574,f75,f220])).

fof(f220,plain,
    ( spl4_14
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f75,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f574,plain,
    ( spl4_36
  <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f651,plain,
    ( spl4_42
  <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1234,plain,
    ( k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_3
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1233,f576])).

fof(f576,plain,
    ( k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f574])).

fof(f1233,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_3
    | ~ spl4_42 ),
    inference(superposition,[],[f90,f653])).

fof(f653,plain,
    ( k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f651])).

fof(f90,plain,
    ( ! [X2,X1] : k2_wellord1(k2_wellord1(sK2,X1),X2) = k8_relat_1(X2,k7_relat_1(k2_wellord1(sK2,X1),X2))
    | ~ spl4_3 ),
    inference(resolution,[],[f43,f79])).

fof(f79,plain,
    ( ! [X0] : v1_relat_1(k2_wellord1(sK2,X0))
    | ~ spl4_3 ),
    inference(resolution,[],[f42,f77])).

fof(f77,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(f654,plain,
    ( spl4_42
    | ~ spl4_37
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f646,f598,f578,f651])).

fof(f578,plain,
    ( spl4_37
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f598,plain,
    ( spl4_39
  <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f646,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_39 ),
    inference(resolution,[],[f600,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f600,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f598])).

fof(f608,plain,
    ( ~ spl4_3
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | ~ spl4_3
    | spl4_37 ),
    inference(resolution,[],[f580,f79])).

fof(f580,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f578])).

fof(f601,plain,
    ( spl4_39
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f590,f369,f75,f598])).

fof(f369,plain,
    ( spl4_24
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f590,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f477,f371])).

fof(f371,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f369])).

fof(f477,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,X4)),X5)
        | r1_tarski(k1_relat_1(k2_wellord1(sK2,X4)),X5) )
    | ~ spl4_3 ),
    inference(superposition,[],[f63,f178])).

fof(f178,plain,
    ( ! [X0] : k3_relat_1(k2_wellord1(sK2,X0)) = k3_tarski(k4_enumset1(k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k2_relat_1(k2_wellord1(sK2,X0))))
    | ~ spl4_3 ),
    inference(resolution,[],[f61,f79])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

% (7098)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f581,plain,
    ( spl4_36
    | ~ spl4_37
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f569,f549,f578,f574])).

fof(f549,plain,
    ( spl4_33
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f569,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_33 ),
    inference(resolution,[],[f551,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f551,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f549])).

fof(f552,plain,
    ( spl4_33
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f541,f369,f75,f549])).

fof(f541,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f474,f371])).

fof(f474,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1)
        | r1_tarski(k2_relat_1(k2_wellord1(sK2,X0)),X1) )
    | ~ spl4_3 ),
    inference(superposition,[],[f175,f178])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f59,f59])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f372,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f349,f75,f70,f369])).

fof(f70,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f349,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f315,f72])).

fof(f72,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f315,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X2)),X3) )
    | ~ spl4_3 ),
    inference(resolution,[],[f313,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f313,plain,
    ( ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f249,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f249,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k3_relat_1(k2_wellord1(sK2,X0)),X1),X0)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f117,f77])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(k3_relat_1(k2_wellord1(X0,X1)),X2),X1)
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) ) ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(f224,plain,
    ( ~ spl4_14
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f216,f75,f65,f220])).

fof(f65,plain,
    ( spl4_1
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f216,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f67,f158])).

fof(f158,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f50,f77])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f67,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f78,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f73,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (7046)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (7054)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (7038)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.58  % (7054)Refutation not found, incomplete strategy% (7054)------------------------------
% 0.22/0.58  % (7054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (7054)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (7054)Memory used [KB]: 10746
% 0.22/0.58  % (7054)Time elapsed: 0.154 s
% 0.22/0.58  % (7054)------------------------------
% 0.22/0.58  % (7054)------------------------------
% 0.22/0.58  % (7032)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.58  % (7057)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.59  % (7033)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.59  % (7037)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.59  % (7055)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (7041)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.59  % (7036)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.59  % (7034)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.59  % (7035)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.59  % (7047)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.60  % (7049)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.60  % (7049)Refutation not found, incomplete strategy% (7049)------------------------------
% 0.22/0.60  % (7049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (7049)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (7049)Memory used [KB]: 10618
% 0.22/0.60  % (7049)Time elapsed: 0.168 s
% 0.22/0.60  % (7049)------------------------------
% 0.22/0.60  % (7049)------------------------------
% 0.22/0.60  % (7061)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.60  % (7059)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.59/0.60  % (7060)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.60  % (7056)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.60  % (7045)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.59/0.60  % (7050)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.60  % (7039)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.59/0.61  % (7053)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.61  % (7058)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.61  % (7052)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.61  % (7051)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.59/0.61  % (7044)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.61  % (7043)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.61  % (7042)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.62  % (7040)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.97/0.62  % (7048)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.22/0.68  % (7048)Refutation found. Thanks to Tanya!
% 2.22/0.68  % SZS status Theorem for theBenchmark
% 2.22/0.70  % SZS output start Proof for theBenchmark
% 2.22/0.70  fof(f1236,plain,(
% 2.22/0.70    $false),
% 2.22/0.70    inference(avatar_sat_refutation,[],[f68,f73,f78,f224,f372,f552,f581,f601,f608,f654,f1235])).
% 2.22/0.70  fof(f1235,plain,(
% 2.22/0.70    spl4_14 | ~spl4_3 | ~spl4_36 | ~spl4_42),
% 2.22/0.70    inference(avatar_split_clause,[],[f1234,f651,f574,f75,f220])).
% 2.22/0.70  fof(f220,plain,(
% 2.22/0.70    spl4_14 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.22/0.70  fof(f75,plain,(
% 2.22/0.70    spl4_3 <=> v1_relat_1(sK2)),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.22/0.70  fof(f574,plain,(
% 2.22/0.70    spl4_36 <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.22/0.70  fof(f651,plain,(
% 2.22/0.70    spl4_42 <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 2.22/0.70  fof(f1234,plain,(
% 2.22/0.70    k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) | (~spl4_3 | ~spl4_36 | ~spl4_42)),
% 2.22/0.70    inference(forward_demodulation,[],[f1233,f576])).
% 2.22/0.70  fof(f576,plain,(
% 2.22/0.70    k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~spl4_36),
% 2.22/0.70    inference(avatar_component_clause,[],[f574])).
% 2.22/0.70  fof(f1233,plain,(
% 2.22/0.70    k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | (~spl4_3 | ~spl4_42)),
% 2.22/0.70    inference(superposition,[],[f90,f653])).
% 2.22/0.70  fof(f653,plain,(
% 2.22/0.70    k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~spl4_42),
% 2.22/0.70    inference(avatar_component_clause,[],[f651])).
% 2.22/0.70  fof(f90,plain,(
% 2.22/0.70    ( ! [X2,X1] : (k2_wellord1(k2_wellord1(sK2,X1),X2) = k8_relat_1(X2,k7_relat_1(k2_wellord1(sK2,X1),X2))) ) | ~spl4_3),
% 2.22/0.70    inference(resolution,[],[f43,f79])).
% 2.22/0.70  fof(f79,plain,(
% 2.22/0.70    ( ! [X0] : (v1_relat_1(k2_wellord1(sK2,X0))) ) | ~spl4_3),
% 2.22/0.70    inference(resolution,[],[f42,f77])).
% 2.22/0.70  fof(f77,plain,(
% 2.22/0.70    v1_relat_1(sK2) | ~spl4_3),
% 2.22/0.70    inference(avatar_component_clause,[],[f75])).
% 2.22/0.70  fof(f42,plain,(
% 2.22/0.70    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1))) )),
% 2.22/0.70    inference(cnf_transformation,[],[f22])).
% 2.22/0.70  fof(f22,plain,(
% 2.22/0.70    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 2.22/0.70    inference(ennf_transformation,[],[f13])).
% 2.22/0.70  fof(f13,axiom,(
% 2.22/0.70    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 2.22/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 2.22/0.70  fof(f43,plain,(
% 2.22/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 2.22/0.70    inference(cnf_transformation,[],[f23])).
% 2.22/0.70  fof(f23,plain,(
% 2.22/0.70    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.22/0.70    inference(ennf_transformation,[],[f14])).
% 2.22/0.70  fof(f14,axiom,(
% 2.22/0.70    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 2.22/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).
% 2.22/0.70  fof(f654,plain,(
% 2.22/0.70    spl4_42 | ~spl4_37 | ~spl4_39),
% 2.22/0.70    inference(avatar_split_clause,[],[f646,f598,f578,f651])).
% 2.22/0.70  fof(f578,plain,(
% 2.22/0.70    spl4_37 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.22/0.70  fof(f598,plain,(
% 2.22/0.70    spl4_39 <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.22/0.70  fof(f646,plain,(
% 2.22/0.70    ~v1_relat_1(k2_wellord1(sK2,sK0)) | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~spl4_39),
% 2.22/0.70    inference(resolution,[],[f600,f45])).
% 2.22/0.70  fof(f45,plain,(
% 2.22/0.70    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 2.22/0.70    inference(cnf_transformation,[],[f27])).
% 2.22/0.70  fof(f27,plain,(
% 2.22/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.22/0.70    inference(flattening,[],[f26])).
% 2.22/0.70  fof(f26,plain,(
% 2.22/0.70    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.22/0.70    inference(ennf_transformation,[],[f12])).
% 2.22/0.70  fof(f12,axiom,(
% 2.22/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.22/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 2.22/0.71  fof(f600,plain,(
% 2.22/0.71    r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_39),
% 2.22/0.71    inference(avatar_component_clause,[],[f598])).
% 2.22/0.71  fof(f608,plain,(
% 2.22/0.71    ~spl4_3 | spl4_37),
% 2.22/0.71    inference(avatar_contradiction_clause,[],[f607])).
% 2.22/0.71  fof(f607,plain,(
% 2.22/0.71    $false | (~spl4_3 | spl4_37)),
% 2.22/0.71    inference(resolution,[],[f580,f79])).
% 2.22/0.71  fof(f580,plain,(
% 2.22/0.71    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_37),
% 2.22/0.71    inference(avatar_component_clause,[],[f578])).
% 2.22/0.71  fof(f601,plain,(
% 2.22/0.71    spl4_39 | ~spl4_3 | ~spl4_24),
% 2.22/0.71    inference(avatar_split_clause,[],[f590,f369,f75,f598])).
% 2.22/0.71  fof(f369,plain,(
% 2.22/0.71    spl4_24 <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 2.22/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.22/0.71  fof(f590,plain,(
% 2.22/0.71    r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_3 | ~spl4_24)),
% 2.22/0.71    inference(resolution,[],[f477,f371])).
% 2.22/0.71  fof(f371,plain,(
% 2.22/0.71    r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_24),
% 2.22/0.71    inference(avatar_component_clause,[],[f369])).
% 2.22/0.71  fof(f477,plain,(
% 2.22/0.71    ( ! [X4,X5] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,X4)),X5) | r1_tarski(k1_relat_1(k2_wellord1(sK2,X4)),X5)) ) | ~spl4_3),
% 2.22/0.71    inference(superposition,[],[f63,f178])).
% 2.22/0.71  fof(f178,plain,(
% 2.22/0.71    ( ! [X0] : (k3_relat_1(k2_wellord1(sK2,X0)) = k3_tarski(k4_enumset1(k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k2_relat_1(k2_wellord1(sK2,X0))))) ) | ~spl4_3),
% 2.22/0.71    inference(resolution,[],[f61,f79])).
% 2.22/0.71  fof(f61,plain,(
% 2.22/0.71    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.22/0.71    inference(definition_unfolding,[],[f38,f60])).
% 2.22/0.71  fof(f60,plain,(
% 2.22/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 2.22/0.71    inference(definition_unfolding,[],[f40,f59])).
% 2.22/0.71  fof(f59,plain,(
% 2.22/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 2.22/0.71    inference(definition_unfolding,[],[f41,f58])).
% 2.22/0.71  fof(f58,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 2.22/0.71    inference(definition_unfolding,[],[f49,f57])).
% 2.22/0.71  fof(f57,plain,(
% 2.22/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 2.22/0.71    inference(definition_unfolding,[],[f55,f56])).
% 2.22/0.71  fof(f56,plain,(
% 2.22/0.71    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f8])).
% 2.22/0.71  fof(f8,axiom,(
% 2.22/0.71    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.22/0.71  fof(f55,plain,(
% 2.22/0.71    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f7])).
% 2.22/0.71  % (7098)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.22/0.71  fof(f7,axiom,(
% 2.22/0.71    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.22/0.71  fof(f49,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f6])).
% 2.22/0.71  fof(f6,axiom,(
% 2.22/0.71    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.22/0.71  fof(f41,plain,(
% 2.22/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f5])).
% 2.22/0.71  fof(f5,axiom,(
% 2.22/0.71    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.22/0.71  fof(f40,plain,(
% 2.22/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.22/0.71    inference(cnf_transformation,[],[f9])).
% 2.22/0.71  fof(f9,axiom,(
% 2.22/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.22/0.71  fof(f38,plain,(
% 2.22/0.71    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 2.22/0.71    inference(cnf_transformation,[],[f21])).
% 2.22/0.71  fof(f21,plain,(
% 2.22/0.71    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.22/0.71    inference(ennf_transformation,[],[f10])).
% 2.22/0.71  fof(f10,axiom,(
% 2.22/0.71    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 2.22/0.71  fof(f63,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 2.22/0.71    inference(definition_unfolding,[],[f53,f60])).
% 2.22/0.71  fof(f53,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f32])).
% 2.22/0.71  fof(f32,plain,(
% 2.22/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.22/0.71    inference(ennf_transformation,[],[f2])).
% 2.22/0.71  fof(f2,axiom,(
% 2.22/0.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.22/0.71  fof(f581,plain,(
% 2.22/0.71    spl4_36 | ~spl4_37 | ~spl4_33),
% 2.22/0.71    inference(avatar_split_clause,[],[f569,f549,f578,f574])).
% 2.22/0.71  fof(f549,plain,(
% 2.22/0.71    spl4_33 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 2.22/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.22/0.71  fof(f569,plain,(
% 2.22/0.71    ~v1_relat_1(k2_wellord1(sK2,sK0)) | k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~spl4_33),
% 2.22/0.71    inference(resolution,[],[f551,f44])).
% 2.22/0.71  fof(f44,plain,(
% 2.22/0.71    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 2.22/0.71    inference(cnf_transformation,[],[f25])).
% 2.22/0.71  fof(f25,plain,(
% 2.22/0.71    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.22/0.71    inference(flattening,[],[f24])).
% 2.22/0.71  fof(f24,plain,(
% 2.22/0.71    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.22/0.71    inference(ennf_transformation,[],[f11])).
% 2.22/0.71  fof(f11,axiom,(
% 2.22/0.71    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 2.22/0.71  fof(f551,plain,(
% 2.22/0.71    r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_33),
% 2.22/0.71    inference(avatar_component_clause,[],[f549])).
% 2.22/0.71  fof(f552,plain,(
% 2.22/0.71    spl4_33 | ~spl4_3 | ~spl4_24),
% 2.22/0.71    inference(avatar_split_clause,[],[f541,f369,f75,f549])).
% 2.22/0.71  fof(f541,plain,(
% 2.22/0.71    r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_3 | ~spl4_24)),
% 2.22/0.71    inference(resolution,[],[f474,f371])).
% 2.22/0.71  fof(f474,plain,(
% 2.22/0.71    ( ! [X0,X1] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1) | r1_tarski(k2_relat_1(k2_wellord1(sK2,X0)),X1)) ) | ~spl4_3),
% 2.22/0.71    inference(superposition,[],[f175,f178])).
% 2.22/0.71  fof(f175,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)),X2) | r1_tarski(X0,X2)) )),
% 2.22/0.71    inference(superposition,[],[f63,f62])).
% 2.22/0.71  fof(f62,plain,(
% 2.22/0.71    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 2.22/0.71    inference(definition_unfolding,[],[f39,f59,f59])).
% 2.22/0.71  fof(f39,plain,(
% 2.22/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f4])).
% 2.22/0.71  fof(f4,axiom,(
% 2.22/0.71    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.22/0.71  fof(f372,plain,(
% 2.22/0.71    spl4_24 | ~spl4_2 | ~spl4_3),
% 2.22/0.71    inference(avatar_split_clause,[],[f349,f75,f70,f369])).
% 2.22/0.71  fof(f70,plain,(
% 2.22/0.71    spl4_2 <=> r1_tarski(sK0,sK1)),
% 2.22/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.22/0.71  fof(f349,plain,(
% 2.22/0.71    r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_2 | ~spl4_3)),
% 2.22/0.71    inference(resolution,[],[f315,f72])).
% 2.22/0.71  fof(f72,plain,(
% 2.22/0.71    r1_tarski(sK0,sK1) | ~spl4_2),
% 2.22/0.71    inference(avatar_component_clause,[],[f70])).
% 2.22/0.71  fof(f315,plain,(
% 2.22/0.71    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X2)),X3)) ) | ~spl4_3),
% 2.22/0.71    inference(resolution,[],[f313,f54])).
% 2.22/0.71  fof(f54,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f34])).
% 2.22/0.71  fof(f34,plain,(
% 2.22/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.22/0.71    inference(flattening,[],[f33])).
% 2.22/0.71  fof(f33,plain,(
% 2.22/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.22/0.71    inference(ennf_transformation,[],[f3])).
% 2.22/0.71  fof(f3,axiom,(
% 2.22/0.71    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.22/0.71  fof(f313,plain,(
% 2.22/0.71    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)) ) | ~spl4_3),
% 2.22/0.71    inference(duplicate_literal_removal,[],[f308])).
% 2.22/0.71  fof(f308,plain,(
% 2.22/0.71    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)) ) | ~spl4_3),
% 2.22/0.71    inference(resolution,[],[f249,f48])).
% 2.22/0.71  fof(f48,plain,(
% 2.22/0.71    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f28])).
% 2.22/0.71  fof(f28,plain,(
% 2.22/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.22/0.71    inference(ennf_transformation,[],[f1])).
% 2.22/0.71  fof(f1,axiom,(
% 2.22/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.22/0.71  fof(f249,plain,(
% 2.22/0.71    ( ! [X0,X1] : (r2_hidden(sK3(k3_relat_1(k2_wellord1(sK2,X0)),X1),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1)) ) | ~spl4_3),
% 2.22/0.71    inference(resolution,[],[f117,f77])).
% 2.22/0.71  fof(f117,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(k3_relat_1(k2_wellord1(X0,X1)),X2),X1) | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2)) )),
% 2.22/0.71    inference(resolution,[],[f52,f47])).
% 2.22/0.71  fof(f47,plain,(
% 2.22/0.71    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f28])).
% 2.22/0.71  fof(f52,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2) | r2_hidden(X0,X1)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f31])).
% 2.22/0.71  fof(f31,plain,(
% 2.22/0.71    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 2.22/0.71    inference(flattening,[],[f30])).
% 2.22/0.71  fof(f30,plain,(
% 2.22/0.71    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.22/0.71    inference(ennf_transformation,[],[f15])).
% 2.22/0.71  fof(f15,axiom,(
% 2.22/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).
% 2.22/0.71  fof(f224,plain,(
% 2.22/0.71    ~spl4_14 | spl4_1 | ~spl4_3),
% 2.22/0.71    inference(avatar_split_clause,[],[f216,f75,f65,f220])).
% 2.22/0.71  fof(f65,plain,(
% 2.22/0.71    spl4_1 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 2.22/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.22/0.71  fof(f216,plain,(
% 2.22/0.71    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | (spl4_1 | ~spl4_3)),
% 2.22/0.71    inference(superposition,[],[f67,f158])).
% 2.22/0.71  fof(f158,plain,(
% 2.22/0.71    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)) ) | ~spl4_3),
% 2.22/0.71    inference(resolution,[],[f50,f77])).
% 2.22/0.71  fof(f50,plain,(
% 2.22/0.71    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 2.22/0.71    inference(cnf_transformation,[],[f29])).
% 2.22/0.71  fof(f29,plain,(
% 2.22/0.71    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 2.22/0.71    inference(ennf_transformation,[],[f16])).
% 2.22/0.71  fof(f16,axiom,(
% 2.22/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).
% 2.22/0.71  fof(f67,plain,(
% 2.22/0.71    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) | spl4_1),
% 2.22/0.71    inference(avatar_component_clause,[],[f65])).
% 2.22/0.71  fof(f78,plain,(
% 2.22/0.71    spl4_3),
% 2.22/0.71    inference(avatar_split_clause,[],[f35,f75])).
% 2.22/0.71  fof(f35,plain,(
% 2.22/0.71    v1_relat_1(sK2)),
% 2.22/0.71    inference(cnf_transformation,[],[f20])).
% 2.22/0.71  fof(f20,plain,(
% 2.22/0.71    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 2.22/0.71    inference(flattening,[],[f19])).
% 2.22/0.71  fof(f19,plain,(
% 2.22/0.71    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 2.22/0.71    inference(ennf_transformation,[],[f18])).
% 2.22/0.71  fof(f18,negated_conjecture,(
% 2.22/0.71    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 2.22/0.71    inference(negated_conjecture,[],[f17])).
% 2.22/0.71  fof(f17,conjecture,(
% 2.22/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 2.22/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 2.22/0.71  fof(f73,plain,(
% 2.22/0.71    spl4_2),
% 2.22/0.71    inference(avatar_split_clause,[],[f36,f70])).
% 2.22/0.71  fof(f36,plain,(
% 2.22/0.71    r1_tarski(sK0,sK1)),
% 2.22/0.71    inference(cnf_transformation,[],[f20])).
% 2.22/0.71  fof(f68,plain,(
% 2.22/0.71    ~spl4_1),
% 2.22/0.71    inference(avatar_split_clause,[],[f37,f65])).
% 2.22/0.71  fof(f37,plain,(
% 2.22/0.71    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 2.22/0.71    inference(cnf_transformation,[],[f20])).
% 2.22/0.71  % SZS output end Proof for theBenchmark
% 2.22/0.71  % (7048)------------------------------
% 2.22/0.71  % (7048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.71  % (7048)Termination reason: Refutation
% 2.22/0.71  
% 2.22/0.71  % (7048)Memory used [KB]: 11641
% 2.22/0.71  % (7048)Time elapsed: 0.257 s
% 2.22/0.71  % (7048)------------------------------
% 2.22/0.71  % (7048)------------------------------
% 2.22/0.71  % (7031)Success in time 0.349 s
%------------------------------------------------------------------------------
