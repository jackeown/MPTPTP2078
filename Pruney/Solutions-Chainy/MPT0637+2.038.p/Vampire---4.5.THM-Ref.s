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
% DateTime   : Thu Dec  3 12:52:27 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 335 expanded)
%              Number of leaves         :   20 ( 105 expanded)
%              Depth                    :   20
%              Number of atoms          :  180 ( 493 expanded)
%              Number of equality atoms :   72 ( 254 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1956,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f1943,f1955])).

fof(f1955,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1954])).

fof(f1954,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f109,f175])).

fof(f175,plain,(
    ! [X4,X5] : r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(k1_setfam_1(k2_enumset1(X4,X4,X4,X5)))) ),
    inference(superposition,[],[f99,f170])).

fof(f170,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(forward_demodulation,[],[f167,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f167,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

% (22232)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% (22208)Refutation not found, incomplete strategy% (22208)------------------------------
% (22208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22208)Termination reason: Refutation not found, incomplete strategy

% (22208)Memory used [KB]: 6140
% (22208)Time elapsed: 0.237 s
% (22208)------------------------------
% (22208)------------------------------
% (22203)Refutation not found, incomplete strategy% (22203)------------------------------
% (22203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22203)Termination reason: Refutation not found, incomplete strategy

% (22203)Memory used [KB]: 6140
% (22203)Time elapsed: 0.224 s
% (22203)------------------------------
% (22203)------------------------------
fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f99,plain,(
    ! [X4,X3] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) ),
    inference(subsumption_resolution,[],[f97,f36])).

fof(f97,plain,(
    ! [X4,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f49,f90])).

fof(f90,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f109,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_4
  <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1943,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f1920])).

fof(f1920,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f1312,f105])).

fof(f105,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_3
  <=> r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1312,plain,(
    ! [X15,X16] : r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X15,X15,X15,X16))),k7_relat_1(k6_relat_1(X15),X16)) ),
    inference(forward_demodulation,[],[f1298,f170])).

fof(f1298,plain,(
    ! [X15,X16] : r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X15,X15,X15,X16))),k7_relat_1(k6_relat_1(X15),k1_setfam_1(k2_enumset1(X15,X15,X15,X16)))) ),
    inference(superposition,[],[f1270,f133])).

fof(f133,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3) ),
    inference(resolution,[],[f127,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f126,f90])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f125,f36])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f51,f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1270,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(superposition,[],[f1256,f216])).

fof(f216,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) ),
    inference(superposition,[],[f153,f171])).

fof(f171,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(superposition,[],[f170,f62])).

fof(f62,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f43,f59,f59])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f153,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(resolution,[],[f66,f36])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f57,f59])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1256,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(subsumption_resolution,[],[f1245,f920])).

fof(f920,plain,(
    ! [X6,X7] : v1_relat_1(k7_relat_1(k6_relat_1(X7),X6)) ),
    inference(subsumption_resolution,[],[f899,f36])).

fof(f899,plain,(
    ! [X6,X7] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X7),X6))
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(superposition,[],[f63,f340])).

fof(f340,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_demodulation,[],[f337,f90])).

fof(f337,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ),
    inference(resolution,[],[f294,f36])).

fof(f294,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k5_relat_1(X1,k6_relat_1(X2)))) ) ),
    inference(forward_demodulation,[],[f115,f62])).

fof(f115,plain,(
    ! [X2,X1] :
      ( k5_relat_1(X1,k6_relat_1(X2)) = k1_setfam_1(k2_enumset1(k5_relat_1(X1,k6_relat_1(X2)),k5_relat_1(X1,k6_relat_1(X2)),k5_relat_1(X1,k6_relat_1(X2)),X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1245,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(superposition,[],[f49,f1148])).

fof(f1148,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(backward_demodulation,[],[f719,f925])).

fof(f925,plain,(
    ! [X6,X8,X7] : k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) = k5_relat_1(k6_relat_1(X8),k7_relat_1(k6_relat_1(X6),X7)) ),
    inference(resolution,[],[f920,f47])).

fof(f719,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f716,f90])).

fof(f716,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f247,f36])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f244,f90])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f162,f36])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f111,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f101,f103,f107])).

fof(f101,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    inference(extensionality_resolution,[],[f55,f93])).

fof(f93,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f60,f90])).

fof(f60,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:07:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (22213)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (22221)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (22206)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (22202)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (22215)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (22204)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (22203)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (22223)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (22210)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (22201)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (22201)Refutation not found, incomplete strategy% (22201)------------------------------
% 0.21/0.54  % (22201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22201)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22201)Memory used [KB]: 1663
% 0.21/0.54  % (22201)Time elapsed: 0.124 s
% 0.21/0.54  % (22201)------------------------------
% 0.21/0.54  % (22201)------------------------------
% 0.21/0.54  % (22222)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (22200)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (22216)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (22227)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (22227)Refutation not found, incomplete strategy% (22227)------------------------------
% 0.21/0.55  % (22227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22227)Memory used [KB]: 6140
% 0.21/0.55  % (22227)Time elapsed: 0.138 s
% 0.21/0.55  % (22227)------------------------------
% 0.21/0.55  % (22227)------------------------------
% 0.21/0.55  % (22208)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (22226)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22216)Refutation not found, incomplete strategy% (22216)------------------------------
% 0.21/0.55  % (22216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22216)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22216)Memory used [KB]: 10618
% 0.21/0.55  % (22216)Time elapsed: 0.138 s
% 0.21/0.55  % (22216)------------------------------
% 0.21/0.55  % (22216)------------------------------
% 0.21/0.55  % (22224)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (22224)Refutation not found, incomplete strategy% (22224)------------------------------
% 0.21/0.56  % (22224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22224)Memory used [KB]: 10618
% 0.21/0.56  % (22224)Time elapsed: 0.149 s
% 0.21/0.56  % (22224)------------------------------
% 0.21/0.56  % (22224)------------------------------
% 0.21/0.56  % (22217)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (22214)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (22210)Refutation not found, incomplete strategy% (22210)------------------------------
% 0.21/0.56  % (22210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22210)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22210)Memory used [KB]: 10746
% 0.21/0.56  % (22210)Time elapsed: 0.150 s
% 0.21/0.56  % (22210)------------------------------
% 0.21/0.56  % (22210)------------------------------
% 0.21/0.56  % (22226)Refutation not found, incomplete strategy% (22226)------------------------------
% 0.21/0.56  % (22226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22226)Memory used [KB]: 6140
% 0.21/0.56  % (22226)Time elapsed: 0.150 s
% 0.21/0.56  % (22226)------------------------------
% 0.21/0.56  % (22226)------------------------------
% 0.21/0.56  % (22217)Refutation not found, incomplete strategy% (22217)------------------------------
% 0.21/0.56  % (22217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22217)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22217)Memory used [KB]: 1663
% 0.21/0.56  % (22217)Time elapsed: 0.147 s
% 0.21/0.56  % (22217)------------------------------
% 0.21/0.56  % (22217)------------------------------
% 0.21/0.56  % (22207)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (22225)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (22214)Refutation not found, incomplete strategy% (22214)------------------------------
% 0.21/0.56  % (22214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22214)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22214)Memory used [KB]: 1663
% 0.21/0.56  % (22214)Time elapsed: 0.147 s
% 0.21/0.56  % (22214)------------------------------
% 0.21/0.56  % (22214)------------------------------
% 0.21/0.56  % (22209)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (22225)Refutation not found, incomplete strategy% (22225)------------------------------
% 0.21/0.56  % (22225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22225)Memory used [KB]: 6140
% 0.21/0.56  % (22225)Time elapsed: 0.136 s
% 0.21/0.56  % (22225)------------------------------
% 0.21/0.56  % (22225)------------------------------
% 0.21/0.57  % (22220)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.61/0.57  % (22211)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.61/0.57  % (22205)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.61/0.58  % (22218)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.61/0.58  % (22212)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.61/0.58  % (22212)Refutation not found, incomplete strategy% (22212)------------------------------
% 1.61/0.58  % (22212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (22212)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (22212)Memory used [KB]: 10618
% 1.61/0.58  % (22212)Time elapsed: 0.140 s
% 1.61/0.58  % (22212)------------------------------
% 1.61/0.58  % (22212)------------------------------
% 1.61/0.58  % (22211)Refutation not found, incomplete strategy% (22211)------------------------------
% 1.61/0.58  % (22211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (22211)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (22211)Memory used [KB]: 6140
% 1.61/0.58  % (22211)Time elapsed: 0.136 s
% 1.61/0.58  % (22211)------------------------------
% 1.61/0.58  % (22211)------------------------------
% 1.69/0.59  % (22228)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.69/0.59  % (22229)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.69/0.59  % (22229)Refutation not found, incomplete strategy% (22229)------------------------------
% 1.69/0.59  % (22229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (22229)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (22229)Memory used [KB]: 1663
% 1.69/0.59  % (22229)Time elapsed: 0.148 s
% 1.69/0.59  % (22229)------------------------------
% 1.69/0.59  % (22229)------------------------------
% 1.69/0.59  % (22219)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.69/0.59  % (22228)Refutation not found, incomplete strategy% (22228)------------------------------
% 1.69/0.59  % (22228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (22228)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (22228)Memory used [KB]: 10746
% 1.69/0.59  % (22228)Time elapsed: 0.151 s
% 1.69/0.59  % (22228)------------------------------
% 1.69/0.59  % (22228)------------------------------
% 1.69/0.60  % (22218)Refutation not found, incomplete strategy% (22218)------------------------------
% 1.69/0.60  % (22218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.60  % (22218)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.60  
% 1.69/0.60  % (22218)Memory used [KB]: 1663
% 1.69/0.60  % (22218)Time elapsed: 0.165 s
% 1.69/0.60  % (22218)------------------------------
% 1.69/0.60  % (22218)------------------------------
% 1.97/0.63  % (22206)Refutation found. Thanks to Tanya!
% 1.97/0.63  % SZS status Theorem for theBenchmark
% 1.97/0.63  % SZS output start Proof for theBenchmark
% 1.97/0.63  fof(f1956,plain,(
% 1.97/0.63    $false),
% 1.97/0.63    inference(avatar_sat_refutation,[],[f111,f1943,f1955])).
% 1.97/0.63  fof(f1955,plain,(
% 1.97/0.63    spl2_4),
% 1.97/0.63    inference(avatar_contradiction_clause,[],[f1954])).
% 1.97/0.63  fof(f1954,plain,(
% 1.97/0.63    $false | spl2_4),
% 1.97/0.63    inference(subsumption_resolution,[],[f109,f175])).
% 1.97/0.63  fof(f175,plain,(
% 1.97/0.63    ( ! [X4,X5] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(k1_setfam_1(k2_enumset1(X4,X4,X4,X5))))) )),
% 1.97/0.63    inference(superposition,[],[f99,f170])).
% 1.97/0.63  fof(f170,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.97/0.63    inference(forward_demodulation,[],[f167,f38])).
% 1.97/0.63  fof(f38,plain,(
% 1.97/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.97/0.63    inference(cnf_transformation,[],[f12])).
% 1.97/0.63  fof(f12,axiom,(
% 1.97/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.97/0.63  fof(f167,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)))) )),
% 1.97/0.63    inference(resolution,[],[f64,f36])).
% 1.97/0.63  fof(f36,plain,(
% 1.97/0.63    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f17])).
% 1.97/0.63  fof(f17,axiom,(
% 1.97/0.63    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.04/0.65  % (22232)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.04/0.65  % (22208)Refutation not found, incomplete strategy% (22208)------------------------------
% 2.04/0.65  % (22208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.65  % (22208)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.65  
% 2.04/0.65  % (22208)Memory used [KB]: 6140
% 2.04/0.65  % (22208)Time elapsed: 0.237 s
% 2.04/0.65  % (22208)------------------------------
% 2.04/0.65  % (22208)------------------------------
% 2.04/0.66  % (22203)Refutation not found, incomplete strategy% (22203)------------------------------
% 2.04/0.66  % (22203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.66  % (22203)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.66  
% 2.04/0.66  % (22203)Memory used [KB]: 6140
% 2.04/0.66  % (22203)Time elapsed: 0.224 s
% 2.04/0.66  % (22203)------------------------------
% 2.04/0.66  % (22203)------------------------------
% 2.04/0.66  fof(f64,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 2.04/0.66    inference(definition_unfolding,[],[f48,f59])).
% 2.04/0.66  fof(f59,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.04/0.66    inference(definition_unfolding,[],[f44,f58])).
% 2.04/0.66  fof(f58,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.04/0.66    inference(definition_unfolding,[],[f45,f56])).
% 2.04/0.66  fof(f56,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f6])).
% 2.04/0.66  fof(f6,axiom,(
% 2.04/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.04/0.66  fof(f45,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f5])).
% 2.04/0.66  fof(f5,axiom,(
% 2.04/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.04/0.66  fof(f44,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f7])).
% 2.04/0.66  fof(f7,axiom,(
% 2.04/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.04/0.66  fof(f48,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f25])).
% 2.04/0.66  fof(f25,plain,(
% 2.04/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.04/0.66    inference(ennf_transformation,[],[f10])).
% 2.04/0.66  fof(f10,axiom,(
% 2.04/0.66    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 2.04/0.66  fof(f99,plain,(
% 2.04/0.66    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))) )),
% 2.04/0.66    inference(subsumption_resolution,[],[f97,f36])).
% 2.04/0.66  fof(f97,plain,(
% 2.04/0.66    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 2.04/0.66    inference(superposition,[],[f49,f90])).
% 2.04/0.66  fof(f90,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.04/0.66    inference(resolution,[],[f47,f36])).
% 2.04/0.66  fof(f47,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f24])).
% 2.04/0.66  fof(f24,plain,(
% 2.04/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.04/0.66    inference(ennf_transformation,[],[f16])).
% 2.04/0.66  fof(f16,axiom,(
% 2.04/0.66    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.04/0.66  fof(f49,plain,(
% 2.04/0.66    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f26])).
% 2.04/0.66  fof(f26,plain,(
% 2.04/0.66    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 2.04/0.66    inference(ennf_transformation,[],[f13])).
% 2.04/0.66  fof(f13,axiom,(
% 2.04/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 2.04/0.66  fof(f109,plain,(
% 2.04/0.66    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | spl2_4),
% 2.04/0.66    inference(avatar_component_clause,[],[f107])).
% 2.04/0.66  fof(f107,plain,(
% 2.04/0.66    spl2_4 <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.04/0.66  fof(f1943,plain,(
% 2.04/0.66    spl2_3),
% 2.04/0.66    inference(avatar_contradiction_clause,[],[f1920])).
% 2.04/0.66  fof(f1920,plain,(
% 2.04/0.66    $false | spl2_3),
% 2.04/0.66    inference(resolution,[],[f1312,f105])).
% 2.04/0.66  fof(f105,plain,(
% 2.04/0.66    ~r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_3),
% 2.04/0.66    inference(avatar_component_clause,[],[f103])).
% 2.04/0.66  fof(f103,plain,(
% 2.04/0.66    spl2_3 <=> r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.04/0.66  fof(f1312,plain,(
% 2.04/0.66    ( ! [X15,X16] : (r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X15,X15,X15,X16))),k7_relat_1(k6_relat_1(X15),X16))) )),
% 2.04/0.66    inference(forward_demodulation,[],[f1298,f170])).
% 2.04/0.66  fof(f1298,plain,(
% 2.04/0.66    ( ! [X15,X16] : (r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X15,X15,X15,X16))),k7_relat_1(k6_relat_1(X15),k1_setfam_1(k2_enumset1(X15,X15,X15,X16))))) )),
% 2.04/0.66    inference(superposition,[],[f1270,f133])).
% 2.04/0.66  fof(f133,plain,(
% 2.04/0.66    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3)) )),
% 2.04/0.66    inference(resolution,[],[f127,f61])).
% 2.04/0.66  fof(f61,plain,(
% 2.04/0.66    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 2.04/0.66    inference(definition_unfolding,[],[f42,f59])).
% 2.04/0.66  fof(f42,plain,(
% 2.04/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f3])).
% 2.04/0.66  fof(f3,axiom,(
% 2.04/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.04/0.66  fof(f127,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.04/0.66    inference(forward_demodulation,[],[f126,f90])).
% 2.04/0.66  fof(f126,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 2.04/0.66    inference(subsumption_resolution,[],[f125,f36])).
% 2.04/0.66  fof(f125,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.04/0.66    inference(superposition,[],[f51,f38])).
% 2.04/0.66  fof(f51,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f28])).
% 2.04/0.66  fof(f28,plain,(
% 2.04/0.66    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.04/0.66    inference(flattening,[],[f27])).
% 2.04/0.66  fof(f27,plain,(
% 2.04/0.66    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.04/0.66    inference(ennf_transformation,[],[f14])).
% 2.04/0.66  fof(f14,axiom,(
% 2.04/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 2.04/0.66  fof(f1270,plain,(
% 2.04/0.66    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.04/0.66    inference(superposition,[],[f1256,f216])).
% 2.04/0.66  fof(f216,plain,(
% 2.04/0.66    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) )),
% 2.04/0.66    inference(superposition,[],[f153,f171])).
% 2.04/0.66  fof(f171,plain,(
% 2.04/0.66    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))) )),
% 2.04/0.66    inference(superposition,[],[f170,f62])).
% 2.04/0.66  fof(f62,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 2.04/0.66    inference(definition_unfolding,[],[f43,f59,f59])).
% 2.04/0.66  fof(f43,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f1])).
% 2.04/0.66  fof(f1,axiom,(
% 2.04/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.04/0.66  fof(f153,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) )),
% 2.04/0.66    inference(resolution,[],[f66,f36])).
% 2.04/0.66  fof(f66,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.04/0.66    inference(definition_unfolding,[],[f57,f59])).
% 2.04/0.66  fof(f57,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f30])).
% 2.04/0.66  fof(f30,plain,(
% 2.04/0.66    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.04/0.66    inference(ennf_transformation,[],[f9])).
% 2.04/0.66  fof(f9,axiom,(
% 2.04/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 2.04/0.66  fof(f1256,plain,(
% 2.04/0.66    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.04/0.66    inference(subsumption_resolution,[],[f1245,f920])).
% 2.04/0.66  fof(f920,plain,(
% 2.04/0.66    ( ! [X6,X7] : (v1_relat_1(k7_relat_1(k6_relat_1(X7),X6))) )),
% 2.04/0.66    inference(subsumption_resolution,[],[f899,f36])).
% 2.04/0.66  fof(f899,plain,(
% 2.04/0.66    ( ! [X6,X7] : (v1_relat_1(k7_relat_1(k6_relat_1(X7),X6)) | ~v1_relat_1(k6_relat_1(X6))) )),
% 2.04/0.66    inference(superposition,[],[f63,f340])).
% 2.04/0.66  fof(f340,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0)))) )),
% 2.04/0.66    inference(forward_demodulation,[],[f337,f90])).
% 2.04/0.66  fof(f337,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))))) )),
% 2.04/0.66    inference(resolution,[],[f294,f36])).
% 2.04/0.66  fof(f294,plain,(
% 2.04/0.66    ( ! [X2,X1] : (~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k5_relat_1(X1,k6_relat_1(X2))))) )),
% 2.04/0.66    inference(forward_demodulation,[],[f115,f62])).
% 2.04/0.66  fof(f115,plain,(
% 2.04/0.66    ( ! [X2,X1] : (k5_relat_1(X1,k6_relat_1(X2)) = k1_setfam_1(k2_enumset1(k5_relat_1(X1,k6_relat_1(X2)),k5_relat_1(X1,k6_relat_1(X2)),k5_relat_1(X1,k6_relat_1(X2)),X1)) | ~v1_relat_1(X1)) )),
% 2.04/0.66    inference(resolution,[],[f65,f49])).
% 2.04/0.66  fof(f65,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0) )),
% 2.04/0.66    inference(definition_unfolding,[],[f52,f59])).
% 2.04/0.66  fof(f52,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f29])).
% 2.04/0.66  fof(f29,plain,(
% 2.04/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.04/0.66    inference(ennf_transformation,[],[f4])).
% 2.04/0.66  fof(f4,axiom,(
% 2.04/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.04/0.66  fof(f63,plain,(
% 2.04/0.66    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 2.04/0.66    inference(definition_unfolding,[],[f46,f59])).
% 2.04/0.66  fof(f46,plain,(
% 2.04/0.66    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f23])).
% 2.04/0.66  fof(f23,plain,(
% 2.04/0.66    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.04/0.66    inference(ennf_transformation,[],[f8])).
% 2.04/0.66  fof(f8,axiom,(
% 2.04/0.66    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.04/0.66  fof(f1245,plain,(
% 2.04/0.66    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.04/0.66    inference(superposition,[],[f49,f1148])).
% 2.04/0.66  fof(f1148,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 2.04/0.66    inference(backward_demodulation,[],[f719,f925])).
% 2.04/0.66  fof(f925,plain,(
% 2.04/0.66    ( ! [X6,X8,X7] : (k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) = k5_relat_1(k6_relat_1(X8),k7_relat_1(k6_relat_1(X6),X7))) )),
% 2.04/0.66    inference(resolution,[],[f920,f47])).
% 2.04/0.66  fof(f719,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 2.04/0.66    inference(forward_demodulation,[],[f716,f90])).
% 2.04/0.66  fof(f716,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.04/0.66    inference(resolution,[],[f247,f36])).
% 2.04/0.66  fof(f247,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.04/0.66    inference(forward_demodulation,[],[f244,f90])).
% 2.04/0.66  fof(f244,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.04/0.66    inference(resolution,[],[f162,f36])).
% 2.04/0.66  fof(f162,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.04/0.66    inference(resolution,[],[f41,f36])).
% 2.04/0.66  fof(f41,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f22])).
% 2.04/0.66  fof(f22,plain,(
% 2.04/0.66    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.04/0.66    inference(ennf_transformation,[],[f11])).
% 2.04/0.66  fof(f11,axiom,(
% 2.04/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.04/0.66  fof(f111,plain,(
% 2.04/0.66    ~spl2_4 | ~spl2_3),
% 2.04/0.66    inference(avatar_split_clause,[],[f101,f103,f107])).
% 2.04/0.66  fof(f101,plain,(
% 2.04/0.66    ~r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 2.04/0.66    inference(extensionality_resolution,[],[f55,f93])).
% 2.04/0.66  fof(f93,plain,(
% 2.04/0.66    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.04/0.66    inference(backward_demodulation,[],[f60,f90])).
% 2.04/0.66  fof(f60,plain,(
% 2.04/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 2.04/0.66    inference(definition_unfolding,[],[f35,f59])).
% 2.04/0.66  fof(f35,plain,(
% 2.04/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.04/0.66    inference(cnf_transformation,[],[f32])).
% 2.04/0.66  fof(f32,plain,(
% 2.04/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.04/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 2.04/0.66  fof(f31,plain,(
% 2.04/0.66    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.04/0.66    introduced(choice_axiom,[])).
% 2.04/0.66  fof(f20,plain,(
% 2.04/0.66    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.04/0.66    inference(ennf_transformation,[],[f19])).
% 2.04/0.66  fof(f19,negated_conjecture,(
% 2.04/0.66    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.04/0.66    inference(negated_conjecture,[],[f18])).
% 2.04/0.66  fof(f18,conjecture,(
% 2.04/0.66    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.04/0.66  fof(f55,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f34])).
% 2.04/0.66  fof(f34,plain,(
% 2.04/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.66    inference(flattening,[],[f33])).
% 2.04/0.66  fof(f33,plain,(
% 2.04/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.66    inference(nnf_transformation,[],[f2])).
% 2.04/0.66  fof(f2,axiom,(
% 2.04/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.04/0.66  % SZS output end Proof for theBenchmark
% 2.04/0.66  % (22206)------------------------------
% 2.04/0.66  % (22206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.66  % (22206)Termination reason: Refutation
% 2.04/0.66  
% 2.04/0.66  % (22206)Memory used [KB]: 12665
% 2.04/0.66  % (22206)Time elapsed: 0.231 s
% 2.04/0.66  % (22206)------------------------------
% 2.04/0.66  % (22206)------------------------------
% 2.04/0.66  % (22199)Success in time 0.286 s
%------------------------------------------------------------------------------
