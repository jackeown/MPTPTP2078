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
% DateTime   : Thu Dec  3 12:52:30 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 445 expanded)
%              Number of leaves         :   18 ( 136 expanded)
%              Depth                    :   21
%              Number of atoms          :  175 ( 662 expanded)
%              Number of equality atoms :   76 ( 343 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10168)Refutation not found, incomplete strategy% (10168)------------------------------
% (10168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10168)Termination reason: Refutation not found, incomplete strategy

% (10168)Memory used [KB]: 1663
% (10168)Time elapsed: 0.100 s
% (10168)------------------------------
% (10168)------------------------------
fof(f1156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f1149,f1155])).

fof(f1155,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f95,f130])).

fof(f130,plain,(
    ! [X2,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) ),
    inference(superposition,[],[f117,f111])).

fof(f111,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))) = k8_relat_1(X2,k6_relat_1(X3)) ),
    inference(superposition,[],[f110,f101])).

fof(f101,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f74,f72])).

fof(f72,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f74,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f41,f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f110,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(forward_demodulation,[],[f109,f101])).

fof(f109,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(forward_demodulation,[],[f107,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f107,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) ),
    inference(resolution,[],[f55,f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

% (10170)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% (10169)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% (10171)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% (10169)Refutation not found, incomplete strategy% (10169)------------------------------
% (10169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10169)Termination reason: Refutation not found, incomplete strategy

% (10169)Memory used [KB]: 10618
% (10169)Time elapsed: 0.109 s
% (10169)------------------------------
% (10169)------------------------------
% (10135)Refutation not found, incomplete strategy% (10135)------------------------------
% (10135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10135)Termination reason: Refutation not found, incomplete strategy
% (10167)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark

% (10135)Memory used [KB]: 6140
% (10135)Time elapsed: 0.255 s
% (10135)------------------------------
% (10135)------------------------------
fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f117,plain,(
    ! [X8,X9] : r1_tarski(k8_relat_1(X9,k6_relat_1(X8)),k6_relat_1(X8)) ),
    inference(superposition,[],[f52,f100])).

fof(f100,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0))) ),
    inference(forward_demodulation,[],[f98,f33])).

fof(f98,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0))) ),
    inference(resolution,[],[f54,f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f95,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,k6_relat_1(sK1)),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_4
  <=> r1_tarski(k8_relat_1(sK0,k6_relat_1(sK1)),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1149,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f1132])).

fof(f1132,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f1122,f91])).

fof(f91,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k8_relat_1(sK0,k6_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_3
  <=> r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k8_relat_1(sK0,k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1122,plain,(
    ! [X4,X3] : r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),k8_relat_1(X3,k6_relat_1(X4))) ),
    inference(forward_demodulation,[],[f1121,f111])).

fof(f1121,plain,(
    ! [X4,X3] : r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),k8_relat_1(X3,k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))))) ),
    inference(forward_demodulation,[],[f1111,f33])).

fof(f1111,plain,(
    ! [X4,X3] : r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),k8_relat_1(X3,k6_relat_1(k1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))))))) ),
    inference(superposition,[],[f949,f106])).

fof(f106,plain,(
    ! [X2,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k8_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k6_relat_1(X1)) ),
    inference(resolution,[],[f104,f52])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f78,f72])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f44,f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

% (10134)Refutation not found, incomplete strategy% (10134)------------------------------
% (10134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10134)Termination reason: Refutation not found, incomplete strategy

% (10134)Memory used [KB]: 6140
% (10134)Time elapsed: 0.259 s
% (10134)------------------------------
% (10134)------------------------------
fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f949,plain,(
    ! [X4,X5] : r1_tarski(k8_relat_1(X4,k6_relat_1(X5)),k8_relat_1(X5,k6_relat_1(k1_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) ),
    inference(superposition,[],[f943,f411])).

fof(f411,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3)))))) ),
    inference(superposition,[],[f122,f288])).

fof(f288,plain,(
    ! [X14,X12,X13] : k5_relat_1(k6_relat_1(X14),k8_relat_1(X12,k6_relat_1(X13))) = k8_relat_1(X12,k8_relat_1(X13,k6_relat_1(X14))) ),
    inference(backward_demodulation,[],[f123,f284])).

fof(f284,plain,(
    ! [X2,X0,X1] : k7_relat_1(k8_relat_1(X2,k6_relat_1(X1)),X0) = k8_relat_1(X2,k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f283,f124])).

fof(f124,plain,(
    ! [X17,X15,X16] : k8_relat_1(X15,k8_relat_1(X16,k6_relat_1(X17))) = k5_relat_1(k8_relat_1(X16,k6_relat_1(X17)),k6_relat_1(X15)) ),
    inference(resolution,[],[f118,f40])).

fof(f118,plain,(
    ! [X6,X7] : v1_relat_1(k8_relat_1(X7,k6_relat_1(X6))) ),
    inference(subsumption_resolution,[],[f116,f31])).

fof(f116,plain,(
    ! [X6,X7] :
      ( v1_relat_1(k8_relat_1(X7,k6_relat_1(X6)))
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(superposition,[],[f53,f100])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f283,plain,(
    ! [X2,X0,X1] : k7_relat_1(k8_relat_1(X2,k6_relat_1(X1)),X0) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f282,f72])).

fof(f282,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k8_relat_1(X2,k6_relat_1(X1)),X0) ),
    inference(forward_demodulation,[],[f279,f123])).

fof(f279,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(resolution,[],[f143,f31])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1))) ) ),
    inference(forward_demodulation,[],[f140,f72])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f102,f31])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f35,f31])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f123,plain,(
    ! [X14,X12,X13] : k7_relat_1(k8_relat_1(X12,k6_relat_1(X13)),X14) = k5_relat_1(k6_relat_1(X14),k8_relat_1(X12,k6_relat_1(X13))) ),
    inference(resolution,[],[f118,f41])).

fof(f122,plain,(
    ! [X10,X11] : k8_relat_1(X10,k6_relat_1(X11)) = k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X10,k6_relat_1(X11)))),k8_relat_1(X10,k6_relat_1(X11))) ),
    inference(resolution,[],[f118,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(resolution,[],[f44,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

% (10165)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f943,plain,(
    ! [X2,X0,X1] : r1_tarski(k8_relat_1(X2,k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[],[f484,f100])).

fof(f484,plain,(
    ! [X2,X0,X1] : r1_tarski(k8_relat_1(X2,k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1))),k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1))) ),
    inference(superposition,[],[f52,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2))) = k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2)),k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2)),k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2)),k2_zfmisc_1(k1_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2))),X0))) ),
    inference(resolution,[],[f99,f31])).

fof(f99,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | k8_relat_1(X2,k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)),k1_setfam_1(k2_enumset1(X3,X3,X3,X4)),k1_setfam_1(k2_enumset1(X3,X3,X3,X4)),k2_zfmisc_1(k1_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X2))) ) ),
    inference(resolution,[],[f54,f53])).

fof(f97,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f87,f89,f93])).

fof(f87,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k8_relat_1(sK0,k6_relat_1(sK1)))
    | ~ r1_tarski(k8_relat_1(sK0,k6_relat_1(sK1)),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    inference(extensionality_resolution,[],[f47,f83])).

fof(f83,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f51,f72])).

fof(f51,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f30,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f26])).

fof(f26,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (10145)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (10142)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (10142)Refutation not found, incomplete strategy% (10142)------------------------------
% 0.20/0.51  % (10142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10142)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10142)Memory used [KB]: 10618
% 0.20/0.51  % (10142)Time elapsed: 0.104 s
% 0.20/0.51  % (10142)------------------------------
% 0.20/0.51  % (10142)------------------------------
% 0.20/0.51  % (10140)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (10136)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (10157)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (10157)Refutation not found, incomplete strategy% (10157)------------------------------
% 0.20/0.51  % (10157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10157)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10157)Memory used [KB]: 6140
% 0.20/0.51  % (10157)Time elapsed: 0.117 s
% 0.20/0.51  % (10157)------------------------------
% 0.20/0.51  % (10157)------------------------------
% 0.20/0.51  % (10137)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (10132)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (10135)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (10138)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (10141)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (10161)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (10159)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (10161)Refutation not found, incomplete strategy% (10161)------------------------------
% 0.20/0.52  % (10161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10159)Refutation not found, incomplete strategy% (10159)------------------------------
% 0.20/0.52  % (10159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10159)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10159)Memory used [KB]: 6140
% 0.20/0.52  % (10159)Time elapsed: 0.120 s
% 0.20/0.52  % (10159)------------------------------
% 0.20/0.52  % (10159)------------------------------
% 0.20/0.52  % (10153)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (10156)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (10161)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10161)Memory used [KB]: 1663
% 0.20/0.52  % (10161)Time elapsed: 0.004 s
% 0.20/0.52  % (10161)------------------------------
% 0.20/0.52  % (10161)------------------------------
% 0.20/0.52  % (10156)Refutation not found, incomplete strategy% (10156)------------------------------
% 0.20/0.52  % (10156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10156)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10156)Memory used [KB]: 10618
% 0.20/0.52  % (10156)Time elapsed: 0.124 s
% 0.20/0.52  % (10156)------------------------------
% 0.20/0.52  % (10156)------------------------------
% 0.20/0.52  % (10146)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (10146)Refutation not found, incomplete strategy% (10146)------------------------------
% 0.20/0.52  % (10146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10146)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10146)Memory used [KB]: 1663
% 0.20/0.52  % (10146)Time elapsed: 0.092 s
% 0.20/0.52  % (10146)------------------------------
% 0.20/0.52  % (10146)------------------------------
% 0.20/0.53  % (10143)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (10154)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (10143)Refutation not found, incomplete strategy% (10143)------------------------------
% 0.20/0.53  % (10143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10143)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10143)Memory used [KB]: 6140
% 0.20/0.53  % (10143)Time elapsed: 0.134 s
% 0.20/0.53  % (10143)------------------------------
% 0.20/0.53  % (10143)------------------------------
% 0.20/0.53  % (10133)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (10133)Refutation not found, incomplete strategy% (10133)------------------------------
% 0.20/0.53  % (10133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10133)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10133)Memory used [KB]: 1663
% 0.20/0.53  % (10133)Time elapsed: 0.126 s
% 0.20/0.53  % (10133)------------------------------
% 0.20/0.53  % (10133)------------------------------
% 0.20/0.53  % (10149)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (10160)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (10149)Refutation not found, incomplete strategy% (10149)------------------------------
% 0.20/0.53  % (10149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10149)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10149)Memory used [KB]: 1663
% 0.20/0.53  % (10149)Time elapsed: 0.132 s
% 0.20/0.53  % (10149)------------------------------
% 0.20/0.53  % (10149)------------------------------
% 0.20/0.53  % (10160)Refutation not found, incomplete strategy% (10160)------------------------------
% 0.20/0.53  % (10160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10160)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10160)Memory used [KB]: 10618
% 0.20/0.53  % (10160)Time elapsed: 0.129 s
% 0.20/0.53  % (10160)------------------------------
% 0.20/0.53  % (10160)------------------------------
% 0.20/0.53  % (10148)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (10155)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (10148)Refutation not found, incomplete strategy% (10148)------------------------------
% 0.20/0.53  % (10148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10148)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10148)Memory used [KB]: 10618
% 0.20/0.53  % (10148)Time elapsed: 0.126 s
% 0.20/0.53  % (10148)------------------------------
% 0.20/0.53  % (10148)------------------------------
% 0.20/0.54  % (10134)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (10158)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (10158)Refutation not found, incomplete strategy% (10158)------------------------------
% 0.20/0.54  % (10158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10158)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10158)Memory used [KB]: 6140
% 0.20/0.54  % (10158)Time elapsed: 0.138 s
% 0.20/0.54  % (10158)------------------------------
% 0.20/0.54  % (10158)------------------------------
% 0.20/0.55  % (10150)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (10150)Refutation not found, incomplete strategy% (10150)------------------------------
% 0.20/0.55  % (10150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10150)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10150)Memory used [KB]: 1663
% 0.20/0.55  % (10150)Time elapsed: 0.150 s
% 0.20/0.55  % (10150)------------------------------
% 0.20/0.55  % (10150)------------------------------
% 0.20/0.55  % (10151)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (10152)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (10147)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (10139)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.56  % (10144)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (10144)Refutation not found, incomplete strategy% (10144)------------------------------
% 0.20/0.56  % (10144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10144)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10144)Memory used [KB]: 10618
% 0.20/0.56  % (10144)Time elapsed: 0.162 s
% 0.20/0.56  % (10144)------------------------------
% 0.20/0.56  % (10144)------------------------------
% 2.14/0.64  % (10163)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.14/0.65  % (10138)Refutation found. Thanks to Tanya!
% 2.14/0.65  % SZS status Theorem for theBenchmark
% 2.14/0.65  % (10166)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.14/0.65  % (10168)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.14/0.65  % (10140)Refutation not found, incomplete strategy% (10140)------------------------------
% 2.14/0.65  % (10140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.65  % (10140)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.65  
% 2.14/0.65  % (10140)Memory used [KB]: 6140
% 2.14/0.65  % (10140)Time elapsed: 0.229 s
% 2.14/0.65  % (10140)------------------------------
% 2.14/0.65  % (10140)------------------------------
% 2.14/0.65  % SZS output start Proof for theBenchmark
% 2.14/0.65  % (10168)Refutation not found, incomplete strategy% (10168)------------------------------
% 2.14/0.65  % (10168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.65  % (10168)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.65  
% 2.14/0.65  % (10168)Memory used [KB]: 1663
% 2.14/0.65  % (10168)Time elapsed: 0.100 s
% 2.14/0.65  % (10168)------------------------------
% 2.14/0.65  % (10168)------------------------------
% 2.14/0.65  fof(f1156,plain,(
% 2.14/0.65    $false),
% 2.14/0.65    inference(avatar_sat_refutation,[],[f97,f1149,f1155])).
% 2.14/0.65  fof(f1155,plain,(
% 2.14/0.65    spl2_4),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f1154])).
% 2.14/0.65  fof(f1154,plain,(
% 2.14/0.65    $false | spl2_4),
% 2.14/0.65    inference(subsumption_resolution,[],[f95,f130])).
% 2.14/0.65  fof(f130,plain,(
% 2.14/0.65    ( ! [X2,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))))) )),
% 2.14/0.65    inference(superposition,[],[f117,f111])).
% 2.14/0.65  fof(f111,plain,(
% 2.14/0.65    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))) = k8_relat_1(X2,k6_relat_1(X3))) )),
% 2.14/0.65    inference(superposition,[],[f110,f101])).
% 2.14/0.65  fof(f101,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.14/0.65    inference(forward_demodulation,[],[f74,f72])).
% 2.14/0.65  fof(f72,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 2.14/0.65    inference(resolution,[],[f40,f31])).
% 2.14/0.65  fof(f31,plain,(
% 2.14/0.65    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f14])).
% 2.14/0.65  fof(f14,axiom,(
% 2.14/0.65    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.14/0.65  fof(f40,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f20])).
% 2.14/0.65  fof(f20,plain,(
% 2.14/0.65    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.14/0.65    inference(ennf_transformation,[],[f7])).
% 2.14/0.65  fof(f7,axiom,(
% 2.14/0.65    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 2.14/0.66  fof(f74,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.14/0.66    inference(resolution,[],[f41,f31])).
% 2.14/0.66  fof(f41,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f21])).
% 2.14/0.66  fof(f21,plain,(
% 2.14/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f13])).
% 2.14/0.66  fof(f13,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.14/0.66  fof(f110,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f109,f101])).
% 2.14/0.66  fof(f109,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f107,f33])).
% 2.14/0.66  fof(f33,plain,(
% 2.14/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.14/0.66    inference(cnf_transformation,[],[f11])).
% 2.14/0.66  fof(f11,axiom,(
% 2.14/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.14/0.66  fof(f107,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)))) )),
% 2.14/0.66    inference(resolution,[],[f55,f31])).
% 2.14/0.66  fof(f55,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 2.14/0.66    inference(definition_unfolding,[],[f43,f50])).
% 2.14/0.66  fof(f50,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.14/0.66    inference(definition_unfolding,[],[f37,f49])).
% 2.14/0.66  fof(f49,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.14/0.66    inference(definition_unfolding,[],[f38,f48])).
% 2.14/0.66  fof(f48,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f4])).
% 2.14/0.66  fof(f4,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.14/0.66  fof(f38,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f3])).
% 2.14/0.66  fof(f3,axiom,(
% 2.14/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.14/0.66  fof(f37,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.14/0.66    inference(cnf_transformation,[],[f5])).
% 2.14/0.66  fof(f5,axiom,(
% 2.14/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.14/0.66  fof(f43,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f23])).
% 2.14/0.66  % (10170)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.14/0.66  % (10169)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.14/0.66  % (10171)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.14/0.66  % (10169)Refutation not found, incomplete strategy% (10169)------------------------------
% 2.14/0.66  % (10169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (10169)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.66  
% 2.14/0.66  % (10169)Memory used [KB]: 10618
% 2.14/0.66  % (10169)Time elapsed: 0.109 s
% 2.14/0.66  % (10169)------------------------------
% 2.14/0.66  % (10169)------------------------------
% 2.14/0.66  % (10135)Refutation not found, incomplete strategy% (10135)------------------------------
% 2.14/0.66  % (10135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (10135)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.66  % (10167)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.14/0.66  
% 2.14/0.66  % (10135)Memory used [KB]: 6140
% 2.14/0.66  % (10135)Time elapsed: 0.255 s
% 2.14/0.66  % (10135)------------------------------
% 2.14/0.66  % (10135)------------------------------
% 2.14/0.66  fof(f23,plain,(
% 2.14/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f9])).
% 2.14/0.66  fof(f9,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 2.14/0.66  fof(f117,plain,(
% 2.14/0.66    ( ! [X8,X9] : (r1_tarski(k8_relat_1(X9,k6_relat_1(X8)),k6_relat_1(X8))) )),
% 2.14/0.66    inference(superposition,[],[f52,f100])).
% 2.14/0.66  fof(f100,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0)))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f98,f33])).
% 2.14/0.66  fof(f98,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0)))) )),
% 2.14/0.66    inference(resolution,[],[f54,f31])).
% 2.14/0.66  fof(f54,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 2.14/0.66    inference(definition_unfolding,[],[f42,f50])).
% 2.14/0.66  fof(f42,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f22])).
% 2.14/0.66  fof(f22,plain,(
% 2.14/0.66    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f8])).
% 2.14/0.66  fof(f8,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 2.14/0.66  fof(f52,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 2.14/0.66    inference(definition_unfolding,[],[f36,f50])).
% 2.14/0.66  fof(f36,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f2])).
% 2.14/0.66  fof(f2,axiom,(
% 2.14/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.14/0.66  fof(f95,plain,(
% 2.14/0.66    ~r1_tarski(k8_relat_1(sK0,k6_relat_1(sK1)),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | spl2_4),
% 2.14/0.66    inference(avatar_component_clause,[],[f93])).
% 2.14/0.66  fof(f93,plain,(
% 2.14/0.66    spl2_4 <=> r1_tarski(k8_relat_1(sK0,k6_relat_1(sK1)),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.14/0.66  fof(f1149,plain,(
% 2.14/0.66    spl2_3),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f1132])).
% 2.14/0.66  fof(f1132,plain,(
% 2.14/0.66    $false | spl2_3),
% 2.14/0.66    inference(resolution,[],[f1122,f91])).
% 2.14/0.66  fof(f91,plain,(
% 2.14/0.66    ~r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k8_relat_1(sK0,k6_relat_1(sK1))) | spl2_3),
% 2.14/0.66    inference(avatar_component_clause,[],[f89])).
% 2.14/0.66  fof(f89,plain,(
% 2.14/0.66    spl2_3 <=> r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k8_relat_1(sK0,k6_relat_1(sK1)))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.14/0.66  fof(f1122,plain,(
% 2.14/0.66    ( ! [X4,X3] : (r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),k8_relat_1(X3,k6_relat_1(X4)))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f1121,f111])).
% 2.14/0.66  fof(f1121,plain,(
% 2.14/0.66    ( ! [X4,X3] : (r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),k8_relat_1(X3,k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f1111,f33])).
% 2.14/0.66  fof(f1111,plain,(
% 2.14/0.66    ( ! [X4,X3] : (r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),k8_relat_1(X3,k6_relat_1(k1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))))))) )),
% 2.14/0.66    inference(superposition,[],[f949,f106])).
% 2.14/0.66  fof(f106,plain,(
% 2.14/0.66    ( ! [X2,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k8_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k6_relat_1(X1))) )),
% 2.14/0.66    inference(resolution,[],[f104,f52])).
% 2.14/0.66  fof(f104,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f78,f72])).
% 2.14/0.66  fof(f78,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f77,f31])).
% 2.14/0.66  fof(f77,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.14/0.66    inference(superposition,[],[f44,f33])).
% 2.14/0.66  fof(f44,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f25])).
% 2.14/0.66  % (10134)Refutation not found, incomplete strategy% (10134)------------------------------
% 2.14/0.66  % (10134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (10134)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.66  
% 2.14/0.66  % (10134)Memory used [KB]: 6140
% 2.14/0.66  % (10134)Time elapsed: 0.259 s
% 2.14/0.66  % (10134)------------------------------
% 2.14/0.66  % (10134)------------------------------
% 2.14/0.66  fof(f25,plain,(
% 2.14/0.66    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(flattening,[],[f24])).
% 2.14/0.66  fof(f24,plain,(
% 2.14/0.66    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f12])).
% 2.14/0.66  fof(f12,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 2.14/0.66  fof(f949,plain,(
% 2.14/0.66    ( ! [X4,X5] : (r1_tarski(k8_relat_1(X4,k6_relat_1(X5)),k8_relat_1(X5,k6_relat_1(k1_relat_1(k8_relat_1(X4,k6_relat_1(X5))))))) )),
% 2.14/0.66    inference(superposition,[],[f943,f411])).
% 2.14/0.66  fof(f411,plain,(
% 2.14/0.66    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))))) )),
% 2.14/0.66    inference(superposition,[],[f122,f288])).
% 2.14/0.66  fof(f288,plain,(
% 2.14/0.66    ( ! [X14,X12,X13] : (k5_relat_1(k6_relat_1(X14),k8_relat_1(X12,k6_relat_1(X13))) = k8_relat_1(X12,k8_relat_1(X13,k6_relat_1(X14)))) )),
% 2.14/0.66    inference(backward_demodulation,[],[f123,f284])).
% 2.14/0.66  fof(f284,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X2,k6_relat_1(X1)),X0) = k8_relat_1(X2,k8_relat_1(X1,k6_relat_1(X0)))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f283,f124])).
% 2.14/0.66  fof(f124,plain,(
% 2.14/0.66    ( ! [X17,X15,X16] : (k8_relat_1(X15,k8_relat_1(X16,k6_relat_1(X17))) = k5_relat_1(k8_relat_1(X16,k6_relat_1(X17)),k6_relat_1(X15))) )),
% 2.14/0.66    inference(resolution,[],[f118,f40])).
% 2.14/0.66  fof(f118,plain,(
% 2.14/0.66    ( ! [X6,X7] : (v1_relat_1(k8_relat_1(X7,k6_relat_1(X6)))) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f116,f31])).
% 2.14/0.66  fof(f116,plain,(
% 2.14/0.66    ( ! [X6,X7] : (v1_relat_1(k8_relat_1(X7,k6_relat_1(X6))) | ~v1_relat_1(k6_relat_1(X6))) )),
% 2.14/0.66    inference(superposition,[],[f53,f100])).
% 2.14/0.66  fof(f53,plain,(
% 2.14/0.66    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(definition_unfolding,[],[f39,f50])).
% 2.14/0.66  fof(f39,plain,(
% 2.14/0.66    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f19])).
% 2.14/0.66  fof(f19,plain,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f6])).
% 2.14/0.66  fof(f6,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.14/0.66  fof(f283,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X2,k6_relat_1(X1)),X0) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f282,f72])).
% 2.14/0.66  fof(f282,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k8_relat_1(X2,k6_relat_1(X1)),X0)) )),
% 2.14/0.66    inference(forward_demodulation,[],[f279,f123])).
% 2.14/0.66  fof(f279,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1)))) )),
% 2.14/0.66    inference(resolution,[],[f143,f31])).
% 2.14/0.66  fof(f143,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1)))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f140,f72])).
% 2.14/0.66  fof(f140,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(resolution,[],[f102,f31])).
% 2.14/0.66  fof(f102,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(resolution,[],[f35,f31])).
% 2.14/0.66  fof(f35,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f18])).
% 2.14/0.66  fof(f18,plain,(
% 2.14/0.66    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f10])).
% 2.14/0.66  fof(f10,axiom,(
% 2.14/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.14/0.66  fof(f123,plain,(
% 2.14/0.66    ( ! [X14,X12,X13] : (k7_relat_1(k8_relat_1(X12,k6_relat_1(X13)),X14) = k5_relat_1(k6_relat_1(X14),k8_relat_1(X12,k6_relat_1(X13)))) )),
% 2.14/0.66    inference(resolution,[],[f118,f41])).
% 2.14/0.66  fof(f122,plain,(
% 2.14/0.66    ( ! [X10,X11] : (k8_relat_1(X10,k6_relat_1(X11)) = k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X10,k6_relat_1(X11)))),k8_relat_1(X10,k6_relat_1(X11)))) )),
% 2.14/0.66    inference(resolution,[],[f118,f76])).
% 2.14/0.66  fof(f76,plain,(
% 2.14/0.66    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.14/0.66    inference(resolution,[],[f44,f56])).
% 2.14/0.66  fof(f56,plain,(
% 2.14/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.14/0.66    inference(equality_resolution,[],[f46])).
% 2.14/0.66  % (10165)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.14/0.66  fof(f46,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.14/0.66    inference(cnf_transformation,[],[f29])).
% 2.14/0.66  fof(f29,plain,(
% 2.14/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.66    inference(flattening,[],[f28])).
% 2.14/0.66  fof(f28,plain,(
% 2.14/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.66    inference(nnf_transformation,[],[f1])).
% 2.14/0.66  fof(f1,axiom,(
% 2.14/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.66  fof(f943,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X2,k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X1,k6_relat_1(X0)))) )),
% 2.14/0.66    inference(superposition,[],[f484,f100])).
% 2.14/0.66  fof(f484,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X2,k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1))),k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1)))) )),
% 2.14/0.66    inference(superposition,[],[f52,f200])).
% 2.14/0.66  fof(f200,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (k8_relat_1(X0,k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2))) = k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2)),k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2)),k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2)),k2_zfmisc_1(k1_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),X2))),X0)))) )),
% 2.14/0.66    inference(resolution,[],[f99,f31])).
% 2.14/0.66  fof(f99,plain,(
% 2.14/0.66    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | k8_relat_1(X2,k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)),k1_setfam_1(k2_enumset1(X3,X3,X3,X4)),k1_setfam_1(k2_enumset1(X3,X3,X3,X4)),k2_zfmisc_1(k1_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X2)))) )),
% 2.14/0.66    inference(resolution,[],[f54,f53])).
% 2.14/0.66  fof(f97,plain,(
% 2.14/0.66    ~spl2_4 | ~spl2_3),
% 2.14/0.66    inference(avatar_split_clause,[],[f87,f89,f93])).
% 2.14/0.66  fof(f87,plain,(
% 2.14/0.66    ~r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k8_relat_1(sK0,k6_relat_1(sK1))) | ~r1_tarski(k8_relat_1(sK0,k6_relat_1(sK1)),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 2.14/0.66    inference(extensionality_resolution,[],[f47,f83])).
% 2.14/0.66  fof(f83,plain,(
% 2.14/0.66    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 2.14/0.66    inference(backward_demodulation,[],[f51,f72])).
% 2.14/0.66  fof(f51,plain,(
% 2.14/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 2.14/0.66    inference(definition_unfolding,[],[f30,f50])).
% 2.14/0.66  fof(f30,plain,(
% 2.14/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.14/0.66    inference(cnf_transformation,[],[f27])).
% 2.14/0.66  fof(f27,plain,(
% 2.14/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.14/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f26])).
% 2.14/0.66  fof(f26,plain,(
% 2.14/0.66    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f17,plain,(
% 2.14/0.66    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f16])).
% 2.14/0.66  fof(f16,negated_conjecture,(
% 2.14/0.66    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.14/0.66    inference(negated_conjecture,[],[f15])).
% 2.14/0.66  fof(f15,conjecture,(
% 2.14/0.66    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.14/0.66  fof(f47,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f29])).
% 2.14/0.66  % SZS output end Proof for theBenchmark
% 2.14/0.66  % (10138)------------------------------
% 2.14/0.66  % (10138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (10138)Termination reason: Refutation
% 2.14/0.66  
% 2.14/0.66  % (10138)Memory used [KB]: 12153
% 2.14/0.66  % (10138)Time elapsed: 0.226 s
% 2.14/0.66  % (10138)------------------------------
% 2.14/0.66  % (10138)------------------------------
% 2.14/0.66  % (10131)Success in time 0.296 s
%------------------------------------------------------------------------------
