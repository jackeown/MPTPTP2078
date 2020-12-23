%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:23 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 317 expanded)
%              Number of leaves         :   20 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :  180 ( 475 expanded)
%              Number of equality atoms :   72 ( 236 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2033,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f2021,f2032])).

% (8413)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% (8408)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% (8413)Refutation not found, incomplete strategy% (8413)------------------------------
% (8413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8408)Refutation not found, incomplete strategy% (8408)------------------------------
% (8408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8408)Termination reason: Refutation not found, incomplete strategy

% (8408)Memory used [KB]: 1663
% (8408)Time elapsed: 0.106 s
% (8408)------------------------------
% (8408)------------------------------
% (8417)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% (8355)Refutation not found, incomplete strategy% (8355)------------------------------
% (8355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8355)Termination reason: Refutation not found, incomplete strategy

% (8355)Memory used [KB]: 6140
% (8355)Time elapsed: 0.224 s
% (8355)------------------------------
% (8355)------------------------------
% (8415)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% (8417)Refutation not found, incomplete strategy% (8417)------------------------------
% (8417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8417)Termination reason: Refutation not found, incomplete strategy

% (8417)Memory used [KB]: 10618
% (8417)Time elapsed: 0.096 s
% (8417)------------------------------
% (8417)------------------------------
% (8405)Memory used [KB]: 10618
% (8405)Time elapsed: 0.081 s
% (8405)------------------------------
% (8405)------------------------------
% (8407)Termination reason: Refutation not found, incomplete strategy

% (8407)Memory used [KB]: 10618
% (8407)Time elapsed: 0.086 s
% (8407)------------------------------
% (8407)------------------------------
% (8413)Termination reason: Refutation not found, incomplete strategy

% (8413)Memory used [KB]: 10618
% (8413)Time elapsed: 0.079 s
% (8413)------------------------------
% (8413)------------------------------
fof(f2032,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f2031])).

fof(f2031,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f109,f181])).

fof(f181,plain,(
    ! [X4,X5] : r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(k1_setfam_1(k2_enumset1(X4,X4,X4,X5)))) ),
    inference(superposition,[],[f99,f176])).

fof(f176,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(forward_demodulation,[],[f173,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f173,plain,(
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

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
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

fof(f2021,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f1999])).

fof(f1999,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f1383,f105])).

fof(f105,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_3
  <=> r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1383,plain,(
    ! [X15,X16] : r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X15,X15,X15,X16))),k7_relat_1(k6_relat_1(X15),X16)) ),
    inference(forward_demodulation,[],[f1369,f176])).

fof(f1369,plain,(
    ! [X15,X16] : r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X15,X15,X15,X16))),k7_relat_1(k6_relat_1(X15),k1_setfam_1(k2_enumset1(X15,X15,X15,X16)))) ),
    inference(superposition,[],[f1327,f157])).

fof(f157,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3) ),
    inference(resolution,[],[f147,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f146,f90])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f145,f36])).

fof(f145,plain,(
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

fof(f1327,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f1314,f281])).

fof(f281,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) ),
    inference(superposition,[],[f152,f177])).

fof(f177,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f176,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f58,f58])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f152,plain,(
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

fof(f1314,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(subsumption_resolution,[],[f1303,f934])).

fof(f934,plain,(
    ! [X2,X3] : v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(subsumption_resolution,[],[f911,f36])).

fof(f911,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f63,f221])).

fof(f221,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_demodulation,[],[f218,f90])).

fof(f218,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ),
    inference(resolution,[],[f130,f36])).

fof(f130,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k5_relat_1(X1,k6_relat_1(X2)))) ) ),
    inference(forward_demodulation,[],[f124,f62])).

fof(f124,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f1303,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(superposition,[],[f49,f1162])).

fof(f1162,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(backward_demodulation,[],[f722,f939])).

fof(f939,plain,(
    ! [X6,X8,X7] : k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) = k5_relat_1(k6_relat_1(X8),k7_relat_1(k6_relat_1(X6),X7)) ),
    inference(resolution,[],[f934,f47])).

fof(f722,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f719,f90])).

fof(f719,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f324,f36])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f321,f90])).

fof(f321,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f168,f36])).

fof(f168,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:52:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (8359)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (8361)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (8367)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (8367)Refutation not found, incomplete strategy% (8367)------------------------------
% 0.22/0.51  % (8367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8367)Memory used [KB]: 1663
% 0.22/0.51  % (8367)Time elapsed: 0.081 s
% 0.22/0.51  % (8367)------------------------------
% 0.22/0.51  % (8367)------------------------------
% 0.22/0.52  % (8362)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (8375)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (8369)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (8360)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (8370)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (8354)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (8354)Refutation not found, incomplete strategy% (8354)------------------------------
% 0.22/0.53  % (8354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8354)Memory used [KB]: 1663
% 0.22/0.53  % (8354)Time elapsed: 0.106 s
% 0.22/0.53  % (8354)------------------------------
% 0.22/0.53  % (8354)------------------------------
% 0.22/0.54  % (8382)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (8376)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (8369)Refutation not found, incomplete strategy% (8369)------------------------------
% 0.22/0.54  % (8369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8377)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (8369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8369)Memory used [KB]: 10618
% 0.22/0.54  % (8369)Time elapsed: 0.116 s
% 0.22/0.54  % (8369)------------------------------
% 0.22/0.54  % (8369)------------------------------
% 0.22/0.54  % (8377)Refutation not found, incomplete strategy% (8377)------------------------------
% 0.22/0.54  % (8377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8377)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8377)Memory used [KB]: 10618
% 0.22/0.54  % (8377)Time elapsed: 0.112 s
% 0.22/0.54  % (8377)------------------------------
% 0.22/0.54  % (8377)------------------------------
% 0.22/0.54  % (8378)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (8370)Refutation not found, incomplete strategy% (8370)------------------------------
% 0.22/0.54  % (8370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8370)Memory used [KB]: 1663
% 0.22/0.54  % (8370)Time elapsed: 0.110 s
% 0.22/0.54  % (8370)------------------------------
% 0.22/0.54  % (8370)------------------------------
% 0.22/0.54  % (8356)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (8372)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (8378)Refutation not found, incomplete strategy% (8378)------------------------------
% 0.22/0.54  % (8378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8378)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8378)Memory used [KB]: 6140
% 0.22/0.54  % (8378)Time elapsed: 0.110 s
% 0.22/0.54  % (8378)------------------------------
% 0.22/0.54  % (8378)------------------------------
% 0.22/0.55  % (8371)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (8371)Refutation not found, incomplete strategy% (8371)------------------------------
% 0.22/0.55  % (8371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8371)Memory used [KB]: 1663
% 0.22/0.55  % (8371)Time elapsed: 0.087 s
% 0.22/0.55  % (8371)------------------------------
% 0.22/0.55  % (8371)------------------------------
% 0.22/0.55  % (8358)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (8355)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (8353)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (8368)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (8380)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (8380)Refutation not found, incomplete strategy% (8380)------------------------------
% 0.22/0.55  % (8380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8380)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8380)Memory used [KB]: 6140
% 0.22/0.55  % (8380)Time elapsed: 0.128 s
% 0.22/0.55  % (8380)------------------------------
% 0.22/0.55  % (8380)------------------------------
% 0.22/0.55  % (8363)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (8366)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (8363)Refutation not found, incomplete strategy% (8363)------------------------------
% 0.22/0.56  % (8363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8363)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8363)Memory used [KB]: 10746
% 0.22/0.56  % (8363)Time elapsed: 0.098 s
% 0.22/0.56  % (8363)------------------------------
% 0.22/0.56  % (8363)------------------------------
% 0.22/0.56  % (8364)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (8364)Refutation not found, incomplete strategy% (8364)------------------------------
% 0.22/0.56  % (8364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8364)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8364)Memory used [KB]: 6140
% 0.22/0.56  % (8364)Time elapsed: 0.125 s
% 0.22/0.56  % (8364)------------------------------
% 0.22/0.56  % (8364)------------------------------
% 0.22/0.56  % (8382)Refutation not found, incomplete strategy% (8382)------------------------------
% 0.22/0.56  % (8382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8382)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8382)Memory used [KB]: 1663
% 0.22/0.56  % (8382)Time elapsed: 0.141 s
% 0.22/0.56  % (8382)------------------------------
% 0.22/0.56  % (8382)------------------------------
% 0.22/0.56  % (8379)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (8379)Refutation not found, incomplete strategy% (8379)------------------------------
% 0.22/0.56  % (8379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8379)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8379)Memory used [KB]: 6140
% 0.22/0.56  % (8379)Time elapsed: 0.107 s
% 0.22/0.56  % (8379)------------------------------
% 0.22/0.56  % (8379)------------------------------
% 0.22/0.56  % (8381)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (8357)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % (8374)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (8373)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (8381)Refutation not found, incomplete strategy% (8381)------------------------------
% 0.22/0.57  % (8381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (8381)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (8381)Memory used [KB]: 10746
% 0.22/0.57  % (8381)Time elapsed: 0.150 s
% 0.22/0.57  % (8381)------------------------------
% 0.22/0.57  % (8381)------------------------------
% 0.22/0.58  % (8365)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (8365)Refutation not found, incomplete strategy% (8365)------------------------------
% 0.22/0.58  % (8365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (8365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (8365)Memory used [KB]: 10618
% 0.22/0.58  % (8365)Time elapsed: 0.160 s
% 0.22/0.58  % (8365)------------------------------
% 0.22/0.58  % (8365)------------------------------
% 2.00/0.63  % (8361)Refutation not found, incomplete strategy% (8361)------------------------------
% 2.00/0.63  % (8361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.64  % (8361)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.64  
% 2.00/0.64  % (8361)Memory used [KB]: 6140
% 2.00/0.64  % (8361)Time elapsed: 0.205 s
% 2.00/0.64  % (8361)------------------------------
% 2.00/0.64  % (8361)------------------------------
% 2.00/0.65  % (8402)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.00/0.66  % (8405)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.00/0.66  % (8390)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.00/0.66  % (8405)Refutation not found, incomplete strategy% (8405)------------------------------
% 2.00/0.66  % (8405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.66  % (8405)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.66  
% 2.00/0.67  % (8356)Refutation not found, incomplete strategy% (8356)------------------------------
% 2.00/0.67  % (8356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.67  % (8356)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.67  
% 2.00/0.67  % (8356)Memory used [KB]: 6140
% 2.00/0.67  % (8356)Time elapsed: 0.245 s
% 2.00/0.67  % (8356)------------------------------
% 2.00/0.67  % (8356)------------------------------
% 2.00/0.67  % (8407)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.00/0.67  % (8407)Refutation not found, incomplete strategy% (8407)------------------------------
% 2.00/0.67  % (8407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.67  % (8404)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.00/0.67  % (8359)Refutation found. Thanks to Tanya!
% 2.00/0.67  % SZS status Theorem for theBenchmark
% 2.00/0.67  % SZS output start Proof for theBenchmark
% 2.00/0.67  fof(f2033,plain,(
% 2.00/0.67    $false),
% 2.00/0.67    inference(avatar_sat_refutation,[],[f111,f2021,f2032])).
% 2.00/0.67  % (8413)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.00/0.67  % (8408)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.00/0.68  % (8413)Refutation not found, incomplete strategy% (8413)------------------------------
% 2.00/0.68  % (8413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (8408)Refutation not found, incomplete strategy% (8408)------------------------------
% 2.00/0.68  % (8408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (8408)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (8408)Memory used [KB]: 1663
% 2.00/0.68  % (8408)Time elapsed: 0.106 s
% 2.00/0.68  % (8408)------------------------------
% 2.00/0.68  % (8408)------------------------------
% 2.00/0.68  % (8417)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.00/0.68  % (8355)Refutation not found, incomplete strategy% (8355)------------------------------
% 2.00/0.68  % (8355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (8355)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (8355)Memory used [KB]: 6140
% 2.00/0.68  % (8355)Time elapsed: 0.224 s
% 2.00/0.68  % (8355)------------------------------
% 2.00/0.68  % (8355)------------------------------
% 2.00/0.68  % (8415)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.00/0.68  % (8417)Refutation not found, incomplete strategy% (8417)------------------------------
% 2.00/0.68  % (8417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (8417)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (8417)Memory used [KB]: 10618
% 2.00/0.68  % (8417)Time elapsed: 0.096 s
% 2.00/0.68  % (8417)------------------------------
% 2.00/0.68  % (8417)------------------------------
% 2.00/0.68  % (8405)Memory used [KB]: 10618
% 2.00/0.68  % (8405)Time elapsed: 0.081 s
% 2.00/0.68  % (8405)------------------------------
% 2.00/0.68  % (8405)------------------------------
% 2.00/0.68  % (8407)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (8407)Memory used [KB]: 10618
% 2.00/0.68  % (8407)Time elapsed: 0.086 s
% 2.00/0.68  % (8407)------------------------------
% 2.00/0.68  % (8407)------------------------------
% 2.00/0.68  % (8413)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (8413)Memory used [KB]: 10618
% 2.00/0.68  % (8413)Time elapsed: 0.079 s
% 2.00/0.68  % (8413)------------------------------
% 2.00/0.68  % (8413)------------------------------
% 2.00/0.68  fof(f2032,plain,(
% 2.00/0.68    spl2_4),
% 2.00/0.68    inference(avatar_contradiction_clause,[],[f2031])).
% 2.00/0.68  fof(f2031,plain,(
% 2.00/0.68    $false | spl2_4),
% 2.00/0.68    inference(subsumption_resolution,[],[f109,f181])).
% 2.00/0.68  fof(f181,plain,(
% 2.00/0.68    ( ! [X4,X5] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(k1_setfam_1(k2_enumset1(X4,X4,X4,X5))))) )),
% 2.00/0.68    inference(superposition,[],[f99,f176])).
% 2.00/0.68  fof(f176,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.00/0.68    inference(forward_demodulation,[],[f173,f38])).
% 2.00/0.68  fof(f38,plain,(
% 2.00/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.00/0.68    inference(cnf_transformation,[],[f12])).
% 2.00/0.68  fof(f12,axiom,(
% 2.00/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.00/0.68  fof(f173,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)))) )),
% 2.00/0.68    inference(resolution,[],[f64,f36])).
% 2.00/0.68  fof(f36,plain,(
% 2.00/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.00/0.68    inference(cnf_transformation,[],[f17])).
% 2.00/0.68  fof(f17,axiom,(
% 2.00/0.68    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.00/0.68  fof(f64,plain,(
% 2.00/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 2.00/0.68    inference(definition_unfolding,[],[f48,f59])).
% 2.00/0.68  fof(f59,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.00/0.68    inference(definition_unfolding,[],[f45,f58])).
% 2.00/0.68  fof(f58,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.00/0.68    inference(definition_unfolding,[],[f44,f56])).
% 2.00/0.68  fof(f56,plain,(
% 2.00/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f6])).
% 2.00/0.68  fof(f6,axiom,(
% 2.00/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.00/0.68  fof(f44,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f5])).
% 2.00/0.68  fof(f5,axiom,(
% 2.00/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.00/0.68  fof(f45,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.00/0.68    inference(cnf_transformation,[],[f7])).
% 2.00/0.68  fof(f7,axiom,(
% 2.00/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.00/0.68  fof(f48,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f25])).
% 2.00/0.68  fof(f25,plain,(
% 2.00/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.00/0.68    inference(ennf_transformation,[],[f10])).
% 2.00/0.68  fof(f10,axiom,(
% 2.00/0.68    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 2.00/0.68  fof(f99,plain,(
% 2.00/0.68    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))) )),
% 2.00/0.68    inference(subsumption_resolution,[],[f97,f36])).
% 2.00/0.68  fof(f97,plain,(
% 2.00/0.68    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 2.00/0.68    inference(superposition,[],[f49,f90])).
% 2.00/0.68  fof(f90,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.00/0.68    inference(resolution,[],[f47,f36])).
% 2.00/0.68  fof(f47,plain,(
% 2.00/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f24])).
% 2.00/0.68  fof(f24,plain,(
% 2.00/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.00/0.68    inference(ennf_transformation,[],[f16])).
% 2.00/0.68  fof(f16,axiom,(
% 2.00/0.68    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.00/0.68  fof(f49,plain,(
% 2.00/0.68    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f26])).
% 2.00/0.68  fof(f26,plain,(
% 2.00/0.68    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 2.00/0.68    inference(ennf_transformation,[],[f13])).
% 2.00/0.68  fof(f13,axiom,(
% 2.00/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 2.00/0.68  fof(f109,plain,(
% 2.00/0.68    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | spl2_4),
% 2.00/0.68    inference(avatar_component_clause,[],[f107])).
% 2.00/0.68  fof(f107,plain,(
% 2.00/0.68    spl2_4 <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 2.00/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.00/0.68  fof(f2021,plain,(
% 2.00/0.68    spl2_3),
% 2.00/0.68    inference(avatar_contradiction_clause,[],[f1999])).
% 2.00/0.68  fof(f1999,plain,(
% 2.00/0.68    $false | spl2_3),
% 2.00/0.68    inference(resolution,[],[f1383,f105])).
% 2.00/0.68  fof(f105,plain,(
% 2.00/0.68    ~r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_3),
% 2.00/0.68    inference(avatar_component_clause,[],[f103])).
% 2.00/0.68  fof(f103,plain,(
% 2.00/0.68    spl2_3 <=> r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))),
% 2.00/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.00/0.68  fof(f1383,plain,(
% 2.00/0.68    ( ! [X15,X16] : (r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X15,X15,X15,X16))),k7_relat_1(k6_relat_1(X15),X16))) )),
% 2.00/0.68    inference(forward_demodulation,[],[f1369,f176])).
% 2.00/0.68  fof(f1369,plain,(
% 2.00/0.68    ( ! [X15,X16] : (r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X15,X15,X15,X16))),k7_relat_1(k6_relat_1(X15),k1_setfam_1(k2_enumset1(X15,X15,X15,X16))))) )),
% 2.00/0.68    inference(superposition,[],[f1327,f157])).
% 2.00/0.68  fof(f157,plain,(
% 2.00/0.68    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3)) )),
% 2.00/0.68    inference(resolution,[],[f147,f61])).
% 2.00/0.68  fof(f61,plain,(
% 2.00/0.68    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 2.00/0.68    inference(definition_unfolding,[],[f42,f59])).
% 2.00/0.68  fof(f42,plain,(
% 2.00/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f2])).
% 2.00/0.68  fof(f2,axiom,(
% 2.00/0.68    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.00/0.68  fof(f147,plain,(
% 2.00/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.00/0.68    inference(forward_demodulation,[],[f146,f90])).
% 2.00/0.68  fof(f146,plain,(
% 2.00/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 2.00/0.68    inference(subsumption_resolution,[],[f145,f36])).
% 2.00/0.69  fof(f145,plain,(
% 2.00/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.00/0.69    inference(superposition,[],[f51,f38])).
% 2.00/0.69  fof(f51,plain,(
% 2.00/0.69    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f28])).
% 2.00/0.69  fof(f28,plain,(
% 2.00/0.69    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.00/0.69    inference(flattening,[],[f27])).
% 2.00/0.69  fof(f27,plain,(
% 2.00/0.69    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.00/0.69    inference(ennf_transformation,[],[f14])).
% 2.00/0.69  fof(f14,axiom,(
% 2.00/0.69    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.00/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 2.00/0.69  fof(f1327,plain,(
% 2.00/0.69    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.00/0.69    inference(superposition,[],[f1314,f281])).
% 2.00/0.69  fof(f281,plain,(
% 2.00/0.69    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) )),
% 2.00/0.69    inference(superposition,[],[f152,f177])).
% 2.00/0.69  fof(f177,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 2.00/0.69    inference(superposition,[],[f176,f62])).
% 2.00/0.69  fof(f62,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.00/0.69    inference(definition_unfolding,[],[f43,f58,f58])).
% 2.00/0.69  fof(f43,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f4])).
% 2.00/0.69  fof(f4,axiom,(
% 2.00/0.69    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.00/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.00/0.69  fof(f152,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) )),
% 2.00/0.69    inference(resolution,[],[f66,f36])).
% 2.00/0.69  fof(f66,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.00/0.69    inference(definition_unfolding,[],[f57,f59])).
% 2.00/0.69  fof(f57,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f30])).
% 2.00/0.69  fof(f30,plain,(
% 2.00/0.69    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.00/0.69    inference(ennf_transformation,[],[f9])).
% 2.00/0.69  fof(f9,axiom,(
% 2.00/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.00/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 2.00/0.69  fof(f1314,plain,(
% 2.00/0.69    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.00/0.69    inference(subsumption_resolution,[],[f1303,f934])).
% 2.00/0.69  fof(f934,plain,(
% 2.00/0.69    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.00/0.69    inference(subsumption_resolution,[],[f911,f36])).
% 2.00/0.69  fof(f911,plain,(
% 2.00/0.69    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 2.00/0.69    inference(superposition,[],[f63,f221])).
% 2.00/0.69  fof(f221,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0)))) )),
% 2.00/0.69    inference(forward_demodulation,[],[f218,f90])).
% 2.00/0.69  fof(f218,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))))) )),
% 2.00/0.69    inference(resolution,[],[f130,f36])).
% 2.00/0.69  fof(f130,plain,(
% 2.00/0.69    ( ! [X2,X1] : (~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k5_relat_1(X1,k6_relat_1(X2))))) )),
% 2.00/0.69    inference(forward_demodulation,[],[f124,f62])).
% 2.00/0.69  fof(f124,plain,(
% 2.00/0.69    ( ! [X2,X1] : (k5_relat_1(X1,k6_relat_1(X2)) = k1_setfam_1(k2_enumset1(k5_relat_1(X1,k6_relat_1(X2)),k5_relat_1(X1,k6_relat_1(X2)),k5_relat_1(X1,k6_relat_1(X2)),X1)) | ~v1_relat_1(X1)) )),
% 2.00/0.69    inference(resolution,[],[f65,f49])).
% 2.00/0.69  fof(f65,plain,(
% 2.00/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0) )),
% 2.00/0.69    inference(definition_unfolding,[],[f52,f59])).
% 2.00/0.69  fof(f52,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f29])).
% 2.00/0.69  fof(f29,plain,(
% 2.00/0.69    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.00/0.69    inference(ennf_transformation,[],[f3])).
% 2.00/0.69  fof(f3,axiom,(
% 2.00/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.00/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.00/0.69  fof(f63,plain,(
% 2.00/0.69    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 2.00/0.69    inference(definition_unfolding,[],[f46,f59])).
% 2.00/0.69  fof(f46,plain,(
% 2.00/0.69    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f23])).
% 2.00/0.69  fof(f23,plain,(
% 2.00/0.69    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.00/0.69    inference(ennf_transformation,[],[f8])).
% 2.00/0.69  fof(f8,axiom,(
% 2.00/0.69    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.00/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.00/0.69  fof(f1303,plain,(
% 2.00/0.69    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.00/0.69    inference(superposition,[],[f49,f1162])).
% 2.00/0.69  fof(f1162,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 2.00/0.69    inference(backward_demodulation,[],[f722,f939])).
% 2.00/0.69  fof(f939,plain,(
% 2.00/0.69    ( ! [X6,X8,X7] : (k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) = k5_relat_1(k6_relat_1(X8),k7_relat_1(k6_relat_1(X6),X7))) )),
% 2.00/0.69    inference(resolution,[],[f934,f47])).
% 2.00/0.69  fof(f722,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 2.00/0.69    inference(forward_demodulation,[],[f719,f90])).
% 2.00/0.69  fof(f719,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.00/0.69    inference(resolution,[],[f324,f36])).
% 2.00/0.69  fof(f324,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.00/0.69    inference(forward_demodulation,[],[f321,f90])).
% 2.00/0.69  fof(f321,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.00/0.69    inference(resolution,[],[f168,f36])).
% 2.00/0.69  fof(f168,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.00/0.69    inference(resolution,[],[f41,f36])).
% 2.00/0.69  fof(f41,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f22])).
% 2.00/0.69  fof(f22,plain,(
% 2.00/0.69    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.00/0.69    inference(ennf_transformation,[],[f11])).
% 2.00/0.69  fof(f11,axiom,(
% 2.00/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.00/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.00/0.69  fof(f111,plain,(
% 2.00/0.69    ~spl2_4 | ~spl2_3),
% 2.00/0.69    inference(avatar_split_clause,[],[f101,f103,f107])).
% 2.00/0.69  fof(f101,plain,(
% 2.00/0.69    ~r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 2.00/0.69    inference(extensionality_resolution,[],[f55,f93])).
% 2.00/0.69  fof(f93,plain,(
% 2.00/0.69    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.00/0.69    inference(backward_demodulation,[],[f60,f90])).
% 2.00/0.69  fof(f60,plain,(
% 2.00/0.69    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 2.00/0.69    inference(definition_unfolding,[],[f35,f59])).
% 2.00/0.69  fof(f35,plain,(
% 2.00/0.69    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.00/0.69    inference(cnf_transformation,[],[f32])).
% 2.00/0.69  fof(f32,plain,(
% 2.00/0.69    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.00/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 2.00/0.69  fof(f31,plain,(
% 2.00/0.69    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.00/0.69    introduced(choice_axiom,[])).
% 2.00/0.69  fof(f20,plain,(
% 2.00/0.69    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.00/0.69    inference(ennf_transformation,[],[f19])).
% 2.00/0.69  fof(f19,negated_conjecture,(
% 2.00/0.69    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.00/0.69    inference(negated_conjecture,[],[f18])).
% 2.00/0.69  fof(f18,conjecture,(
% 2.00/0.69    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.00/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.00/0.69  fof(f55,plain,(
% 2.00/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f34])).
% 2.00/0.69  fof(f34,plain,(
% 2.00/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.00/0.69    inference(flattening,[],[f33])).
% 2.00/0.69  fof(f33,plain,(
% 2.00/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.00/0.69    inference(nnf_transformation,[],[f1])).
% 2.00/0.69  fof(f1,axiom,(
% 2.00/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.00/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.00/0.69  % SZS output end Proof for theBenchmark
% 2.00/0.69  % (8359)------------------------------
% 2.00/0.69  % (8359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.69  % (8359)Termination reason: Refutation
% 2.00/0.69  
% 2.00/0.69  % (8359)Memory used [KB]: 12665
% 2.00/0.69  % (8359)Time elapsed: 0.245 s
% 2.00/0.69  % (8359)------------------------------
% 2.00/0.69  % (8359)------------------------------
% 2.00/0.69  % (8352)Success in time 0.301 s
%------------------------------------------------------------------------------
