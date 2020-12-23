%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:29 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 279 expanded)
%              Number of leaves         :   20 (  86 expanded)
%              Depth                    :   17
%              Number of atoms          :  181 ( 427 expanded)
%              Number of equality atoms :   70 ( 200 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f705,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f193,f700])).

fof(f700,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f141,f626])).

fof(f626,plain,(
    ! [X0,X1] : r1_tarski(k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f610,f181])).

fof(f181,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f178,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f178,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) ),
    inference(resolution,[],[f171,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) ) ),
    inference(forward_demodulation,[],[f64,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f57,plain,(
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

% (1649)Refutation not found, incomplete strategy% (1649)------------------------------
% (1649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1649)Termination reason: Refutation not found, incomplete strategy

% (1649)Memory used [KB]: 6140
% (1649)Time elapsed: 0.166 s
% (1649)------------------------------
% (1649)------------------------------
fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

% (1650)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (1630)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (1625)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (1638)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (1650)Refutation not found, incomplete strategy% (1650)------------------------------
% (1650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1650)Termination reason: Refutation not found, incomplete strategy

% (1650)Memory used [KB]: 10618
% (1650)Time elapsed: 0.169 s
% (1650)------------------------------
% (1650)------------------------------
% (1643)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (1651)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (1651)Refutation not found, incomplete strategy% (1651)------------------------------
% (1651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1651)Termination reason: Refutation not found, incomplete strategy

% (1651)Memory used [KB]: 1663
% (1651)Time elapsed: 0.001 s
% (1651)------------------------------
% (1651)------------------------------
% (1638)Refutation not found, incomplete strategy% (1638)------------------------------
% (1638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1631)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f610,plain,(
    ! [X2,X3] : r1_tarski(k6_relat_1(k4_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f583,f100])).

fof(f100,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f93,f69])).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f67,f39])).

fof(f39,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f93,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,(
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

fof(f583,plain,(
    ! [X4,X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(k4_xboole_0(X2,X3)),X4),k7_relat_1(k6_relat_1(X2),X4)) ),
    inference(superposition,[],[f571,f160])).

fof(f160,plain,(
    ! [X6,X5] : k6_relat_1(k4_xboole_0(X5,X6)) = k7_relat_1(k6_relat_1(k4_xboole_0(X5,X6)),X5) ),
    inference(resolution,[],[f153,f148])).

fof(f148,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f129,f144])).

fof(f144,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f63,f62])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f129,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f61,f62])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f97,f93])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f96,f36])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f38])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f571,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(subsumption_resolution,[],[f562,f108])).

fof(f108,plain,(
    ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(subsumption_resolution,[],[f107,f36])).

fof(f107,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f104,f36])).

fof(f104,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X6))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f53,f93])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f562,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(superposition,[],[f50,f504])).

fof(f504,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f503,f93])).

fof(f503,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(forward_demodulation,[],[f499,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f108,f48])).

fof(f499,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f289,f36])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f285,f93])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f154,f36])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f42,f36])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f141,plain,
    ( ~ r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl2_6
  <=> r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f193,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f182,f137])).

fof(f137,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_5
  <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f182,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f106,f181])).

% (1634)Refutation not found, incomplete strategy% (1634)------------------------------
% (1634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f106,plain,(
    ! [X4,X3] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) ),
    inference(subsumption_resolution,[],[f103,f36])).

fof(f103,plain,(
    ! [X4,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f50,f93])).

fof(f143,plain,
    ( ~ spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f133,f135,f139])).

fof(f133,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(extensionality_resolution,[],[f56,f130])).

fof(f130,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f99,f62])).

fof(f99,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f60,f93])).

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

fof(f56,plain,(
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:31:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 1.43/0.56  % (1636)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.43/0.56  % (1628)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.57  % (1645)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.57  % (1636)Refutation not found, incomplete strategy% (1636)------------------------------
% 1.43/0.57  % (1636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (1636)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (1636)Memory used [KB]: 1663
% 1.43/0.57  % (1636)Time elapsed: 0.140 s
% 1.43/0.57  % (1636)------------------------------
% 1.43/0.57  % (1636)------------------------------
% 1.43/0.57  % (1644)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.43/0.58  % (1624)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.43/0.58  % (1629)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.43/0.58  % (1626)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.58  % (1632)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.59  % (1637)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.59  % (1632)Refutation not found, incomplete strategy% (1632)------------------------------
% 1.43/0.59  % (1632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.59  % (1622)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.43/0.59  % (1642)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.59  % (1647)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.59  % (1633)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.59  % (1632)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.59  
% 1.43/0.59  % (1632)Memory used [KB]: 10618
% 1.43/0.59  % (1632)Time elapsed: 0.157 s
% 1.43/0.59  % (1632)------------------------------
% 1.43/0.59  % (1632)------------------------------
% 1.43/0.59  % (1627)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.43/0.59  % (1634)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.59  % (1639)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.43/0.60  % (1649)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.60  % (1648)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.60  % (1628)Refutation found. Thanks to Tanya!
% 1.43/0.60  % SZS status Theorem for theBenchmark
% 1.43/0.60  % SZS output start Proof for theBenchmark
% 1.43/0.60  fof(f705,plain,(
% 1.43/0.60    $false),
% 1.43/0.60    inference(avatar_sat_refutation,[],[f143,f193,f700])).
% 1.43/0.60  fof(f700,plain,(
% 1.43/0.60    spl2_6),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f699])).
% 1.43/0.60  fof(f699,plain,(
% 1.43/0.60    $false | spl2_6),
% 1.43/0.60    inference(subsumption_resolution,[],[f141,f626])).
% 1.43/0.60  fof(f626,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.43/0.60    inference(superposition,[],[f610,f181])).
% 1.43/0.60  fof(f181,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.43/0.60    inference(forward_demodulation,[],[f178,f38])).
% 1.43/0.60  fof(f38,plain,(
% 1.43/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.43/0.60    inference(cnf_transformation,[],[f11])).
% 1.43/0.60  fof(f11,axiom,(
% 1.43/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.43/0.60  fof(f178,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)))) )),
% 1.43/0.60    inference(resolution,[],[f171,f36])).
% 1.43/0.60  fof(f36,plain,(
% 1.43/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.60    inference(cnf_transformation,[],[f17])).
% 1.43/0.60  fof(f17,axiom,(
% 1.43/0.60    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.43/0.60  fof(f171,plain,(
% 1.43/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))) )),
% 1.43/0.60    inference(forward_demodulation,[],[f64,f62])).
% 1.43/0.60  fof(f62,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.43/0.60    inference(definition_unfolding,[],[f46,f59])).
% 1.43/0.60  fof(f59,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.43/0.60    inference(definition_unfolding,[],[f44,f58])).
% 1.43/0.60  fof(f58,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f45,f57])).
% 1.43/0.60  fof(f57,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f6])).
% 1.43/0.60  fof(f6,axiom,(
% 1.43/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.43/0.60  fof(f45,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f5])).
% 1.43/0.60  fof(f5,axiom,(
% 1.43/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.60  fof(f44,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.43/0.60    inference(cnf_transformation,[],[f7])).
% 1.43/0.60  fof(f7,axiom,(
% 1.43/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.43/0.60  % (1649)Refutation not found, incomplete strategy% (1649)------------------------------
% 1.43/0.60  % (1649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  % (1649)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.60  
% 1.43/0.60  % (1649)Memory used [KB]: 6140
% 1.43/0.60  % (1649)Time elapsed: 0.166 s
% 1.43/0.60  % (1649)------------------------------
% 1.43/0.60  % (1649)------------------------------
% 1.43/0.60  fof(f46,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.43/0.60    inference(cnf_transformation,[],[f4])).
% 1.43/0.60  fof(f4,axiom,(
% 1.43/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.43/0.60  % (1650)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.60  % (1630)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.60  % (1625)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.43/0.60  % (1638)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.60  % (1650)Refutation not found, incomplete strategy% (1650)------------------------------
% 1.43/0.60  % (1650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  % (1650)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.60  
% 1.43/0.60  % (1650)Memory used [KB]: 10618
% 1.43/0.60  % (1650)Time elapsed: 0.169 s
% 1.43/0.60  % (1650)------------------------------
% 1.43/0.60  % (1650)------------------------------
% 1.43/0.60  % (1643)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.60  % (1651)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.60  % (1651)Refutation not found, incomplete strategy% (1651)------------------------------
% 1.43/0.60  % (1651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  % (1651)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.60  
% 1.43/0.60  % (1651)Memory used [KB]: 1663
% 1.43/0.60  % (1651)Time elapsed: 0.001 s
% 1.43/0.60  % (1651)------------------------------
% 1.43/0.60  % (1651)------------------------------
% 1.43/0.60  % (1638)Refutation not found, incomplete strategy% (1638)------------------------------
% 1.43/0.60  % (1638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  % (1631)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.60  fof(f64,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f49,f59])).
% 1.43/0.60  fof(f49,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f25])).
% 1.43/0.60  fof(f25,plain,(
% 1.43/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.43/0.60    inference(ennf_transformation,[],[f9])).
% 1.43/0.60  fof(f9,axiom,(
% 1.43/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 1.43/0.60  fof(f610,plain,(
% 1.43/0.60    ( ! [X2,X3] : (r1_tarski(k6_relat_1(k4_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),k4_xboole_0(X2,X3)))) )),
% 1.43/0.60    inference(superposition,[],[f583,f100])).
% 1.43/0.60  fof(f100,plain,(
% 1.43/0.60    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.43/0.60    inference(superposition,[],[f93,f69])).
% 1.43/0.60  fof(f69,plain,(
% 1.43/0.60    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.43/0.60    inference(forward_demodulation,[],[f67,f39])).
% 1.43/0.60  fof(f39,plain,(
% 1.43/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.43/0.60    inference(cnf_transformation,[],[f11])).
% 1.43/0.60  fof(f67,plain,(
% 1.43/0.60    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 1.43/0.60    inference(resolution,[],[f40,f36])).
% 1.43/0.60  fof(f40,plain,(
% 1.43/0.60    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.43/0.60    inference(cnf_transformation,[],[f21])).
% 1.43/0.60  fof(f21,plain,(
% 1.43/0.60    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.43/0.60    inference(ennf_transformation,[],[f15])).
% 1.43/0.60  fof(f15,axiom,(
% 1.43/0.60    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.43/0.60  fof(f93,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.43/0.60    inference(resolution,[],[f48,f36])).
% 1.43/0.60  fof(f48,plain,(
% 1.43/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f24])).
% 1.43/0.60  fof(f24,plain,(
% 1.43/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.43/0.60    inference(ennf_transformation,[],[f16])).
% 1.43/0.60  fof(f16,axiom,(
% 1.43/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.43/0.60  fof(f583,plain,(
% 1.43/0.60    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(k4_xboole_0(X2,X3)),X4),k7_relat_1(k6_relat_1(X2),X4))) )),
% 1.43/0.60    inference(superposition,[],[f571,f160])).
% 1.43/0.60  fof(f160,plain,(
% 1.43/0.60    ( ! [X6,X5] : (k6_relat_1(k4_xboole_0(X5,X6)) = k7_relat_1(k6_relat_1(k4_xboole_0(X5,X6)),X5)) )),
% 1.43/0.60    inference(resolution,[],[f153,f148])).
% 1.43/0.60  fof(f148,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.43/0.60    inference(superposition,[],[f129,f144])).
% 1.43/0.60  fof(f144,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.43/0.60    inference(forward_demodulation,[],[f63,f62])).
% 1.43/0.60  fof(f63,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.43/0.60    inference(definition_unfolding,[],[f47,f59])).
% 1.43/0.60  fof(f47,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f3])).
% 1.43/0.60  fof(f3,axiom,(
% 1.43/0.60    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.43/0.60  fof(f129,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.43/0.60    inference(backward_demodulation,[],[f61,f62])).
% 1.43/0.60  fof(f61,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f43,f59])).
% 1.43/0.60  fof(f43,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f2])).
% 1.43/0.60  fof(f2,axiom,(
% 1.43/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.43/0.60  fof(f153,plain,(
% 1.43/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.43/0.60    inference(forward_demodulation,[],[f97,f93])).
% 1.43/0.60  fof(f97,plain,(
% 1.43/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.43/0.60    inference(subsumption_resolution,[],[f96,f36])).
% 1.43/0.60  fof(f96,plain,(
% 1.43/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.60    inference(superposition,[],[f52,f38])).
% 1.43/0.60  fof(f52,plain,(
% 1.43/0.60    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f28])).
% 1.43/0.60  fof(f28,plain,(
% 1.43/0.60    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.43/0.60    inference(flattening,[],[f27])).
% 1.43/0.60  fof(f27,plain,(
% 1.43/0.60    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.43/0.60    inference(ennf_transformation,[],[f13])).
% 1.43/0.60  fof(f13,axiom,(
% 1.43/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.43/0.60  fof(f571,plain,(
% 1.43/0.60    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.43/0.60    inference(subsumption_resolution,[],[f562,f108])).
% 1.43/0.60  fof(f108,plain,(
% 1.43/0.60    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) )),
% 1.43/0.60    inference(subsumption_resolution,[],[f107,f36])).
% 1.43/0.60  fof(f107,plain,(
% 1.43/0.60    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.43/0.60    inference(subsumption_resolution,[],[f104,f36])).
% 1.43/0.60  fof(f104,plain,(
% 1.43/0.60    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.43/0.60    inference(superposition,[],[f53,f93])).
% 1.43/0.60  fof(f53,plain,(
% 1.43/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f30])).
% 1.43/0.60  fof(f30,plain,(
% 1.43/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.43/0.60    inference(flattening,[],[f29])).
% 1.43/0.60  fof(f29,plain,(
% 1.43/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.43/0.60    inference(ennf_transformation,[],[f8])).
% 1.43/0.60  fof(f8,axiom,(
% 1.43/0.60    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.43/0.60  fof(f562,plain,(
% 1.43/0.60    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.43/0.60    inference(superposition,[],[f50,f504])).
% 1.43/0.60  fof(f504,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 1.43/0.60    inference(forward_demodulation,[],[f503,f93])).
% 1.43/0.60  fof(f503,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) )),
% 1.43/0.60    inference(forward_demodulation,[],[f499,f109])).
% 1.43/0.60  fof(f109,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.43/0.60    inference(resolution,[],[f108,f48])).
% 1.43/0.60  fof(f499,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.43/0.60    inference(resolution,[],[f289,f36])).
% 1.43/0.60  fof(f289,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.43/0.60    inference(forward_demodulation,[],[f285,f93])).
% 1.43/0.60  fof(f285,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.43/0.60    inference(resolution,[],[f154,f36])).
% 1.43/0.60  fof(f154,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.43/0.60    inference(resolution,[],[f42,f36])).
% 1.43/0.60  fof(f42,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f23])).
% 1.43/0.60  fof(f23,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.43/0.60    inference(ennf_transformation,[],[f10])).
% 1.43/0.60  fof(f10,axiom,(
% 1.43/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.43/0.60  fof(f50,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f26])).
% 1.43/0.60  fof(f26,plain,(
% 1.43/0.60    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.43/0.60    inference(ennf_transformation,[],[f12])).
% 1.43/0.60  fof(f12,axiom,(
% 1.43/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.43/0.60  fof(f141,plain,(
% 1.43/0.60    ~r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_6),
% 1.43/0.60    inference(avatar_component_clause,[],[f139])).
% 1.43/0.60  fof(f139,plain,(
% 1.43/0.60    spl2_6 <=> r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.43/0.60  fof(f193,plain,(
% 1.43/0.60    spl2_5),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f185])).
% 1.43/0.60  fof(f185,plain,(
% 1.43/0.60    $false | spl2_5),
% 1.43/0.60    inference(resolution,[],[f182,f137])).
% 1.43/0.60  fof(f137,plain,(
% 1.43/0.60    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_5),
% 1.43/0.60    inference(avatar_component_clause,[],[f135])).
% 1.43/0.60  fof(f135,plain,(
% 1.43/0.60    spl2_5 <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.43/0.60  fof(f182,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 1.43/0.60    inference(superposition,[],[f106,f181])).
% 1.43/0.60  % (1634)Refutation not found, incomplete strategy% (1634)------------------------------
% 1.43/0.60  % (1634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  fof(f106,plain,(
% 1.43/0.60    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))) )),
% 1.43/0.60    inference(subsumption_resolution,[],[f103,f36])).
% 1.43/0.60  fof(f103,plain,(
% 1.43/0.60    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.43/0.60    inference(superposition,[],[f50,f93])).
% 1.43/0.60  fof(f143,plain,(
% 1.43/0.60    ~spl2_6 | ~spl2_5),
% 1.43/0.60    inference(avatar_split_clause,[],[f133,f135,f139])).
% 1.43/0.60  fof(f133,plain,(
% 1.43/0.60    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))),
% 1.43/0.60    inference(extensionality_resolution,[],[f56,f130])).
% 1.43/0.60  fof(f130,plain,(
% 1.43/0.60    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.43/0.60    inference(backward_demodulation,[],[f99,f62])).
% 1.43/0.60  fof(f99,plain,(
% 1.43/0.60    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.43/0.60    inference(backward_demodulation,[],[f60,f93])).
% 1.43/0.60  fof(f60,plain,(
% 1.43/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.43/0.60    inference(definition_unfolding,[],[f35,f59])).
% 1.43/0.60  fof(f35,plain,(
% 1.43/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.43/0.60    inference(cnf_transformation,[],[f32])).
% 1.43/0.60  fof(f32,plain,(
% 1.43/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.43/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 1.43/0.60  fof(f31,plain,(
% 1.43/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.43/0.60    introduced(choice_axiom,[])).
% 1.43/0.60  fof(f20,plain,(
% 1.43/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.43/0.60    inference(ennf_transformation,[],[f19])).
% 1.43/0.60  fof(f19,negated_conjecture,(
% 1.43/0.60    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.43/0.60    inference(negated_conjecture,[],[f18])).
% 1.43/0.60  fof(f18,conjecture,(
% 1.43/0.60    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.43/0.60  fof(f56,plain,(
% 1.43/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f34])).
% 1.43/0.60  fof(f34,plain,(
% 1.43/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.60    inference(flattening,[],[f33])).
% 1.43/0.60  fof(f33,plain,(
% 1.43/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.60    inference(nnf_transformation,[],[f1])).
% 1.43/0.60  fof(f1,axiom,(
% 1.43/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.60  % SZS output end Proof for theBenchmark
% 1.43/0.60  % (1628)------------------------------
% 1.43/0.60  % (1628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  % (1628)Termination reason: Refutation
% 1.43/0.60  
% 1.43/0.60  % (1628)Memory used [KB]: 11257
% 1.43/0.60  % (1628)Time elapsed: 0.145 s
% 1.43/0.60  % (1628)------------------------------
% 1.43/0.60  % (1628)------------------------------
% 1.43/0.60  % (1634)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.60  
% 1.43/0.60  % (1634)Memory used [KB]: 10618
% 1.43/0.60  % (1634)Time elapsed: 0.176 s
% 1.43/0.60  % (1634)------------------------------
% 1.43/0.60  % (1634)------------------------------
% 1.43/0.61  % (1621)Success in time 0.229 s
%------------------------------------------------------------------------------
