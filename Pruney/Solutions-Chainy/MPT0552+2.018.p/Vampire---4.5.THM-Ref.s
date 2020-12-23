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
% DateTime   : Thu Dec  3 12:49:47 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 137 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 216 expanded)
%              Number of equality atoms :   21 (  75 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f197,f210])).

fof(f210,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f20,f41,f60,f111,f122])).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k9_relat_1(X5,X4),k9_relat_1(X5,X3))
      | ~ v1_relat_1(X5)
      | ~ r1_tarski(X4,X3)
      | ~ r1_tarski(X3,X3) ) ),
    inference(superposition,[],[f98,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f48,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

% (20635)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f98,plain,(
    ! [X14,X15,X13] :
      ( r1_tarski(k9_relat_1(X13,X15),k9_relat_1(X13,k2_xboole_0(X14,X15)))
      | ~ v1_relat_1(X13) ) ),
    inference(superposition,[],[f43,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f22,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f111,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f109])).

% (20618)Refutation not found, incomplete strategy% (20618)------------------------------
% (20618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20618)Termination reason: Refutation not found, incomplete strategy

% (20618)Memory used [KB]: 10618
% (20618)Time elapsed: 0.142 s
% (20618)------------------------------
% (20618)------------------------------
fof(f109,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f24,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f197,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f20,f41,f38,f107,f122])).

fof(f107,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f112,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f103,f109,f105])).

fof(f103,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f37,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f37,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f21,f36,f36])).

fof(f21,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (20612)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (20633)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (20611)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (20625)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (20610)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (20607)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (20616)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (20636)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (20621)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (20623)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (20627)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (20628)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (20630)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (20620)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (20619)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (20622)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (20608)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (20609)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (20629)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (20613)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (20615)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (20631)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.53  % (20621)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.54  % (20632)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.54  % (20634)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (20624)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.54  % (20626)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.54  % (20617)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.36/0.54  % (20618)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.54  % (20636)Refutation not found, incomplete strategy% (20636)------------------------------
% 1.36/0.54  % (20636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f211,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f112,f197,f210])).
% 1.36/0.54  fof(f210,plain,(
% 1.36/0.54    spl3_2),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f208])).
% 1.36/0.54  fof(f208,plain,(
% 1.36/0.54    $false | spl3_2),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f20,f41,f60,f111,f122])).
% 1.36/0.54  fof(f122,plain,(
% 1.36/0.54    ( ! [X4,X5,X3] : (r1_tarski(k9_relat_1(X5,X4),k9_relat_1(X5,X3)) | ~v1_relat_1(X5) | ~r1_tarski(X4,X3) | ~r1_tarski(X3,X3)) )),
% 1.36/0.54    inference(superposition,[],[f98,f54])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 1.36/0.54    inference(resolution,[],[f48,f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.36/0.54    inference(flattening,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 1.36/0.54    inference(resolution,[],[f30,f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.54  % (20635)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.54  fof(f98,plain,(
% 1.36/0.54    ( ! [X14,X15,X13] : (r1_tarski(k9_relat_1(X13,X15),k9_relat_1(X13,k2_xboole_0(X14,X15))) | ~v1_relat_1(X13)) )),
% 1.36/0.54    inference(superposition,[],[f43,f32])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.36/0.54    inference(ennf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.36/0.54    inference(superposition,[],[f22,f25])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.36/0.54  fof(f111,plain,(
% 1.36/0.54    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | spl3_2),
% 1.36/0.54    inference(avatar_component_clause,[],[f109])).
% 1.36/0.54  % (20618)Refutation not found, incomplete strategy% (20618)------------------------------
% 1.36/0.54  % (20618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (20618)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (20618)Memory used [KB]: 10618
% 1.36/0.54  % (20618)Time elapsed: 0.142 s
% 1.36/0.54  % (20618)------------------------------
% 1.36/0.54  % (20618)------------------------------
% 1.36/0.54  fof(f109,plain,(
% 1.36/0.54    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0)) )),
% 1.36/0.54    inference(superposition,[],[f38,f39])).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f24,f35,f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f26,f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f9,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f23,f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.36/0.54    inference(definition_unfolding,[],[f27,f35])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,axiom,(
% 1.36/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.54    inference(equality_resolution,[],[f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    v1_relat_1(sK2)),
% 1.36/0.54    inference(cnf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,plain,(
% 1.36/0.54    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 1.36/0.54    inference(ennf_transformation,[],[f13])).
% 1.36/0.54  fof(f13,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.36/0.54    inference(negated_conjecture,[],[f12])).
% 1.36/0.54  fof(f12,conjecture,(
% 1.36/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 1.36/0.54  fof(f197,plain,(
% 1.36/0.54    spl3_1),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f186])).
% 1.36/0.54  fof(f186,plain,(
% 1.36/0.54    $false | spl3_1),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f20,f41,f38,f107,f122])).
% 1.36/0.54  fof(f107,plain,(
% 1.36/0.54    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) | spl3_1),
% 1.36/0.54    inference(avatar_component_clause,[],[f105])).
% 1.36/0.54  fof(f105,plain,(
% 1.36/0.54    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.36/0.54  fof(f112,plain,(
% 1.36/0.54    ~spl3_1 | ~spl3_2),
% 1.36/0.54    inference(avatar_split_clause,[],[f103,f109,f105])).
% 1.36/0.54  fof(f103,plain,(
% 1.36/0.54    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0))),
% 1.36/0.54    inference(resolution,[],[f37,f40])).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f33,f36])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.36/0.54    inference(flattening,[],[f16])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 1.36/0.54    inference(definition_unfolding,[],[f21,f36,f36])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.36/0.54    inference(cnf_transformation,[],[f14])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (20621)------------------------------
% 1.36/0.54  % (20621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (20621)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (20621)Memory used [KB]: 6268
% 1.36/0.54  % (20621)Time elapsed: 0.124 s
% 1.36/0.54  % (20621)------------------------------
% 1.36/0.54  % (20621)------------------------------
% 1.36/0.54  % (20603)Success in time 0.185 s
%------------------------------------------------------------------------------
