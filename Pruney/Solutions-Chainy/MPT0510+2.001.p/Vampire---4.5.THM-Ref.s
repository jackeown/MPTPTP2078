%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:42 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 361 expanded)
%              Number of leaves         :    7 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :   77 ( 529 expanded)
%              Number of equality atoms :   49 ( 355 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1755,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1690,f286])).

fof(f286,plain,(
    ! [X2,X3] : k7_relat_1(sK2,k1_setfam_1(k2_tarski(X2,X3))) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(superposition,[],[f221,f220])).

fof(f220,plain,(
    ! [X2,X3] : k1_setfam_1(k2_tarski(k7_relat_1(sK2,X2),k2_zfmisc_1(X3,k2_relat_1(sK2)))) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(forward_demodulation,[],[f209,f44])).

fof(f44,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k1_setfam_1(k2_tarski(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f27,f11])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f209,plain,(
    ! [X2,X3] : k1_setfam_1(k2_tarski(k7_relat_1(sK2,X2),k2_zfmisc_1(X3,k2_relat_1(sK2)))) = k1_setfam_1(k2_tarski(sK2,k2_zfmisc_1(k1_setfam_1(k2_tarski(X2,X3)),k2_relat_1(sK2)))) ),
    inference(superposition,[],[f49,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_setfam_1(k2_tarski(X0,X1)),X2) = k1_setfam_1(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f17,f14,f14])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f49,plain,(
    ! [X6,X7] : k1_setfam_1(k2_tarski(sK2,k1_setfam_1(k2_tarski(k2_zfmisc_1(X6,k2_relat_1(sK2)),X7)))) = k1_setfam_1(k2_tarski(k7_relat_1(sK2,X6),X7)) ),
    inference(superposition,[],[f28,f44])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(definition_unfolding,[],[f16,f14,f14,f14,f14])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f221,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(k7_relat_1(sK2,X1),k2_zfmisc_1(X0,k2_relat_1(sK2)))) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(backward_demodulation,[],[f155,f220])).

fof(f155,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(k7_relat_1(sK2,X0),k2_zfmisc_1(X1,k2_relat_1(sK2)))) = k1_setfam_1(k2_tarski(k7_relat_1(sK2,X1),k2_zfmisc_1(X0,k2_relat_1(sK2)))) ),
    inference(superposition,[],[f122,f49])).

fof(f122,plain,(
    ! [X2,X3] : k1_setfam_1(k2_tarski(k7_relat_1(sK2,X2),X3)) = k1_setfam_1(k2_tarski(sK2,k1_setfam_1(k2_tarski(X3,k2_zfmisc_1(X2,k2_relat_1(sK2)))))) ),
    inference(superposition,[],[f49,f26])).

fof(f26,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1690,plain,(
    k7_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) != k7_relat_1(sK2,k1_setfam_1(k2_tarski(sK1,sK0))) ),
    inference(superposition,[],[f25,f1634])).

fof(f1634,plain,(
    ! [X24,X25] : k7_relat_1(sK2,k1_setfam_1(k2_tarski(X24,X25))) = k1_setfam_1(k2_tarski(k7_relat_1(sK2,X25),k7_relat_1(sK2,X24))) ),
    inference(backward_demodulation,[],[f232,f1632])).

fof(f1632,plain,(
    ! [X36] : k7_relat_1(sK2,X36) = k1_setfam_1(k2_tarski(sK2,k7_relat_1(sK2,X36))) ),
    inference(forward_demodulation,[],[f1603,f1381])).

fof(f1381,plain,(
    ! [X5] : k1_setfam_1(k2_tarski(X5,X5)) = X5 ),
    inference(duplicate_literal_removal,[],[f1376])).

fof(f1376,plain,(
    ! [X5] :
      ( k1_setfam_1(k2_tarski(X5,X5)) = X5
      | k1_setfam_1(k2_tarski(X5,X5)) = X5 ) ),
    inference(resolution,[],[f1370,f535])).

fof(f535,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X1 ) ),
    inference(factoring,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f21,f14])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1370,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k2_tarski(X10,X11)) = X11 ) ),
    inference(subsumption_resolution,[],[f1367,f34])).

fof(f1367,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X11)
      | ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k2_tarski(X10,X11)) = X11 ) ),
    inference(duplicate_literal_removal,[],[f1362])).

fof(f1362,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X11)
      | ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k2_tarski(X10,X11)) = X11
      | k1_setfam_1(k2_tarski(X10,X11)) = X11 ) ),
    inference(resolution,[],[f36,f535])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f19,f14])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1603,plain,(
    ! [X36] : k1_setfam_1(k2_tarski(k7_relat_1(sK2,X36),k7_relat_1(sK2,X36))) = k1_setfam_1(k2_tarski(sK2,k7_relat_1(sK2,X36))) ),
    inference(superposition,[],[f122,f1575])).

fof(f1575,plain,(
    ! [X73] : k7_relat_1(sK2,X73) = k1_setfam_1(k2_tarski(k7_relat_1(sK2,X73),k2_zfmisc_1(X73,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f1522,f44])).

fof(f1522,plain,(
    ! [X73] : k1_setfam_1(k2_tarski(k7_relat_1(sK2,X73),k2_zfmisc_1(X73,k2_relat_1(sK2)))) = k1_setfam_1(k2_tarski(sK2,k2_zfmisc_1(X73,k2_relat_1(sK2)))) ),
    inference(superposition,[],[f122,f1381])).

fof(f232,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(k7_relat_1(sK2,X25),k7_relat_1(sK2,X24))) = k1_setfam_1(k2_tarski(sK2,k7_relat_1(sK2,k1_setfam_1(k2_tarski(X24,X25))))) ),
    inference(superposition,[],[f122,f220])).

fof(f25,plain,(
    k7_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) != k1_setfam_1(k2_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) ),
    inference(definition_unfolding,[],[f12,f14,f14])).

fof(f12,plain,(
    k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (9353)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (9361)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (9361)Refutation not found, incomplete strategy% (9361)------------------------------
% 0.21/0.50  % (9361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9371)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (9361)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9361)Memory used [KB]: 10618
% 0.21/0.51  % (9361)Time elapsed: 0.095 s
% 0.21/0.51  % (9361)------------------------------
% 0.21/0.51  % (9361)------------------------------
% 0.21/0.51  % (9375)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (9352)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (9352)Refutation not found, incomplete strategy% (9352)------------------------------
% 0.21/0.51  % (9352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9380)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (9356)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (9357)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (9362)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (9363)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (9372)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (9367)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (9359)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (9365)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (9367)Refutation not found, incomplete strategy% (9367)------------------------------
% 0.21/0.53  % (9367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9367)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9367)Memory used [KB]: 6140
% 0.21/0.53  % (9367)Time elapsed: 0.002 s
% 0.21/0.53  % (9367)------------------------------
% 0.21/0.53  % (9367)------------------------------
% 0.21/0.53  % (9360)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (9352)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9352)Memory used [KB]: 1663
% 0.21/0.53  % (9352)Time elapsed: 0.109 s
% 0.21/0.53  % (9352)------------------------------
% 0.21/0.53  % (9352)------------------------------
% 0.21/0.53  % (9368)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (9364)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (9362)Refutation not found, incomplete strategy% (9362)------------------------------
% 0.21/0.53  % (9362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9362)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9362)Memory used [KB]: 10618
% 0.21/0.53  % (9362)Time elapsed: 0.127 s
% 0.21/0.53  % (9362)------------------------------
% 0.21/0.53  % (9362)------------------------------
% 0.21/0.53  % (9378)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (9354)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (9370)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (9355)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (9381)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (9373)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (9369)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (9376)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (9358)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (9379)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (9377)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (9369)Refutation not found, incomplete strategy% (9369)------------------------------
% 0.21/0.55  % (9369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9369)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9369)Memory used [KB]: 10618
% 0.21/0.55  % (9369)Time elapsed: 0.154 s
% 0.21/0.55  % (9369)------------------------------
% 0.21/0.55  % (9369)------------------------------
% 0.21/0.57  % (9374)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (9366)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (9374)Refutation not found, incomplete strategy% (9374)------------------------------
% 0.21/0.57  % (9374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (9374)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (9374)Memory used [KB]: 10618
% 0.21/0.59  % (9374)Time elapsed: 0.149 s
% 0.21/0.59  % (9374)------------------------------
% 0.21/0.59  % (9374)------------------------------
% 2.20/0.65  % (9385)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.20/0.65  % (9385)Refutation not found, incomplete strategy% (9385)------------------------------
% 2.20/0.65  % (9385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.65  % (9385)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.65  
% 2.20/0.65  % (9385)Memory used [KB]: 6140
% 2.20/0.65  % (9385)Time elapsed: 0.093 s
% 2.20/0.65  % (9385)------------------------------
% 2.20/0.65  % (9385)------------------------------
% 2.20/0.69  % (9386)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.20/0.69  % (9388)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.20/0.70  % (9387)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.20/0.71  % (9390)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.20/0.72  % (9358)Refutation found. Thanks to Tanya!
% 2.20/0.72  % SZS status Theorem for theBenchmark
% 2.20/0.72  % SZS output start Proof for theBenchmark
% 2.20/0.72  fof(f1755,plain,(
% 2.20/0.72    $false),
% 2.20/0.72    inference(subsumption_resolution,[],[f1690,f286])).
% 2.20/0.72  fof(f286,plain,(
% 2.20/0.72    ( ! [X2,X3] : (k7_relat_1(sK2,k1_setfam_1(k2_tarski(X2,X3))) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X3,X2)))) )),
% 2.20/0.72    inference(superposition,[],[f221,f220])).
% 2.20/0.72  fof(f220,plain,(
% 2.20/0.72    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(k7_relat_1(sK2,X2),k2_zfmisc_1(X3,k2_relat_1(sK2)))) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X2,X3)))) )),
% 2.20/0.72    inference(forward_demodulation,[],[f209,f44])).
% 2.20/0.72  fof(f44,plain,(
% 2.20/0.72    ( ! [X0] : (k7_relat_1(sK2,X0) = k1_setfam_1(k2_tarski(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2))))) )),
% 2.20/0.72    inference(resolution,[],[f27,f11])).
% 2.20/0.72  fof(f11,plain,(
% 2.20/0.72    v1_relat_1(sK2)),
% 2.20/0.72    inference(cnf_transformation,[],[f9])).
% 2.20/0.72  fof(f9,plain,(
% 2.20/0.72    ? [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 2.20/0.72    inference(ennf_transformation,[],[f8])).
% 2.20/0.72  fof(f8,negated_conjecture,(
% 2.20/0.72    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 2.20/0.72    inference(negated_conjecture,[],[f7])).
% 2.20/0.72  fof(f7,conjecture,(
% 2.20/0.72    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).
% 2.20/0.72  fof(f27,plain,(
% 2.20/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))) )),
% 2.20/0.72    inference(definition_unfolding,[],[f15,f14])).
% 2.20/0.72  fof(f14,plain,(
% 2.20/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.20/0.72    inference(cnf_transformation,[],[f5])).
% 2.20/0.72  fof(f5,axiom,(
% 2.20/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.20/0.72  fof(f15,plain,(
% 2.20/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 2.20/0.72    inference(cnf_transformation,[],[f10])).
% 2.20/0.72  fof(f10,plain,(
% 2.20/0.72    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.20/0.72    inference(ennf_transformation,[],[f6])).
% 2.20/0.72  fof(f6,axiom,(
% 2.20/0.72    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 2.73/0.72  fof(f209,plain,(
% 2.73/0.72    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(k7_relat_1(sK2,X2),k2_zfmisc_1(X3,k2_relat_1(sK2)))) = k1_setfam_1(k2_tarski(sK2,k2_zfmisc_1(k1_setfam_1(k2_tarski(X2,X3)),k2_relat_1(sK2))))) )),
% 2.73/0.72    inference(superposition,[],[f49,f30])).
% 2.73/0.72  fof(f30,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_setfam_1(k2_tarski(X0,X1)),X2) = k1_setfam_1(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 2.73/0.72    inference(definition_unfolding,[],[f17,f14,f14])).
% 2.73/0.72  fof(f17,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.73/0.72    inference(cnf_transformation,[],[f4])).
% 2.73/0.72  fof(f4,axiom,(
% 2.73/0.72    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 2.73/0.72  fof(f49,plain,(
% 2.73/0.72    ( ! [X6,X7] : (k1_setfam_1(k2_tarski(sK2,k1_setfam_1(k2_tarski(k2_zfmisc_1(X6,k2_relat_1(sK2)),X7)))) = k1_setfam_1(k2_tarski(k7_relat_1(sK2,X6),X7))) )),
% 2.73/0.72    inference(superposition,[],[f28,f44])).
% 2.73/0.72  fof(f28,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))))) )),
% 2.73/0.72    inference(definition_unfolding,[],[f16,f14,f14,f14,f14])).
% 2.73/0.72  fof(f16,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.73/0.72    inference(cnf_transformation,[],[f3])).
% 2.73/0.72  fof(f3,axiom,(
% 2.73/0.72    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.73/0.72  fof(f221,plain,(
% 2.73/0.72    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k7_relat_1(sK2,X1),k2_zfmisc_1(X0,k2_relat_1(sK2)))) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.73/0.72    inference(backward_demodulation,[],[f155,f220])).
% 2.73/0.72  fof(f155,plain,(
% 2.73/0.72    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k7_relat_1(sK2,X0),k2_zfmisc_1(X1,k2_relat_1(sK2)))) = k1_setfam_1(k2_tarski(k7_relat_1(sK2,X1),k2_zfmisc_1(X0,k2_relat_1(sK2))))) )),
% 2.73/0.72    inference(superposition,[],[f122,f49])).
% 2.73/0.72  fof(f122,plain,(
% 2.73/0.72    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(k7_relat_1(sK2,X2),X3)) = k1_setfam_1(k2_tarski(sK2,k1_setfam_1(k2_tarski(X3,k2_zfmisc_1(X2,k2_relat_1(sK2))))))) )),
% 2.73/0.72    inference(superposition,[],[f49,f26])).
% 2.73/0.72  fof(f26,plain,(
% 2.73/0.72    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 2.73/0.72    inference(definition_unfolding,[],[f13,f14,f14])).
% 2.73/0.72  fof(f13,plain,(
% 2.73/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f1])).
% 2.73/0.72  fof(f1,axiom,(
% 2.73/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.73/0.72  fof(f1690,plain,(
% 2.73/0.72    k7_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) != k7_relat_1(sK2,k1_setfam_1(k2_tarski(sK1,sK0)))),
% 2.73/0.72    inference(superposition,[],[f25,f1634])).
% 2.73/0.72  fof(f1634,plain,(
% 2.73/0.72    ( ! [X24,X25] : (k7_relat_1(sK2,k1_setfam_1(k2_tarski(X24,X25))) = k1_setfam_1(k2_tarski(k7_relat_1(sK2,X25),k7_relat_1(sK2,X24)))) )),
% 2.73/0.72    inference(backward_demodulation,[],[f232,f1632])).
% 2.73/0.72  fof(f1632,plain,(
% 2.73/0.72    ( ! [X36] : (k7_relat_1(sK2,X36) = k1_setfam_1(k2_tarski(sK2,k7_relat_1(sK2,X36)))) )),
% 2.73/0.72    inference(forward_demodulation,[],[f1603,f1381])).
% 2.73/0.72  fof(f1381,plain,(
% 2.73/0.72    ( ! [X5] : (k1_setfam_1(k2_tarski(X5,X5)) = X5) )),
% 2.73/0.72    inference(duplicate_literal_removal,[],[f1376])).
% 2.73/0.72  fof(f1376,plain,(
% 2.73/0.72    ( ! [X5] : (k1_setfam_1(k2_tarski(X5,X5)) = X5 | k1_setfam_1(k2_tarski(X5,X5)) = X5) )),
% 2.73/0.72    inference(resolution,[],[f1370,f535])).
% 2.73/0.72  fof(f535,plain,(
% 2.73/0.72    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X0,X1)) = X1) )),
% 2.73/0.72    inference(factoring,[],[f34])).
% 2.73/0.72  fof(f34,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 2.73/0.72    inference(definition_unfolding,[],[f21,f14])).
% 2.73/0.72  fof(f21,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.73/0.72    inference(cnf_transformation,[],[f2])).
% 2.73/0.72  fof(f2,axiom,(
% 2.73/0.72    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.73/0.72  fof(f1370,plain,(
% 2.73/0.72    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k2_tarski(X10,X11)) = X11) )),
% 2.73/0.72    inference(subsumption_resolution,[],[f1367,f34])).
% 2.73/0.72  fof(f1367,plain,(
% 2.73/0.72    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X11) | ~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k2_tarski(X10,X11)) = X11) )),
% 2.73/0.72    inference(duplicate_literal_removal,[],[f1362])).
% 2.73/0.72  fof(f1362,plain,(
% 2.73/0.72    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X11) | ~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k2_tarski(X10,X11)) = X11 | k1_setfam_1(k2_tarski(X10,X11)) = X11) )),
% 2.73/0.72    inference(resolution,[],[f36,f535])).
% 2.73/0.72  fof(f36,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 2.73/0.72    inference(definition_unfolding,[],[f19,f14])).
% 2.73/0.72  fof(f19,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.73/0.72    inference(cnf_transformation,[],[f2])).
% 2.73/0.72  fof(f1603,plain,(
% 2.73/0.72    ( ! [X36] : (k1_setfam_1(k2_tarski(k7_relat_1(sK2,X36),k7_relat_1(sK2,X36))) = k1_setfam_1(k2_tarski(sK2,k7_relat_1(sK2,X36)))) )),
% 2.73/0.72    inference(superposition,[],[f122,f1575])).
% 2.73/0.72  fof(f1575,plain,(
% 2.73/0.72    ( ! [X73] : (k7_relat_1(sK2,X73) = k1_setfam_1(k2_tarski(k7_relat_1(sK2,X73),k2_zfmisc_1(X73,k2_relat_1(sK2))))) )),
% 2.73/0.72    inference(forward_demodulation,[],[f1522,f44])).
% 2.73/0.72  fof(f1522,plain,(
% 2.73/0.72    ( ! [X73] : (k1_setfam_1(k2_tarski(k7_relat_1(sK2,X73),k2_zfmisc_1(X73,k2_relat_1(sK2)))) = k1_setfam_1(k2_tarski(sK2,k2_zfmisc_1(X73,k2_relat_1(sK2))))) )),
% 2.73/0.72    inference(superposition,[],[f122,f1381])).
% 2.73/0.72  fof(f232,plain,(
% 2.73/0.72    ( ! [X24,X25] : (k1_setfam_1(k2_tarski(k7_relat_1(sK2,X25),k7_relat_1(sK2,X24))) = k1_setfam_1(k2_tarski(sK2,k7_relat_1(sK2,k1_setfam_1(k2_tarski(X24,X25)))))) )),
% 2.73/0.72    inference(superposition,[],[f122,f220])).
% 2.73/0.72  fof(f25,plain,(
% 2.73/0.72    k7_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) != k1_setfam_1(k2_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),
% 2.73/0.72    inference(definition_unfolding,[],[f12,f14,f14])).
% 2.73/0.72  fof(f12,plain,(
% 2.73/0.72    k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),
% 2.73/0.72    inference(cnf_transformation,[],[f9])).
% 2.73/0.72  % SZS output end Proof for theBenchmark
% 2.73/0.72  % (9358)------------------------------
% 2.73/0.72  % (9358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.72  % (9358)Termination reason: Refutation
% 2.73/0.72  
% 2.73/0.72  % (9358)Memory used [KB]: 8827
% 2.73/0.72  % (9358)Time elapsed: 0.297 s
% 2.73/0.72  % (9358)------------------------------
% 2.73/0.72  % (9358)------------------------------
% 2.73/0.72  % (9351)Success in time 0.353 s
%------------------------------------------------------------------------------
