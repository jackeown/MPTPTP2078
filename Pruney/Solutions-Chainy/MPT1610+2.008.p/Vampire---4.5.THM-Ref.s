%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  64 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 111 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f31,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(subsumption_resolution,[],[f63,f48])).

fof(f48,plain,(
    ! [X1] : ~ v1_xboole_0(k9_setfam_1(X1)) ),
    inference(resolution,[],[f46,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f46,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(resolution,[],[f45,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k9_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f18])).

fof(f18,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f17,f38])).

fof(f38,plain,(
    k1_xboole_0 = np__0 ),
    inference(resolution,[],[f21,f17])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f17,plain,(
    v1_xboole_0(np__0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(np__0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc0_boole)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(k9_setfam_1(X0))
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(resolution,[],[f20,f46])).

fof(f20,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f31,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f16,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (3495)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3512)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (3489)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (3491)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (3509)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (3512)Refutation not found, incomplete strategy% (3512)------------------------------
% 0.21/0.53  % (3512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3512)Memory used [KB]: 1663
% 0.21/0.53  % (3512)Time elapsed: 0.085 s
% 0.21/0.53  % (3512)------------------------------
% 0.21/0.53  % (3512)------------------------------
% 0.21/0.53  % (3491)Refutation not found, incomplete strategy% (3491)------------------------------
% 0.21/0.53  % (3491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3491)Memory used [KB]: 10618
% 0.21/0.53  % (3491)Time elapsed: 0.123 s
% 0.21/0.53  % (3491)------------------------------
% 0.21/0.53  % (3491)------------------------------
% 0.21/0.53  % (3504)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3511)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (3509)Refutation not found, incomplete strategy% (3509)------------------------------
% 0.21/0.53  % (3509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3509)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3509)Memory used [KB]: 10618
% 0.21/0.53  % (3509)Time elapsed: 0.126 s
% 0.21/0.53  % (3509)------------------------------
% 0.21/0.53  % (3509)------------------------------
% 0.21/0.53  % (3492)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (3496)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (3493)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (3495)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0),
% 0.21/0.53    inference(superposition,[],[f31,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f63,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_xboole_0(k9_setfam_1(X1))) )),
% 0.21/0.53    inference(resolution,[],[f46,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(k1_xboole_0,k9_setfam_1(X0))) )),
% 0.21/0.53    inference(resolution,[],[f45,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k9_setfam_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k9_setfam_1(X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f27,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f43,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f17,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    k1_xboole_0 = np__0),
% 0.21/0.53    inference(resolution,[],[f21,f17])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    v1_xboole_0(np__0)),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    v1_xboole_0(np__0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc0_boole)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f25,f23])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(k9_setfam_1(X0)) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.21/0.53    inference(resolution,[],[f20,f46])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.21/0.53    inference(definition_unfolding,[],[f16,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (3495)------------------------------
% 0.21/0.53  % (3495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3495)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (3495)Memory used [KB]: 6140
% 0.21/0.53  % (3495)Time elapsed: 0.129 s
% 0.21/0.53  % (3495)------------------------------
% 0.21/0.53  % (3495)------------------------------
% 0.21/0.53  % (3488)Success in time 0.172 s
%------------------------------------------------------------------------------
