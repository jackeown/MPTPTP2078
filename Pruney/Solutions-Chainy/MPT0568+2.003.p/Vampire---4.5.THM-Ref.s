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
% DateTime   : Thu Dec  3 12:50:10 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 (  57 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f14,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f44,f15])).

fof(f15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f42,f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f42,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f21,f16])).

fof(f16,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f36,f15])).

fof(f36,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | X1 = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f26,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f14,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:32:41 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.42/0.56  % (6511)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.56  % (6504)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.56  % (6513)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.56  % (6511)Refutation not found, incomplete strategy% (6511)------------------------------
% 1.42/0.56  % (6511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (6511)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (6511)Memory used [KB]: 10618
% 1.42/0.56  % (6511)Time elapsed: 0.132 s
% 1.42/0.56  % (6511)------------------------------
% 1.42/0.56  % (6511)------------------------------
% 1.42/0.56  % (6513)Refutation not found, incomplete strategy% (6513)------------------------------
% 1.42/0.56  % (6513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (6513)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.57  % (6495)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.42/0.57  % (6513)Memory used [KB]: 1663
% 1.42/0.57  % (6513)Time elapsed: 0.131 s
% 1.42/0.57  % (6513)------------------------------
% 1.42/0.57  % (6513)------------------------------
% 1.42/0.57  % (6495)Refutation found. Thanks to Tanya!
% 1.42/0.57  % SZS status Theorem for theBenchmark
% 1.42/0.57  % SZS output start Proof for theBenchmark
% 1.42/0.57  fof(f51,plain,(
% 1.42/0.57    $false),
% 1.42/0.57    inference(trivial_inequality_removal,[],[f49])).
% 1.42/0.57  fof(f49,plain,(
% 1.42/0.57    k1_xboole_0 != k1_xboole_0),
% 1.42/0.57    inference(superposition,[],[f14,f45])).
% 1.42/0.57  fof(f45,plain,(
% 1.42/0.57    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f44,f15])).
% 1.42/0.57  fof(f15,plain,(
% 1.42/0.57    v1_xboole_0(k1_xboole_0)),
% 1.42/0.57    inference(cnf_transformation,[],[f3])).
% 1.42/0.57  fof(f3,axiom,(
% 1.42/0.57    v1_xboole_0(k1_xboole_0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.42/0.57  fof(f44,plain,(
% 1.42/0.57    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.42/0.57    inference(resolution,[],[f42,f18])).
% 1.42/0.57  fof(f18,plain,(
% 1.42/0.57    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f11])).
% 1.42/0.57  fof(f11,plain,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f5])).
% 1.42/0.57  fof(f5,axiom,(
% 1.42/0.57    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.42/0.57  fof(f42,plain,(
% 1.42/0.57    ( ! [X1] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) )),
% 1.42/0.57    inference(resolution,[],[f39,f31])).
% 1.42/0.57  fof(f31,plain,(
% 1.42/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.42/0.57    inference(superposition,[],[f21,f16])).
% 1.42/0.57  fof(f16,plain,(
% 1.42/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.42/0.57    inference(cnf_transformation,[],[f7])).
% 1.42/0.57  fof(f7,axiom,(
% 1.42/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.42/0.57  fof(f21,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f12])).
% 1.42/0.57  fof(f12,plain,(
% 1.42/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.42/0.57    inference(ennf_transformation,[],[f6])).
% 1.42/0.57  fof(f6,axiom,(
% 1.42/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.42/0.57  fof(f39,plain,(
% 1.42/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.42/0.57    inference(resolution,[],[f36,f15])).
% 1.42/0.57  fof(f36,plain,(
% 1.42/0.57    ( ! [X2,X1] : (~v1_xboole_0(X2) | X1 = X2 | ~r1_tarski(X1,X2)) )),
% 1.42/0.57    inference(resolution,[],[f24,f32])).
% 1.42/0.57  fof(f32,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.42/0.57    inference(resolution,[],[f26,f20])).
% 1.42/0.57  fof(f20,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f1,axiom,(
% 1.42/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.42/0.57  fof(f26,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f13])).
% 1.42/0.57  fof(f13,plain,(
% 1.42/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.42/0.57    inference(ennf_transformation,[],[f2])).
% 1.42/0.57  fof(f2,axiom,(
% 1.42/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.42/0.57  fof(f24,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.42/0.57    inference(cnf_transformation,[],[f4])).
% 1.42/0.57  fof(f4,axiom,(
% 1.42/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.57  fof(f14,plain,(
% 1.42/0.57    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.42/0.57    inference(cnf_transformation,[],[f10])).
% 1.42/0.57  fof(f10,plain,(
% 1.42/0.57    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.42/0.57    inference(ennf_transformation,[],[f9])).
% 1.42/0.57  fof(f9,negated_conjecture,(
% 1.42/0.57    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.42/0.57    inference(negated_conjecture,[],[f8])).
% 1.42/0.57  fof(f8,conjecture,(
% 1.42/0.57    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 1.42/0.57  % SZS output end Proof for theBenchmark
% 1.42/0.57  % (6495)------------------------------
% 1.42/0.57  % (6495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (6495)Termination reason: Refutation
% 1.42/0.57  
% 1.42/0.57  % (6495)Memory used [KB]: 6140
% 1.42/0.57  % (6495)Time elapsed: 0.127 s
% 1.42/0.57  % (6495)------------------------------
% 1.42/0.57  % (6495)------------------------------
% 1.42/0.57  % (6488)Success in time 0.195 s
%------------------------------------------------------------------------------
