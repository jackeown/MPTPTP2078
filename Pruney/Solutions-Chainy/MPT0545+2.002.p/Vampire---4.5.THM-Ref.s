%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  22 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  37 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f8])).

fof(f8,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

fof(f16,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f13,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f13,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f9,f12])).

fof(f12,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(resolution,[],[f10,f8])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f9,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (24522)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (24516)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (24524)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (24516)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f16,f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0,X1] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ~v1_relat_1(sK1)),
% 0.21/0.42    inference(resolution,[],[f13,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ~r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 0.21/0.42    inference(superposition,[],[f9,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 0.21/0.42    inference(resolution,[],[f10,f8])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (24516)------------------------------
% 0.21/0.42  % (24516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (24516)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (24516)Memory used [KB]: 10490
% 0.21/0.42  % (24516)Time elapsed: 0.004 s
% 0.21/0.42  % (24516)------------------------------
% 0.21/0.42  % (24516)------------------------------
% 0.21/0.42  % (24515)Success in time 0.063 s
%------------------------------------------------------------------------------
