%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  61 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 124 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f52,f30])).

fof(f30,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f51,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f44,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f43,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f43,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f51,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f41,f45])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f28,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).

fof(f22,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:02:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (18322)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (18341)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (18333)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (18333)Refutation not found, incomplete strategy% (18333)------------------------------
% 0.22/0.55  % (18333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18333)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18333)Memory used [KB]: 6140
% 0.22/0.55  % (18333)Time elapsed: 0.071 s
% 0.22/0.55  % (18333)------------------------------
% 0.22/0.55  % (18333)------------------------------
% 0.22/0.55  % (18322)Refutation not found, incomplete strategy% (18322)------------------------------
% 0.22/0.55  % (18322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18322)Memory used [KB]: 6140
% 0.22/0.55  % (18322)Time elapsed: 0.132 s
% 0.22/0.55  % (18322)------------------------------
% 0.22/0.55  % (18322)------------------------------
% 0.22/0.56  % (18340)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (18340)Refutation not found, incomplete strategy% (18340)------------------------------
% 0.22/0.56  % (18340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18340)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18340)Memory used [KB]: 10618
% 0.22/0.56  % (18340)Time elapsed: 0.133 s
% 0.22/0.56  % (18340)------------------------------
% 0.22/0.56  % (18340)------------------------------
% 0.22/0.57  % (18325)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (18325)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f28,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f52,f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.57    inference(cnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f51,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(resolution,[],[f46,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.22/0.57    inference(resolution,[],[f45,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    v1_relat_1(k1_xboole_0)),
% 0.22/0.57    inference(resolution,[],[f44,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.22/0.57    inference(unused_predicate_definition_removal,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f43,f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.22/0.57    inference(resolution,[],[f39,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0))) )),
% 0.22/0.57    inference(resolution,[],[f41,f45])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,negated_conjecture,(
% 0.22/0.57    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.57    inference(negated_conjecture,[],[f12])).
% 0.22/0.57  fof(f12,conjecture,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (18325)------------------------------
% 0.22/0.57  % (18325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (18325)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (18325)Memory used [KB]: 6140
% 0.22/0.57  % (18325)Time elapsed: 0.092 s
% 0.22/0.57  % (18325)------------------------------
% 0.22/0.57  % (18325)------------------------------
% 0.22/0.57  % (18317)Success in time 0.202 s
%------------------------------------------------------------------------------
