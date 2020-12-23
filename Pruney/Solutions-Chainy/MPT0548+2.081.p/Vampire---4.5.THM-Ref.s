%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :   61 (  68 expanded)
%              Number of equality atoms :   38 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f46])).

fof(f46,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f17,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f39,f20])).

fof(f20,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f39,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f36,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
      | k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f35,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(global_subsumption,[],[f28,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f25,f19])).

fof(f19,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f28,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f21,f18])).

fof(f18,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f31,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(k1_xboole_0,X2)) = k9_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f23,f28])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f17,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (8993)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.19/0.41  % (8993)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f47,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(trivial_inequality_removal,[],[f46])).
% 0.19/0.41  fof(f46,plain,(
% 0.19/0.41    k1_xboole_0 != k1_xboole_0),
% 0.19/0.41    inference(superposition,[],[f17,f42])).
% 0.19/0.41  fof(f42,plain,(
% 0.19/0.41    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.41    inference(forward_demodulation,[],[f39,f20])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.41  fof(f39,plain,(
% 0.19/0.41    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.41    inference(superposition,[],[f31,f38])).
% 0.19/0.41  fof(f38,plain,(
% 0.19/0.41    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.41    inference(trivial_inequality_removal,[],[f37])).
% 0.19/0.41  fof(f37,plain,(
% 0.19/0.41    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.41    inference(forward_demodulation,[],[f36,f22])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.19/0.41  fof(f36,plain,(
% 0.19/0.41    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.41    inference(resolution,[],[f35,f27])).
% 0.19/0.41  fof(f27,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.41    inference(nnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.41  fof(f35,plain,(
% 0.19/0.41    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.41    inference(global_subsumption,[],[f28,f34])).
% 0.19/0.41  fof(f34,plain,(
% 0.19/0.41    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.19/0.41    inference(superposition,[],[f25,f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f25,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f15])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.41    inference(nnf_transformation,[],[f12])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,axiom,(
% 0.19/0.41    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.19/0.41  fof(f28,plain,(
% 0.19/0.41    v1_relat_1(k1_xboole_0)),
% 0.19/0.41    inference(superposition,[],[f21,f18])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.41    inference(cnf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,axiom,(
% 0.19/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.19/0.41  fof(f31,plain,(
% 0.19/0.41    ( ! [X2] : (k2_relat_1(k7_relat_1(k1_xboole_0,X2)) = k9_relat_1(k1_xboole_0,X2)) )),
% 0.19/0.41    inference(resolution,[],[f23,f28])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.41    inference(ennf_transformation,[],[f9])).
% 0.19/0.41  fof(f9,negated_conjecture,(
% 0.19/0.41    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.41    inference(negated_conjecture,[],[f8])).
% 0.19/0.41  fof(f8,conjecture,(
% 0.19/0.41    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (8993)------------------------------
% 0.19/0.41  % (8993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (8993)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (8993)Memory used [KB]: 6140
% 0.19/0.41  % (8993)Time elapsed: 0.005 s
% 0.19/0.41  % (8993)------------------------------
% 0.19/0.41  % (8993)------------------------------
% 0.19/0.41  % (8994)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.41  % (8986)Success in time 0.062 s
%------------------------------------------------------------------------------
