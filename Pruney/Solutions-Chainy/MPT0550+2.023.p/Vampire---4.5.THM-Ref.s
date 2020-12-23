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
% DateTime   : Thu Dec  3 12:49:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  79 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :   17
%              Number of atoms          :  104 ( 258 expanded)
%              Number of equality atoms :   57 ( 136 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 != X0 ),
    inference(superposition,[],[f73,f24])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 != k1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[],[f63,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f62,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) = k1_xboole_0
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK1,sK0)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k9_relat_1(X1,X0) = k1_xboole_0
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k9_relat_1(X1,X0) = k1_xboole_0
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(inner_rewriting,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = sK0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f57,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f57,plain,(
    sK0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f37,f55])).

fof(f55,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f47,f22])).

fof(f22,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X1] :
      ( k1_xboole_0 != k9_relat_1(sK1,X1)
      | k1_xboole_0 = k7_relat_1(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X2] : v1_relat_1(k7_relat_1(sK1,X2)) ),
    inference(resolution,[],[f19,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X1] :
      ( k1_xboole_0 != k9_relat_1(sK1,X1)
      | k1_xboole_0 = k7_relat_1(sK1,X1)
      | ~ v1_relat_1(k7_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f27,f32])).

fof(f32,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f36,f19])).

fof(f36,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f21,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f21,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (836)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (844)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (825)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (829)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (829)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(equality_resolution,[],[f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != X0) )),
% 0.21/0.48    inference(superposition,[],[f73,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f63,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ~(k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = sK0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(inner_rewriting,[],[f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(X0) = sK0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f57,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    sK0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f37,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.48    inference(superposition,[],[f47,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK1,X1) | k1_xboole_0 = k7_relat_1(sK1,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f46,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2] : (v1_relat_1(k7_relat_1(sK1,X2))) )),
% 0.21/0.48    inference(resolution,[],[f19,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK1,X1) | k1_xboole_0 = k7_relat_1(sK1,X1) | ~v1_relat_1(k7_relat_1(sK1,X1))) )),
% 0.21/0.48    inference(superposition,[],[f27,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X1] : (k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)) )),
% 0.21/0.48    inference(resolution,[],[f19,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f36,f19])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f21,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (829)------------------------------
% 0.21/0.48  % (829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (829)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (829)Memory used [KB]: 1663
% 0.21/0.48  % (829)Time elapsed: 0.081 s
% 0.21/0.48  % (829)------------------------------
% 0.21/0.48  % (829)------------------------------
% 0.21/0.48  % (834)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (832)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (839)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (824)Success in time 0.133 s
%------------------------------------------------------------------------------
