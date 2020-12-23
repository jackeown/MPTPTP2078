%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 188 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  136 ( 551 expanded)
%              Number of equality atoms :   50 ( 194 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(subsumption_resolution,[],[f207,f88])).

fof(f88,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f87,f34])).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f45,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(resolution,[],[f73,f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(resolution,[],[f45,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f207,plain,(
    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f206,f32])).

fof(f32,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f206,plain,(
    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f203,f123])).

fof(f123,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f31,f121])).

fof(f121,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f113,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X0))
      | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f35,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f42,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f113,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f102,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f73,f30])).

fof(f30,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f47,f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f31,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f203,plain,
    ( r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f118,f121])).

fof(f118,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_relat_1(sK1),X0),k1_relat_1(k7_relat_1(sK1,X0)))
      | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f46,f102])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:31:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (30657)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.42  % (30657)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f208,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(subsumption_resolution,[],[f207,f88])).
% 0.22/0.42  fof(f88,plain,(
% 0.22/0.42    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.22/0.42    inference(subsumption_resolution,[],[f87,f34])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.42  fof(f87,plain,(
% 0.22/0.42    ( ! [X2,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.42    inference(superposition,[],[f45,f77])).
% 0.22/0.42  fof(f77,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.22/0.42    inference(resolution,[],[f73,f34])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.42    inference(resolution,[],[f45,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f25])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f41,f39])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f28])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(rectify,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.42  fof(f207,plain,(
% 0.22/0.42    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_xboole_0)),
% 0.22/0.42    inference(forward_demodulation,[],[f206,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,axiom,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.42  fof(f206,plain,(
% 0.22/0.42    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0))),
% 0.22/0.42    inference(subsumption_resolution,[],[f203,f123])).
% 0.22/0.42  fof(f123,plain,(
% 0.22/0.42    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f122])).
% 0.22/0.42  fof(f122,plain,(
% 0.22/0.42    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.42    inference(backward_demodulation,[],[f31,f121])).
% 0.22/0.42  fof(f121,plain,(
% 0.22/0.42    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.42    inference(subsumption_resolution,[],[f113,f58])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X0)) | k1_xboole_0 = k7_relat_1(sK1,X0)) )),
% 0.22/0.42    inference(resolution,[],[f35,f49])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.22/0.42    inference(resolution,[],[f42,f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    v1_relat_1(sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f24])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.42    inference(flattening,[],[f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.42    inference(nnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.42    inference(negated_conjecture,[],[f10])).
% 0.22/0.42  fof(f10,conjecture,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(flattening,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.42  fof(f113,plain,(
% 0.22/0.42    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.42    inference(superposition,[],[f102,f78])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.43    inference(resolution,[],[f73,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 0.22/0.43    inference(resolution,[],[f47,f29])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f43,f39])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f203,plain,(
% 0.22/0.43    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.43    inference(superposition,[],[f118,f121])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK3(k1_relat_1(sK1),X0),k1_relat_1(k7_relat_1(sK1,X0))) | r1_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.22/0.43    inference(superposition,[],[f46,f102])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f40,f39])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f28])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (30657)------------------------------
% 0.22/0.43  % (30657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (30657)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (30657)Memory used [KB]: 1791
% 0.22/0.43  % (30657)Time elapsed: 0.010 s
% 0.22/0.43  % (30657)------------------------------
% 0.22/0.43  % (30657)------------------------------
% 0.22/0.43  % (30643)Success in time 0.06 s
%------------------------------------------------------------------------------
