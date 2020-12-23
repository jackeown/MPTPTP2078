%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 213 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(subsumption_resolution,[],[f68,f25])).

fof(f25,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( r1_xboole_0(sK0,sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK2,sK0)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17])).

% (12676)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK0,sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK2,sK0)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f68,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f67,f57])).

fof(f57,plain,(
    r1_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f49,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f47,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f45,f26])).

fof(f26,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_xboole_0(X0,sK1) ) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f65,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f65,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(forward_demodulation,[],[f63,f30])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f63,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k4_xboole_0(X2,k1_xboole_0))
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(superposition,[],[f39,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f38,f30])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:13:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (12678)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (12687)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (12687)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (12684)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f68,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ~v1_xboole_0(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17])).
% 0.20/0.46  % (12676)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    v1_xboole_0(sK2)),
% 0.20/0.46    inference(resolution,[],[f67,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    r1_xboole_0(sK2,sK2)),
% 0.20/0.46    inference(resolution,[],[f50,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    r1_tarski(sK2,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_xboole_0(X0,sK2)) )),
% 0.20/0.46    inference(resolution,[],[f49,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    r1_xboole_0(sK1,sK2)),
% 0.20/0.46    inference(resolution,[],[f47,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    r1_xboole_0(sK2,sK1)),
% 0.20/0.46    inference(resolution,[],[f45,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    r1_tarski(sK2,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_xboole_0(X0,sK1)) )),
% 0.20/0.46    inference(resolution,[],[f37,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_xboole_0(X0,X0) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(resolution,[],[f65,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.46    inference(rectify,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.46    inference(nnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f63,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(X2,k1_xboole_0)) | ~r1_xboole_0(X2,X2)) )),
% 0.20/0.46    inference(superposition,[],[f39,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(backward_demodulation,[],[f38,f30])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f29,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f35,f33])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (12687)------------------------------
% 0.20/0.46  % (12687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12687)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (12687)Memory used [KB]: 1663
% 0.20/0.46  % (12687)Time elapsed: 0.058 s
% 0.20/0.46  % (12687)------------------------------
% 0.20/0.46  % (12687)------------------------------
% 0.20/0.46  % (12672)Success in time 0.101 s
%------------------------------------------------------------------------------
