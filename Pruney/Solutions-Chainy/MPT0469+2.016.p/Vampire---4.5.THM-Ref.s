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
% DateTime   : Thu Dec  3 12:47:36 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 121 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  150 ( 326 expanded)
%              Number of equality atoms :   46 (  92 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f148,f106])).

fof(f106,plain,(
    k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f37,f102])).

fof(f102,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f100,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f100,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f74,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f74,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k1_tarski(k4_tarski(X2,sK3(X3,X2)))) != X3
      | ~ r2_hidden(X2,k1_relat_1(X3)) ) ),
    inference(resolution,[],[f61,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f37,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f148,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f136,f102])).

fof(f136,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f67,f129])).

fof(f129,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f128,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f128,plain,(
    v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f127,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f127,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f125,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f125,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f113,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f113,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f108,f38])).

fof(f108,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f69,f102])).

fof(f69,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f46,f68])).

fof(f68,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f65,f38])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f67,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f63,f38])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(resolution,[],[f44,f41])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:08:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (30007)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (29999)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (29999)Refutation not found, incomplete strategy% (29999)------------------------------
% 0.21/0.51  % (29999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29999)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29999)Memory used [KB]: 6140
% 0.21/0.51  % (29999)Time elapsed: 0.057 s
% 0.21/0.51  % (29999)------------------------------
% 0.21/0.51  % (29999)------------------------------
% 0.21/0.51  % (29991)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.52  % (29991)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % (29993)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f149,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(subsumption_resolution,[],[f148,f106])).
% 1.22/0.52  fof(f106,plain,(
% 1.22/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(subsumption_resolution,[],[f37,f102])).
% 1.22/0.52  fof(f102,plain,(
% 1.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(resolution,[],[f100,f47])).
% 1.22/0.52  fof(f47,plain,(
% 1.22/0.52    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f29,plain,(
% 1.22/0.52    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 1.22/0.52  fof(f28,plain,(
% 1.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f27,plain,(
% 1.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.22/0.52    inference(ennf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.22/0.52  fof(f100,plain,(
% 1.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.22/0.52    inference(trivial_inequality_removal,[],[f99])).
% 1.22/0.52  fof(f99,plain,(
% 1.22/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.22/0.52    inference(superposition,[],[f74,f39])).
% 1.22/0.52  fof(f39,plain,(
% 1.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.22/0.52  fof(f74,plain,(
% 1.22/0.52    ( ! [X2,X3] : (k4_xboole_0(X3,k1_tarski(k4_tarski(X2,sK3(X3,X2)))) != X3 | ~r2_hidden(X2,k1_relat_1(X3))) )),
% 1.22/0.52    inference(resolution,[],[f61,f54])).
% 1.22/0.52  fof(f54,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.22/0.52    inference(cnf_transformation,[],[f36])).
% 1.22/0.52  fof(f36,plain,(
% 1.22/0.52    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.22/0.52    inference(nnf_transformation,[],[f12])).
% 1.22/0.52  fof(f12,axiom,(
% 1.22/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.22/0.52  fof(f61,plain,(
% 1.22/0.52    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.22/0.52    inference(equality_resolution,[],[f50])).
% 1.22/0.52  fof(f50,plain,(
% 1.22/0.52    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.22/0.52    inference(cnf_transformation,[],[f35])).
% 1.22/0.52  fof(f35,plain,(
% 1.22/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f34,plain,(
% 1.22/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.22/0.52    inference(rectify,[],[f30])).
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.22/0.52    inference(nnf_transformation,[],[f14])).
% 1.22/0.52  fof(f14,axiom,(
% 1.22/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.22/0.52  fof(f37,plain,(
% 1.22/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(cnf_transformation,[],[f20])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(ennf_transformation,[],[f19])).
% 1.22/0.52  fof(f19,negated_conjecture,(
% 1.22/0.52    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.22/0.52    inference(negated_conjecture,[],[f18])).
% 1.22/0.52  fof(f18,conjecture,(
% 1.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.22/0.52  fof(f148,plain,(
% 1.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(forward_demodulation,[],[f136,f102])).
% 1.22/0.52  fof(f136,plain,(
% 1.22/0.52    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(backward_demodulation,[],[f67,f129])).
% 1.22/0.52  fof(f129,plain,(
% 1.22/0.52    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(resolution,[],[f128,f42])).
% 1.22/0.52  fof(f42,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.22/0.52    inference(cnf_transformation,[],[f22])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.22/0.52  fof(f128,plain,(
% 1.22/0.52    v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.22/0.52    inference(subsumption_resolution,[],[f127,f38])).
% 1.22/0.52  fof(f38,plain,(
% 1.22/0.52    v1_xboole_0(k1_xboole_0)),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    v1_xboole_0(k1_xboole_0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.22/0.52  fof(f127,plain,(
% 1.22/0.52    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 1.22/0.52    inference(resolution,[],[f125,f41])).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f21])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f13])).
% 1.22/0.52  fof(f13,axiom,(
% 1.22/0.52    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.22/0.52  fof(f125,plain,(
% 1.22/0.52    ~v1_relat_1(k1_xboole_0) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.22/0.52    inference(resolution,[],[f113,f43])).
% 1.22/0.52  fof(f43,plain,(
% 1.22/0.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f23])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f15])).
% 1.22/0.52  fof(f15,axiom,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.22/0.52  fof(f113,plain,(
% 1.22/0.52    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.22/0.52    inference(subsumption_resolution,[],[f108,f38])).
% 1.22/0.52  fof(f108,plain,(
% 1.22/0.52    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.22/0.52    inference(backward_demodulation,[],[f69,f102])).
% 1.22/0.52  fof(f69,plain,(
% 1.22/0.52    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.22/0.52    inference(superposition,[],[f46,f68])).
% 1.22/0.52  fof(f68,plain,(
% 1.22/0.52    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 1.22/0.52    inference(resolution,[],[f65,f38])).
% 1.22/0.52  fof(f65,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.22/0.52    inference(resolution,[],[f45,f41])).
% 1.22/0.52  fof(f45,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f17])).
% 1.22/0.52  fof(f17,axiom,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.22/0.52  fof(f46,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f26])).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.22/0.52    inference(flattening,[],[f25])).
% 1.22/0.52  fof(f25,plain,(
% 1.22/0.52    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.22/0.52    inference(ennf_transformation,[],[f16])).
% 1.22/0.52  fof(f16,axiom,(
% 1.22/0.52    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 1.22/0.52  fof(f67,plain,(
% 1.22/0.52    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.22/0.52    inference(resolution,[],[f63,f38])).
% 1.22/0.52  fof(f63,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.22/0.52    inference(resolution,[],[f44,f41])).
% 1.22/0.52  fof(f44,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (29991)------------------------------
% 1.22/0.52  % (29991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (29991)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (29991)Memory used [KB]: 6268
% 1.22/0.52  % (29991)Time elapsed: 0.066 s
% 1.22/0.52  % (29991)------------------------------
% 1.22/0.52  % (29991)------------------------------
% 1.22/0.52  % (29983)Success in time 0.159 s
%------------------------------------------------------------------------------
