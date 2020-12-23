%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 111 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 297 expanded)
%              Number of equality atoms :   12 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f452,plain,(
    $false ),
    inference(subsumption_resolution,[],[f449,f223])).

fof(f223,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f219,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

% (22895)Refutation not found, incomplete strategy% (22895)------------------------------
% (22895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f219,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f21,f209,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X0,X1)
      | r2_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f28,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f209,plain,(
    ~ sQ3_eqProxy(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f188,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f188,plain,(
    ~ sQ3_eqProxy(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f42,f38,f168,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_xboole_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r2_xboole_0(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f168,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f20,f150,f34])).

fof(f150,plain,(
    ~ sQ3_eqProxy(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f21,f38,f19,f36])).

fof(f19,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f20,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f42,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f19,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f21,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f449,plain,(
    r1_tarski(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f158,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f158,plain,(
    r2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f61,f19,f36])).

fof(f61,plain,(
    sQ3_eqProxy(sK1,k3_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f32,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f32,plain,(
    ! [X0,X1] : sQ3_eqProxy(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(equality_proxy_replacement,[],[f23,f31])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    sQ3_eqProxy(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f39])).

fof(f46,plain,(
    sQ3_eqProxy(k3_xboole_0(sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f20,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k3_xboole_0(X0,X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f25,f31])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:56:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (22900)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (22888)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (22890)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (22892)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (22895)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (22900)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f452,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f449,f223])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(sK2,X0))) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f219,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % (22895)Refutation not found, incomplete strategy% (22895)------------------------------
% 0.21/0.48  % (22895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f21,f209,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(X0,X1) | r2_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f28,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ~sQ3_eqProxy(sK0,sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f188,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f31])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~sQ3_eqProxy(sK2,sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f42,f38,f168,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_xboole_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r2_xboole_0(X1,X3)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f31])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    r2_xboole_0(sK1,sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f20,f150,f34])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~sQ3_eqProxy(sK1,sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f21,f38,f19,f36])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    r2_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f31])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~r2_xboole_0(sK1,sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f19,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f449,plain,(
% 0.21/0.48    r1_tarski(sK0,k3_xboole_0(sK2,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f158,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    r2_xboole_0(sK0,k3_xboole_0(sK2,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f38,f61,f19,f36])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    sQ3_eqProxy(sK1,k3_xboole_0(sK2,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f48,f32,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X0,X2)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f31])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f23,f31])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    sQ3_eqProxy(sK1,k3_xboole_0(sK1,sK2))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f46,f39])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    sQ3_eqProxy(k3_xboole_0(sK1,sK2),sK1)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f20,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k3_xboole_0(X0,X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f25,f31])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22900)------------------------------
% 0.21/0.48  % (22900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22900)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22900)Memory used [KB]: 10746
% 0.21/0.48  % (22900)Time elapsed: 0.013 s
% 0.21/0.48  % (22900)------------------------------
% 0.21/0.48  % (22900)------------------------------
% 0.21/0.48  % (22878)Success in time 0.123 s
%------------------------------------------------------------------------------
