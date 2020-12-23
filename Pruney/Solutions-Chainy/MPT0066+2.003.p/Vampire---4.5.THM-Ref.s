%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 100 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :   17
%              Number of atoms          :  103 ( 293 expanded)
%              Number of equality atoms :    7 (  25 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f17,f18,f170])).

fof(f170,plain,(
    ! [X5] :
      ( ~ r2_xboole_0(X5,sK2)
      | ~ r1_tarski(sK0,X5) ) ),
    inference(resolution,[],[f132,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f132,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK2)
      | ~ r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f122,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f122,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f120,f19])).

fof(f19,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f120,plain,
    ( r2_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f113,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X0,X1)
      | r2_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f24,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f113,plain,(
    ~ sQ3_eqProxy(sK0,sK2) ),
    inference(resolution,[],[f112,f54])).

fof(f54,plain,(
    ! [X3] :
      ( ~ r2_xboole_0(X3,sK1)
      | ~ sQ3_eqProxy(X3,sK2) ) ),
    inference(resolution,[],[f48,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f48,plain,(
    ! [X0] :
      ( r2_xboole_0(sK1,X0)
      | ~ sQ3_eqProxy(X0,sK2) ) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f39,plain,(
    ! [X6,X7] :
      ( ~ sQ3_eqProxy(sK1,X6)
      | r2_xboole_0(X6,X7)
      | ~ sQ3_eqProxy(X7,sK2) ) ),
    inference(resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(sK2,X0)
      | ~ sQ3_eqProxy(sK1,X1)
      | r2_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f29,f18])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_xboole_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r2_xboole_0(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f112,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f108,f19])).

fof(f108,plain,
    ( r2_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f46,f17])).

fof(f46,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | r2_xboole_0(X2,sK1)
      | r2_xboole_0(X2,sK2) ) ),
    inference(resolution,[],[f43,f28])).

fof(f43,plain,(
    ! [X3] :
      ( ~ sQ3_eqProxy(X3,sK1)
      | r2_xboole_0(X3,sK2) ) ),
    inference(resolution,[],[f36,f32])).

fof(f36,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(sK1,X0)
      | r2_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f35,f31])).

fof(f18,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (23541)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (23551)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (23541)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f17,f18,f170])).
% 0.22/0.47  fof(f170,plain,(
% 0.22/0.47    ( ! [X5] : (~r2_xboole_0(X5,sK2) | ~r1_tarski(sK0,X5)) )),
% 0.22/0.47    inference(resolution,[],[f132,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    ( ! [X2] : (~r1_tarski(X2,sK2) | ~r1_tarski(sK0,X2)) )),
% 0.22/0.47    inference(resolution,[],[f122,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    ~r1_tarski(sK0,sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f120,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    r2_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK2)),
% 0.22/0.47    inference(resolution,[],[f113,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sQ3_eqProxy(X0,X1) | r2_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f24,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~sQ3_eqProxy(sK0,sK2)),
% 0.22/0.47    inference(resolution,[],[f112,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X3] : (~r2_xboole_0(X3,sK1) | ~sQ3_eqProxy(X3,sK2)) )),
% 0.22/0.47    inference(resolution,[],[f48,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0] : (r2_xboole_0(sK1,X0) | ~sQ3_eqProxy(X0,sK2)) )),
% 0.22/0.47    inference(resolution,[],[f39,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.22/0.47    inference(equality_proxy_axiom,[],[f27])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X6,X7] : (~sQ3_eqProxy(sK1,X6) | r2_xboole_0(X6,X7) | ~sQ3_eqProxy(X7,sK2)) )),
% 0.22/0.47    inference(resolution,[],[f35,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_axiom,[],[f27])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~sQ3_eqProxy(sK2,X0) | ~sQ3_eqProxy(sK1,X1) | r2_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(resolution,[],[f29,f18])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~r2_xboole_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r2_xboole_0(X1,X3)) )),
% 0.22/0.47    inference(equality_proxy_axiom,[],[f27])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    r2_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f108,f19])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    r2_xboole_0(sK0,sK1) | r2_xboole_0(sK0,sK2)),
% 0.22/0.47    inference(resolution,[],[f46,f17])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X2] : (~r1_tarski(X2,sK1) | r2_xboole_0(X2,sK1) | r2_xboole_0(X2,sK2)) )),
% 0.22/0.47    inference(resolution,[],[f43,f28])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X3] : (~sQ3_eqProxy(X3,sK1) | r2_xboole_0(X3,sK2)) )),
% 0.22/0.47    inference(resolution,[],[f36,f32])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0] : (~sQ3_eqProxy(sK1,X0) | r2_xboole_0(X0,sK2)) )),
% 0.22/0.47    inference(resolution,[],[f35,f31])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    r2_xboole_0(sK1,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (23541)------------------------------
% 0.22/0.47  % (23541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (23541)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (23541)Memory used [KB]: 6140
% 0.22/0.47  % (23541)Time elapsed: 0.057 s
% 0.22/0.47  % (23541)------------------------------
% 0.22/0.47  % (23541)------------------------------
% 0.22/0.47  % (23543)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (23535)Success in time 0.113 s
%------------------------------------------------------------------------------
