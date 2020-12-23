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
% DateTime   : Thu Dec  3 12:30:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 168 expanded)
%              Number of leaves         :    7 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :   91 ( 416 expanded)
%              Number of equality atoms :   12 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f451,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f409,f249,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f249,plain,(
    r1_tarski(k2_xboole_0(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f147,f23])).

fof(f23,plain,(
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

fof(f147,plain,(
    r2_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f43,f35,f18,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_xboole_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r2_xboole_0(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f18,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f35,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f28])).

fof(f43,plain,(
    sQ3_eqProxy(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f28])).

fof(f41,plain,(
    sQ3_eqProxy(k2_xboole_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f17,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k2_xboole_0(X0,X1),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f22,f28])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f409,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f19,f404,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X0,X1)
      | r2_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f25,f28])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f404,plain,(
    ~ sQ3_eqProxy(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f395,f36])).

fof(f395,plain,(
    ~ sQ3_eqProxy(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f148,f58,f391,f33])).

fof(f391,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f384,f23])).

fof(f384,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f159,f30])).

fof(f159,plain,(
    ~ sQ3_eqProxy(k2_xboole_0(sK1,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f55,f145,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f28])).

fof(f145,plain,(
    ~ sQ3_eqProxy(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f19,f35,f18,f33])).

fof(f55,plain,(
    sQ3_eqProxy(sK1,k2_xboole_0(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f43,f29,f37])).

fof(f29,plain,(
    ! [X0,X1] : sQ3_eqProxy(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    inference(equality_proxy_replacement,[],[f21,f28])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f58,plain,(
    sQ3_eqProxy(k2_xboole_0(sK1,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f29,f41,f37])).

fof(f148,plain,(
    r2_xboole_0(k2_xboole_0(sK1,sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f55,f35,f18,f33])).

fof(f19,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:05:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (12694)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (12701)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (12693)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (12701)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f451,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f409,f249,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    r1_tarski(k2_xboole_0(sK0,sK1),sK2)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f147,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    r2_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f43,f35,f18,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_xboole_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r2_xboole_0(X1,X3)) )),
% 0.22/0.49    inference(equality_proxy_axiom,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    r2_xboole_0(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.22/0.49    inference(equality_proxy_axiom,[],[f28])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    sQ3_eqProxy(sK1,k2_xboole_0(sK0,sK1))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f41,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0)) )),
% 0.22/0.49    inference(equality_proxy_axiom,[],[f28])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    sQ3_eqProxy(k2_xboole_0(sK0,sK1),sK1)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f17,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sQ3_eqProxy(k2_xboole_0(X0,X1),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(equality_proxy_replacement,[],[f22,f28])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    r1_tarski(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f409,plain,(
% 0.22/0.49    ~r1_tarski(sK0,sK2)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f19,f404,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sQ3_eqProxy(X0,X1) | r2_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(equality_proxy_replacement,[],[f25,f28])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    ~sQ3_eqProxy(sK0,sK2)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f395,f36])).
% 0.22/0.49  fof(f395,plain,(
% 0.22/0.49    ~sQ3_eqProxy(sK2,sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f148,f58,f391,f33])).
% 0.22/0.49  fof(f391,plain,(
% 0.22/0.49    ~r2_xboole_0(sK1,sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f384,f23])).
% 0.22/0.49  fof(f384,plain,(
% 0.22/0.49    ~r1_tarski(sK1,sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f159,f30])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ~sQ3_eqProxy(k2_xboole_0(sK1,sK0),sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f55,f145,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X0,X2)) )),
% 0.22/0.49    inference(equality_proxy_axiom,[],[f28])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~sQ3_eqProxy(sK1,sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f19,f35,f18,f33])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    sQ3_eqProxy(sK1,k2_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f43,f29,f37])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sQ3_eqProxy(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0))) )),
% 0.22/0.49    inference(equality_proxy_replacement,[],[f21,f28])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    sQ3_eqProxy(k2_xboole_0(sK1,sK0),sK1)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f29,f41,f37])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    r2_xboole_0(k2_xboole_0(sK1,sK0),sK2)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f55,f35,f18,f33])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (12701)------------------------------
% 0.22/0.49  % (12701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12701)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (12701)Memory used [KB]: 10746
% 0.22/0.49  % (12701)Time elapsed: 0.014 s
% 0.22/0.49  % (12701)------------------------------
% 0.22/0.49  % (12701)------------------------------
% 0.22/0.49  % (12702)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (12684)Success in time 0.126 s
%------------------------------------------------------------------------------
