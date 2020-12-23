%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:09 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 120 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 370 expanded)
%              Number of equality atoms :   30 ( 169 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2937,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f2912,f2936])).

fof(f2936,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f2935])).

fof(f2935,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f2929,f34])).

fof(f34,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f26,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != sK0
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK0
      & ( k1_xboole_0 = k2_relat_1(sK0)
        | k1_xboole_0 = k1_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f2929,plain,
    ( sQ4_eqProxy(k1_xboole_0,sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f24,f2927,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | sQ4_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f33])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f2927,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f2923,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2923,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f24,f2918,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f2918,plain,
    ( v1_xboole_0(k1_relat_1(sK0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f27,f52,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ sQ4_eqProxy(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_proxy_axiom,[],[f33])).

fof(f52,plain,
    ( sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_1
  <=> sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f2912,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f2911])).

fof(f2911,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f2902,f72])).

fof(f72,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f67,f31])).

fof(f67,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f24,f65,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f65,plain,
    ( v1_xboole_0(k2_relat_1(sK0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f56,f27,f43])).

fof(f56,plain,
    ( sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_2
  <=> sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2902,plain,(
    r2_hidden(k4_tarski(sK1(sK0),sK2(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f34,f36])).

fof(f57,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f35,f54,f50])).

fof(f35,plain,
    ( sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK0))
    | sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f25,f33,f33])).

fof(f25,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.42  % (12195)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.48  % (12195)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f2937,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(avatar_sat_refutation,[],[f57,f2912,f2936])).
% 0.23/0.48  fof(f2936,plain,(
% 0.23/0.48    ~spl5_1),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f2935])).
% 0.23/0.48  fof(f2935,plain,(
% 0.23/0.48    $false | ~spl5_1),
% 0.23/0.48    inference(subsumption_resolution,[],[f2929,f34])).
% 0.23/0.48  fof(f34,plain,(
% 0.23/0.48    ~sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.23/0.48    inference(equality_proxy_replacement,[],[f26,f33])).
% 0.23/0.48  fof(f33,plain,(
% 0.23/0.48    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.23/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.23/0.48  fof(f26,plain,(
% 0.23/0.48    k1_xboole_0 != sK0),
% 0.23/0.48    inference(cnf_transformation,[],[f17])).
% 0.23/0.48  fof(f17,plain,(
% 0.23/0.48    k1_xboole_0 != sK0 & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f16])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0)) => (k1_xboole_0 != sK0 & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f9,plain,(
% 0.23/0.48    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.23/0.48    inference(flattening,[],[f8])).
% 0.23/0.48  fof(f8,plain,(
% 0.23/0.48    ? [X0] : ((k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,negated_conjecture,(
% 0.23/0.48    ~! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.23/0.48    inference(negated_conjecture,[],[f6])).
% 0.23/0.48  fof(f6,conjecture,(
% 0.23/0.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.23/0.48  fof(f2929,plain,(
% 0.23/0.48    sQ4_eqProxy(k1_xboole_0,sK0) | ~spl5_1),
% 0.23/0.48    inference(unit_resulting_resolution,[],[f24,f2927,f36])).
% 0.23/0.48  fof(f36,plain,(
% 0.23/0.48    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | sQ4_eqProxy(k1_xboole_0,X0)) )),
% 0.23/0.48    inference(equality_proxy_replacement,[],[f28,f33])).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f19])).
% 0.23/0.48  fof(f19,plain,(
% 0.23/0.48    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0))),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f18])).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f11,plain,(
% 0.23/0.48    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.23/0.48    inference(flattening,[],[f10])).
% 0.23/0.48  fof(f10,plain,(
% 0.23/0.48    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.23/0.48  fof(f2927,plain,(
% 0.23/0.48    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl5_1),
% 0.23/0.48    inference(unit_resulting_resolution,[],[f2923,f31])).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f23])).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f21,plain,(
% 0.23/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.48    inference(rectify,[],[f20])).
% 0.23/0.48  fof(f20,plain,(
% 0.23/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.48    inference(nnf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.48  fof(f2923,plain,(
% 0.23/0.48    v1_xboole_0(sK0) | ~spl5_1),
% 0.23/0.48    inference(unit_resulting_resolution,[],[f24,f2918,f29])).
% 0.23/0.48  fof(f29,plain,(
% 0.23/0.48    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f13])).
% 0.23/0.48  fof(f13,plain,(
% 0.23/0.48    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.23/0.48    inference(flattening,[],[f12])).
% 0.23/0.48  fof(f12,plain,(
% 0.23/0.48    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.23/0.48  fof(f2918,plain,(
% 0.23/0.48    v1_xboole_0(k1_relat_1(sK0)) | ~spl5_1),
% 0.23/0.48    inference(unit_resulting_resolution,[],[f27,f52,f43])).
% 0.23/0.48  fof(f43,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~sQ4_eqProxy(X0,X1) | v1_xboole_0(X1)) )),
% 0.23/0.48    inference(equality_proxy_axiom,[],[f33])).
% 0.23/0.48  fof(f52,plain,(
% 0.23/0.48    sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK0)) | ~spl5_1),
% 0.23/0.48    inference(avatar_component_clause,[],[f50])).
% 0.23/0.48  fof(f50,plain,(
% 0.23/0.48    spl5_1 <=> sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    v1_xboole_0(k1_xboole_0)),
% 0.23/0.48    inference(cnf_transformation,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    v1_xboole_0(k1_xboole_0)),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.23/0.48  fof(f24,plain,(
% 0.23/0.48    v1_relat_1(sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f17])).
% 0.23/0.48  fof(f2912,plain,(
% 0.23/0.48    ~spl5_2),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f2911])).
% 0.23/0.48  fof(f2911,plain,(
% 0.23/0.48    $false | ~spl5_2),
% 0.23/0.48    inference(subsumption_resolution,[],[f2902,f72])).
% 0.23/0.48  fof(f72,plain,(
% 0.23/0.48    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl5_2),
% 0.23/0.48    inference(unit_resulting_resolution,[],[f67,f31])).
% 0.23/0.48  fof(f67,plain,(
% 0.23/0.48    v1_xboole_0(sK0) | ~spl5_2),
% 0.23/0.48    inference(unit_resulting_resolution,[],[f24,f65,f30])).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f15])).
% 0.23/0.48  fof(f15,plain,(
% 0.23/0.48    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.23/0.48    inference(flattening,[],[f14])).
% 0.23/0.48  fof(f14,plain,(
% 0.23/0.48    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.23/0.48  fof(f65,plain,(
% 0.23/0.48    v1_xboole_0(k2_relat_1(sK0)) | ~spl5_2),
% 0.23/0.48    inference(unit_resulting_resolution,[],[f56,f27,f43])).
% 0.23/0.48  fof(f56,plain,(
% 0.23/0.48    sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK0)) | ~spl5_2),
% 0.23/0.48    inference(avatar_component_clause,[],[f54])).
% 0.23/0.48  fof(f54,plain,(
% 0.23/0.48    spl5_2 <=> sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.23/0.48  fof(f2902,plain,(
% 0.23/0.48    r2_hidden(k4_tarski(sK1(sK0),sK2(sK0)),sK0)),
% 0.23/0.48    inference(unit_resulting_resolution,[],[f24,f34,f36])).
% 0.23/0.48  fof(f57,plain,(
% 0.23/0.48    spl5_1 | spl5_2),
% 0.23/0.48    inference(avatar_split_clause,[],[f35,f54,f50])).
% 0.23/0.48  fof(f35,plain,(
% 0.23/0.48    sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK0)) | sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.23/0.48    inference(equality_proxy_replacement,[],[f25,f33,f33])).
% 0.23/0.48  fof(f25,plain,(
% 0.23/0.48    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f17])).
% 0.23/0.48  % SZS output end Proof for theBenchmark
% 0.23/0.48  % (12195)------------------------------
% 0.23/0.48  % (12195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (12195)Termination reason: Refutation
% 0.23/0.48  
% 0.23/0.48  % (12195)Memory used [KB]: 12281
% 0.23/0.48  % (12195)Time elapsed: 0.063 s
% 0.23/0.48  % (12195)------------------------------
% 0.23/0.48  % (12195)------------------------------
% 0.23/0.49  % (12177)Success in time 0.121 s
%------------------------------------------------------------------------------
