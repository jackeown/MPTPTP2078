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
% DateTime   : Thu Dec  3 12:30:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  72 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 174 expanded)
%              Number of equality atoms :   23 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f62,f65,f70])).

fof(f70,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f32,f38,f32,f35,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X1,X3)
      | ~ sQ1_eqProxy(X2,X3)
      | ~ r1_xboole_0(X0,X2)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( sQ1_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).

fof(f35,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_2
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f38,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ sQ1_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0)
      | r1_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f16,f17])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f21,plain,(
    ! [X0] : sQ1_eqProxy(k3_xboole_0(X0,X0),X0) ),
    inference(equality_proxy_replacement,[],[f14,f17])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f32,plain,
    ( sQ1_eqProxy(k1_xboole_0,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> sQ1_eqProxy(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f63,f32])).

fof(f63,plain,
    ( ~ sQ1_eqProxy(k1_xboole_0,sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f20,f36])).

fof(f36,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f20,plain,
    ( ~ sQ1_eqProxy(k1_xboole_0,sK0)
    | ~ r1_xboole_0(sK0,sK0) ),
    inference(equality_proxy_replacement,[],[f10,f17])).

fof(f10,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( r1_xboole_0(sK0,sK0)
      & k1_xboole_0 != sK0 )
    | ( k1_xboole_0 = sK0
      & ~ r1_xboole_0(sK0,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] :
        ( ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
        | ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) )
   => ( ( r1_xboole_0(sK0,sK0)
        & k1_xboole_0 != sK0 )
      | ( k1_xboole_0 = sK0
        & ~ r1_xboole_0(sK0,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f62,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f57,f36])).

fof(f57,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl2_1 ),
    inference(resolution,[],[f53,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f15,f17])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,
    ( ~ sQ1_eqProxy(k3_xboole_0(sK0,sK0),k1_xboole_0)
    | spl2_1 ),
    inference(resolution,[],[f48,f21])).

fof(f48,plain,
    ( ! [X2] :
        ( ~ sQ1_eqProxy(X2,sK0)
        | ~ sQ1_eqProxy(X2,k1_xboole_0) )
    | spl2_1 ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(X1,X0)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f17])).

fof(f43,plain,
    ( ! [X0] :
        ( ~ sQ1_eqProxy(k1_xboole_0,X0)
        | ~ sQ1_eqProxy(X0,sK0) )
    | spl2_1 ),
    inference(resolution,[],[f28,f31])).

fof(f31,plain,
    ( ~ sQ1_eqProxy(k1_xboole_0,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sQ1_eqProxy(X0,X2)
      | ~ sQ1_eqProxy(X1,X2)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f17])).

fof(f37,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f18,f34,f30])).

fof(f18,plain,
    ( r1_xboole_0(sK0,sK0)
    | sQ1_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f13,f17])).

fof(f13,plain,
    ( r1_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (29196)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.46  % (29196)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f37,f62,f65,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ~spl2_1 | spl2_2),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    $false | (~spl2_1 | spl2_2)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f32,f38,f32,f35,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X1,X3) | ~sQ1_eqProxy(X2,X3) | ~r1_xboole_0(X0,X2) | ~sQ1_eqProxy(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_axiom,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X1,X0] : (sQ1_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK0) | spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl2_2 <=> r1_xboole_0(sK0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.47    inference(resolution,[],[f21,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~sQ1_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f16,f17])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0] : (sQ1_eqProxy(k3_xboole_0(X0,X0),X0)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f14,f17])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,plain,(
% 0.22/0.47    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.47    inference(rectify,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    sQ1_eqProxy(k1_xboole_0,sK0) | ~spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    spl2_1 <=> sQ1_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ~spl2_1 | ~spl2_2),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    $false | (~spl2_1 | ~spl2_2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f63,f32])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ~sQ1_eqProxy(k1_xboole_0,sK0) | ~spl2_2),
% 0.22/0.47    inference(subsumption_resolution,[],[f20,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK0) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f34])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ~sQ1_eqProxy(k1_xboole_0,sK0) | ~r1_xboole_0(sK0,sK0)),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f10,f17])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    k1_xboole_0 != sK0 | ~r1_xboole_0(sK0,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    (r1_xboole_0(sK0,sK0) & k1_xboole_0 != sK0) | (k1_xboole_0 = sK0 & ~r1_xboole_0(sK0,sK0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0))) => ((r1_xboole_0(sK0,sK0) & k1_xboole_0 != sK0) | (k1_xboole_0 = sK0 & ~r1_xboole_0(sK0,sK0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.47    inference(negated_conjecture,[],[f3])).
% 0.22/0.47  fof(f3,conjecture,(
% 0.22/0.47    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl2_1 | ~spl2_2),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    $false | (spl2_1 | ~spl2_2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f57,f36])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK0) | spl2_1),
% 0.22/0.47    inference(resolution,[],[f53,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sQ1_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f15,f17])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ~sQ1_eqProxy(k3_xboole_0(sK0,sK0),k1_xboole_0) | spl2_1),
% 0.22/0.47    inference(resolution,[],[f48,f21])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X2] : (~sQ1_eqProxy(X2,sK0) | ~sQ1_eqProxy(X2,k1_xboole_0)) ) | spl2_1),
% 0.22/0.47    inference(resolution,[],[f43,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sQ1_eqProxy(X1,X0) | ~sQ1_eqProxy(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_axiom,[],[f17])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0] : (~sQ1_eqProxy(k1_xboole_0,X0) | ~sQ1_eqProxy(X0,sK0)) ) | spl2_1),
% 0.22/0.47    inference(resolution,[],[f28,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ~sQ1_eqProxy(k1_xboole_0,sK0) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f30])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (sQ1_eqProxy(X0,X2) | ~sQ1_eqProxy(X1,X2) | ~sQ1_eqProxy(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_axiom,[],[f17])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl2_1 | spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f34,f30])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK0) | sQ1_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f13,f17])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK0) | k1_xboole_0 = sK0),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (29196)------------------------------
% 0.22/0.47  % (29196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29196)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (29196)Memory used [KB]: 6140
% 0.22/0.47  % (29196)Time elapsed: 0.055 s
% 0.22/0.47  % (29196)------------------------------
% 0.22/0.47  % (29196)------------------------------
% 0.22/0.47  % (29186)Success in time 0.111 s
%------------------------------------------------------------------------------
