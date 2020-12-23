%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 102 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 285 expanded)
%              Number of equality atoms :   28 ( 125 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f68,f86])).

fof(f86,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f80,f43])).

fof(f43,plain,(
    ~ sQ1_eqProxy(sK0,k1_xboole_0) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ~ sQ1_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f18,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( sQ1_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).

fof(f14,plain,
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

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(X1,X0)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f23])).

fof(f80,plain,
    ( sQ1_eqProxy(sK0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sQ1_eqProxy(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f26,f19])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | sQ1_eqProxy(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f74,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f70,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f69,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f69,plain,
    ( v1_xboole_0(k1_relat_1(sK0))
    | ~ spl2_1 ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ sQ1_eqProxy(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f29,f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ sQ1_eqProxy(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_proxy_axiom,[],[f23])).

fof(f37,plain,
    ( sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f68,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f62,f43])).

fof(f62,plain,
    ( sQ1_eqProxy(sK0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f53,f16])).

fof(f53,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f50,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f50,plain,
    ( v1_xboole_0(k2_relat_1(sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,
    ( sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f42,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f25,f39,f35])).

fof(f25,plain,
    ( sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0))
    | sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f17,f23,f23])).

fof(f17,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (16153)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.45  % (16151)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.45  % (16160)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.46  % (16151)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f42,f68,f86])).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    ~spl2_1),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f85])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    $false | ~spl2_1),
% 0.19/0.46    inference(subsumption_resolution,[],[f80,f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ~sQ1_eqProxy(sK0,k1_xboole_0)),
% 0.19/0.46    inference(resolution,[],[f32,f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ~sQ1_eqProxy(k1_xboole_0,sK0)),
% 0.19/0.46    inference(equality_proxy_replacement,[],[f18,f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X1,X0] : (sQ1_eqProxy(X0,X1) <=> X0 = X1)),
% 0.19/0.46    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    k1_xboole_0 != sK0),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    k1_xboole_0 != sK0 & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0)) => (k1_xboole_0 != sK0 & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f8,plain,(
% 0.19/0.46    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f7])).
% 0.19/0.46  fof(f7,plain,(
% 0.19/0.46    ? [X0] : ((k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,negated_conjecture,(
% 0.19/0.46    ~! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.46    inference(negated_conjecture,[],[f5])).
% 0.19/0.46  fof(f5,conjecture,(
% 0.19/0.46    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ( ! [X0,X1] : (sQ1_eqProxy(X1,X0) | ~sQ1_eqProxy(X0,X1)) )),
% 0.19/0.46    inference(equality_proxy_axiom,[],[f23])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    sQ1_eqProxy(sK0,k1_xboole_0) | ~spl2_1),
% 0.19/0.46    inference(resolution,[],[f74,f47])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_xboole_0(X0) | sQ1_eqProxy(X0,k1_xboole_0)) )),
% 0.19/0.46    inference(resolution,[],[f26,f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    v1_xboole_0(k1_xboole_0)),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    v1_xboole_0(k1_xboole_0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v1_xboole_0(X1) | sQ1_eqProxy(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.19/0.46    inference(equality_proxy_replacement,[],[f22,f23])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.19/0.46  fof(f74,plain,(
% 0.19/0.46    v1_xboole_0(sK0) | ~spl2_1),
% 0.19/0.46    inference(subsumption_resolution,[],[f70,f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    v1_relat_1(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl2_1),
% 0.19/0.46    inference(resolution,[],[f69,f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f9])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    v1_xboole_0(k1_relat_1(sK0)) | ~spl2_1),
% 0.19/0.46    inference(resolution,[],[f37,f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X0] : (~sQ1_eqProxy(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.19/0.46    inference(resolution,[],[f29,f19])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~sQ1_eqProxy(X0,X1) | v1_xboole_0(X1)) )),
% 0.19/0.46    inference(equality_proxy_axiom,[],[f23])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0)) | ~spl2_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    spl2_1 <=> sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    ~spl2_2),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f67])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    $false | ~spl2_2),
% 0.19/0.46    inference(subsumption_resolution,[],[f62,f43])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    sQ1_eqProxy(sK0,k1_xboole_0) | ~spl2_2),
% 0.19/0.46    inference(resolution,[],[f57,f47])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    v1_xboole_0(sK0) | ~spl2_2),
% 0.19/0.46    inference(subsumption_resolution,[],[f53,f16])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl2_2),
% 0.19/0.46    inference(resolution,[],[f50,f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    v1_xboole_0(k2_relat_1(sK0)) | ~spl2_2),
% 0.19/0.46    inference(resolution,[],[f49,f41])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0)) | ~spl2_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f39])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    spl2_2 <=> sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    spl2_1 | spl2_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f25,f39,f35])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0)) | sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.19/0.46    inference(equality_proxy_replacement,[],[f17,f23,f23])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (16151)------------------------------
% 0.19/0.46  % (16151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (16151)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (16151)Memory used [KB]: 6140
% 0.19/0.46  % (16151)Time elapsed: 0.055 s
% 0.19/0.46  % (16151)------------------------------
% 0.19/0.46  % (16151)------------------------------
% 0.19/0.46  % (16145)Success in time 0.107 s
%------------------------------------------------------------------------------
