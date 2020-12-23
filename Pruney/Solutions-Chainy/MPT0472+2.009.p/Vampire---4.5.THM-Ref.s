%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 122 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 304 expanded)
%              Number of equality atoms :   28 ( 135 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f66,f74])).

fof(f74,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f68,f39])).

fof(f39,plain,
    ( sQ2_eqProxy(k1_xboole_0,k1_relat_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> sQ2_eqProxy(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,(
    ~ sQ2_eqProxy(k1_xboole_0,k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f54,f63,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ sQ2_eqProxy(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_proxy_axiom,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f50,f24,f31])).

fof(f24,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f16])).

fof(f16,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f50,plain,(
    sQ2_eqProxy(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ sQ2_eqProxy(X0,X1)
      | sQ2_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f25])).

fof(f45,plain,(
    sQ2_eqProxy(k1_xboole_0,sK1) ),
    inference(unit_resulting_resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0] :
      ( sQ2_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f21,f25])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f54,plain,(
    ~ v1_xboole_0(k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f18,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f18,plain,(
    v1_relat_1(sK0) ),
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

% (23918)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f46,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f26,f28])).

fof(f26,plain,(
    ~ sQ2_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f20,f25])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f59,f63])).

fof(f59,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f55,f43,f31])).

fof(f43,plain,
    ( sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,(
    ~ v1_xboole_0(k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f18,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f44,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f27,f41,f37])).

fof(f27,plain,
    ( sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK0))
    | sQ2_eqProxy(k1_xboole_0,k1_relat_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f19,f25,f25])).

fof(f19,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:24:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (23905)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (23905)Refutation not found, incomplete strategy% (23905)------------------------------
% 0.22/0.48  % (23905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23905)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23905)Memory used [KB]: 6140
% 0.22/0.48  % (23905)Time elapsed: 0.050 s
% 0.22/0.48  % (23905)------------------------------
% 0.22/0.48  % (23905)------------------------------
% 0.22/0.48  % (23919)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (23919)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f44,f66,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ~spl3_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    $false | ~spl3_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    sQ2_eqProxy(k1_xboole_0,k1_relat_1(sK0)) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl3_1 <=> sQ2_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ~sQ2_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f54,f63,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~sQ2_eqProxy(X0,X1) | v1_xboole_0(X1)) )),
% 0.22/0.48    inference(equality_proxy_axiom,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f50,f24,f31])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v1_xboole_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    v1_xboole_0(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    sQ2_eqProxy(sK1,k1_xboole_0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f45,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sQ2_eqProxy(X0,X1) | sQ2_eqProxy(X1,X0)) )),
% 0.22/0.49    inference(equality_proxy_axiom,[],[f25])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    sQ2_eqProxy(k1_xboole_0,sK1)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f24,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0] : (sQ2_eqProxy(k1_xboole_0,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(equality_proxy_replacement,[],[f21,f25])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_relat_1(sK0))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f46,f18,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k1_xboole_0 != sK0 & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0)) => (k1_xboole_0 != sK0 & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  % (23918)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0] : ((k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ~v1_xboole_0(sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f26,f28])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ~sQ2_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.49    inference(equality_proxy_replacement,[],[f20,f25])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    k1_xboole_0 != sK0),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~spl3_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    $false | ~spl3_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f59,f63])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | ~spl3_2),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f55,f43,f31])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK0)) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    spl3_2 <=> sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_relat_1(sK0))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f46,f18,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl3_1 | spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f41,f37])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK0)) | sQ2_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.22/0.49    inference(equality_proxy_replacement,[],[f19,f25,f25])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (23919)------------------------------
% 0.22/0.49  % (23919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23919)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (23919)Memory used [KB]: 10618
% 0.22/0.49  % (23919)Time elapsed: 0.062 s
% 0.22/0.49  % (23919)------------------------------
% 0.22/0.49  % (23919)------------------------------
% 0.22/0.49  % (23904)Success in time 0.121 s
%------------------------------------------------------------------------------
