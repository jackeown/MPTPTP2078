%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  75 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 223 expanded)
%              Number of equality atoms :   28 ( 123 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(global_subsumption,[],[f25,f57,f58])).

fof(f58,plain,(
    ~ sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f51,f19,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ sQ1_eqProxy(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_proxy_axiom,[],[f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( sQ1_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f51,plain,(
    ~ v1_xboole_0(k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f16,f22])).

fof(f22,plain,(
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

fof(f16,plain,(
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

fof(f44,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X0] :
      ( sQ1_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f20,f23])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f24,plain,(
    ~ sQ1_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f18,f23])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ~ sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f50,f19,f29])).

fof(f50,plain,(
    ~ v1_xboole_0(k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f16,f21])).

fof(f21,plain,(
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
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (25997)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (25997)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (25996)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (25989)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(global_subsumption,[],[f25,f57,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ~sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f51,f19,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~sQ1_eqProxy(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ1_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_relat_1(sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f44,f16,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0)) => (k1_xboole_0 != sK0 & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : ((k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (sQ1_eqProxy(k1_xboole_0,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f20,f23])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ~sQ1_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f18,f23])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f50,f19,f29])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_relat_1(sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f44,f16,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    sQ1_eqProxy(k1_xboole_0,k2_relat_1(sK0)) | sQ1_eqProxy(k1_xboole_0,k1_relat_1(sK0))),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f17,f23,f23])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (25997)------------------------------
% 0.21/0.48  % (25997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25997)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (25997)Memory used [KB]: 10618
% 0.21/0.48  % (25997)Time elapsed: 0.054 s
% 0.21/0.48  % (25997)------------------------------
% 0.21/0.48  % (25997)------------------------------
% 0.21/0.48  % (25982)Success in time 0.117 s
%------------------------------------------------------------------------------
