%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:02 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 105 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 278 expanded)
%              Number of equality atoms :   11 (  19 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f119])).

fof(f119,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f28,f86,f81,f36])).

fof(f36,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f81,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK0,k6_relat_1(sK1)),sK4(sK0,k6_relat_1(sK1))),k6_relat_1(sK1))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f28,f78,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK4(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

fof(f78,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),k6_relat_1(sK1))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f28,f20,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(k6_relat_1(X0),k6_relat_1(X1))
        | r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X1,sK2)) )
    | ~ spl7_2 ),
    inference(superposition,[],[f76,f39])).

fof(f39,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

fof(f76,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_relat_1(sK2,X0),k8_relat_1(X1,sK2))
        | ~ r1_tarski(X0,k6_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f70,f28])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | r1_tarski(k5_relat_1(sK2,X1),k8_relat_1(X0,sK2)) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_2
  <=> ! [X1,X0] :
        ( r1_tarski(k5_relat_1(sK2,X1),k8_relat_1(X0,sK2))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f20,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,
    ( r2_hidden(sK4(sK0,k6_relat_1(sK1)),sK1)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f19,f80,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f80,plain,
    ( r2_hidden(sK4(sK0,k6_relat_1(sK1)),sK0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f28,f78,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f75,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f18,f67])).

fof(f67,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

% (9401)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f65,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f71,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f47,f69,f65])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(sK2,X1),k8_relat_1(X0,sK2))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f27,f39])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.42/0.57  % (9402)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.57  % (9410)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.57  % (9409)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.57  % (9417)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.58  % (9425)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.58  % (9402)Refutation found. Thanks to Tanya!
% 1.42/0.58  % SZS status Theorem for theBenchmark
% 1.42/0.58  % (9409)Refutation not found, incomplete strategy% (9409)------------------------------
% 1.42/0.58  % (9409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (9409)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (9409)Memory used [KB]: 10618
% 1.42/0.58  % (9409)Time elapsed: 0.146 s
% 1.42/0.58  % (9409)------------------------------
% 1.42/0.58  % (9409)------------------------------
% 1.79/0.59  % (9404)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.79/0.59  % SZS output start Proof for theBenchmark
% 1.79/0.59  fof(f120,plain,(
% 1.79/0.59    $false),
% 1.79/0.59    inference(avatar_sat_refutation,[],[f71,f75,f119])).
% 1.79/0.59  fof(f119,plain,(
% 1.79/0.59    ~spl7_2),
% 1.79/0.59    inference(avatar_contradiction_clause,[],[f117])).
% 1.79/0.59  fof(f117,plain,(
% 1.79/0.59    $false | ~spl7_2),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f28,f86,f81,f36])).
% 1.79/0.59  fof(f36,plain,(
% 1.79/0.59    ( ! [X0,X3] : (~r2_hidden(X3,X0) | ~v1_relat_1(k6_relat_1(X0)) | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0))) )),
% 1.79/0.59    inference(equality_resolution,[],[f35])).
% 1.79/0.59  fof(f35,plain,(
% 1.79/0.59    ( ! [X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X3,X0) | r2_hidden(k4_tarski(X3,X3),X1) | k6_relat_1(X0) != X1) )),
% 1.79/0.59    inference(equality_resolution,[],[f34])).
% 1.79/0.59  fof(f34,plain,(
% 1.79/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | X2 != X3 | r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 1.79/0.59    inference(cnf_transformation,[],[f17])).
% 1.79/0.59  fof(f17,plain,(
% 1.79/0.59    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 1.79/0.59    inference(ennf_transformation,[],[f2])).
% 1.79/0.59  fof(f2,axiom,(
% 1.79/0.59    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).
% 1.79/0.59  fof(f81,plain,(
% 1.79/0.59    ~r2_hidden(k4_tarski(sK4(sK0,k6_relat_1(sK1)),sK4(sK0,k6_relat_1(sK1))),k6_relat_1(sK1)) | ~spl7_2),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f28,f78,f26])).
% 1.79/0.59  fof(f26,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK4(X0,X1)),X1) | r1_tarski(k6_relat_1(X0),X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f14])).
% 1.79/0.59  fof(f14,plain,(
% 1.79/0.59    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 1.79/0.59    inference(flattening,[],[f13])).
% 1.79/0.59  fof(f13,plain,(
% 1.79/0.59    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 1.79/0.59    inference(ennf_transformation,[],[f6])).
% 1.79/0.59  fof(f6,axiom,(
% 1.79/0.59    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).
% 1.79/0.59  fof(f78,plain,(
% 1.79/0.59    ~r1_tarski(k6_relat_1(sK0),k6_relat_1(sK1)) | ~spl7_2),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f28,f20,f77])).
% 1.79/0.59  fof(f77,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) | r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X1,sK2))) ) | ~spl7_2),
% 1.79/0.59    inference(superposition,[],[f76,f39])).
% 1.79/0.59  fof(f39,plain,(
% 1.79/0.59    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f18,f21])).
% 1.79/0.59  fof(f21,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.79/0.59    inference(cnf_transformation,[],[f11])).
% 1.79/0.59  fof(f11,plain,(
% 1.79/0.59    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.79/0.59    inference(ennf_transformation,[],[f4])).
% 1.79/0.59  fof(f4,axiom,(
% 1.79/0.59    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.79/0.59  fof(f18,plain,(
% 1.79/0.59    v1_relat_1(sK2)),
% 1.79/0.59    inference(cnf_transformation,[],[f10])).
% 1.79/0.59  fof(f10,plain,(
% 1.79/0.59    ? [X0,X1,X2] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.79/0.59    inference(flattening,[],[f9])).
% 1.79/0.59  fof(f9,plain,(
% 1.79/0.59    ? [X0,X1,X2] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.79/0.59    inference(ennf_transformation,[],[f8])).
% 1.79/0.59  fof(f8,negated_conjecture,(
% 1.79/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 1.79/0.59    inference(negated_conjecture,[],[f7])).
% 1.79/0.59  fof(f7,conjecture,(
% 1.79/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).
% 1.79/0.59  fof(f76,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r1_tarski(k5_relat_1(sK2,X0),k8_relat_1(X1,sK2)) | ~r1_tarski(X0,k6_relat_1(X1)) | ~v1_relat_1(X0)) ) | ~spl7_2),
% 1.79/0.59    inference(resolution,[],[f70,f28])).
% 1.79/0.59  fof(f70,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~r1_tarski(X1,k6_relat_1(X0)) | r1_tarski(k5_relat_1(sK2,X1),k8_relat_1(X0,sK2))) ) | ~spl7_2),
% 1.79/0.59    inference(avatar_component_clause,[],[f69])).
% 1.79/0.59  fof(f69,plain,(
% 1.79/0.59    spl7_2 <=> ! [X1,X0] : (r1_tarski(k5_relat_1(sK2,X1),k8_relat_1(X0,sK2)) | ~v1_relat_1(X1) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)))),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.79/0.59  fof(f20,plain,(
% 1.79/0.59    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),
% 1.79/0.59    inference(cnf_transformation,[],[f10])).
% 1.79/0.59  fof(f86,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,k6_relat_1(sK1)),sK1) | ~spl7_2),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f19,f80,f22])).
% 1.79/0.59  fof(f22,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f12])).
% 1.79/0.59  fof(f12,plain,(
% 1.79/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f1])).
% 1.79/0.59  fof(f1,axiom,(
% 1.79/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.79/0.59  fof(f80,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,k6_relat_1(sK1)),sK0) | ~spl7_2),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f28,f78,f25])).
% 1.79/0.59  fof(f25,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK4(X0,X1),X0) | r1_tarski(k6_relat_1(X0),X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f14])).
% 1.79/0.59  fof(f19,plain,(
% 1.79/0.59    r1_tarski(sK0,sK1)),
% 1.79/0.59    inference(cnf_transformation,[],[f10])).
% 1.79/0.59  fof(f28,plain,(
% 1.79/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.79/0.59    inference(cnf_transformation,[],[f3])).
% 1.79/0.59  fof(f3,axiom,(
% 1.79/0.59    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.79/0.59  fof(f75,plain,(
% 1.79/0.59    spl7_1),
% 1.79/0.59    inference(avatar_contradiction_clause,[],[f72])).
% 1.79/0.59  fof(f72,plain,(
% 1.79/0.59    $false | spl7_1),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f18,f67])).
% 1.79/0.59  fof(f67,plain,(
% 1.79/0.59    ~v1_relat_1(sK2) | spl7_1),
% 1.79/0.59    inference(avatar_component_clause,[],[f65])).
% 1.79/0.59  % (9401)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.79/0.59  fof(f65,plain,(
% 1.79/0.59    spl7_1 <=> v1_relat_1(sK2)),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.79/0.59  fof(f71,plain,(
% 1.79/0.59    ~spl7_1 | spl7_2),
% 1.79/0.59    inference(avatar_split_clause,[],[f47,f69,f65])).
% 1.79/0.59  fof(f47,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r1_tarski(k5_relat_1(sK2,X1),k8_relat_1(X0,sK2)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(sK2) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.79/0.59    inference(superposition,[],[f27,f39])).
% 1.79/0.59  fof(f27,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f16])).
% 1.79/0.59  fof(f16,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.79/0.59    inference(flattening,[],[f15])).
% 1.79/0.59  fof(f15,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.79/0.59    inference(ennf_transformation,[],[f5])).
% 1.79/0.59  fof(f5,axiom,(
% 1.79/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 1.79/0.59  % SZS output end Proof for theBenchmark
% 1.79/0.59  % (9402)------------------------------
% 1.79/0.59  % (9402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.59  % (9402)Termination reason: Refutation
% 1.79/0.59  
% 1.79/0.59  % (9402)Memory used [KB]: 6268
% 1.79/0.59  % (9402)Time elapsed: 0.147 s
% 1.79/0.59  % (9402)------------------------------
% 1.79/0.59  % (9402)------------------------------
% 1.79/0.59  % (9397)Success in time 0.231 s
%------------------------------------------------------------------------------
