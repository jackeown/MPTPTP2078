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
% DateTime   : Thu Dec  3 12:55:08 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 100 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f125,f153])).

fof(f153,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f44,f103,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f103,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f125,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f44,f99,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f99,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f104,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f90,f101,f97])).

fof(f90,plain,
    ( r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f64,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f41,f47,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(k5_xboole_0(sK0,X0),k2_xboole_0(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f42,f41,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f42,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f41,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f21,f40])).

fof(f40,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f21,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (19172)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (19195)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (19176)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (19172)Refutation not found, incomplete strategy% (19172)------------------------------
% 0.20/0.51  % (19172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19180)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (19172)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19172)Memory used [KB]: 10618
% 0.20/0.52  % (19172)Time elapsed: 0.103 s
% 0.20/0.52  % (19172)------------------------------
% 0.20/0.52  % (19172)------------------------------
% 0.20/0.53  % (19185)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.53  % (19192)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.53  % (19184)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.53  % (19175)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.54  % (19178)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.26/0.54  % (19174)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.54  % (19171)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.54  % (19174)Refutation found. Thanks to Tanya!
% 1.26/0.54  % SZS status Theorem for theBenchmark
% 1.26/0.54  % SZS output start Proof for theBenchmark
% 1.26/0.54  fof(f154,plain,(
% 1.26/0.54    $false),
% 1.26/0.54    inference(avatar_sat_refutation,[],[f104,f125,f153])).
% 1.26/0.54  fof(f153,plain,(
% 1.26/0.54    ~spl2_2),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f137])).
% 1.26/0.54  fof(f137,plain,(
% 1.26/0.54    $false | ~spl2_2),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f44,f103,f25])).
% 1.26/0.54  fof(f25,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f18])).
% 1.26/0.54  fof(f18,plain,(
% 1.26/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.26/0.54    inference(ennf_transformation,[],[f14])).
% 1.26/0.54  fof(f14,axiom,(
% 1.26/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.26/0.54  fof(f103,plain,(
% 1.26/0.54    r2_hidden(sK0,sK0) | ~spl2_2),
% 1.26/0.54    inference(avatar_component_clause,[],[f101])).
% 1.26/0.54  fof(f101,plain,(
% 1.26/0.54    spl2_2 <=> r2_hidden(sK0,sK0)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.26/0.54  fof(f44,plain,(
% 1.26/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.26/0.54    inference(equality_resolution,[],[f31])).
% 1.26/0.54  fof(f31,plain,(
% 1.26/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.26/0.54    inference(cnf_transformation,[],[f3])).
% 1.26/0.54  fof(f3,axiom,(
% 1.26/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.26/0.54  fof(f125,plain,(
% 1.26/0.54    spl2_1),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f108])).
% 1.26/0.54  fof(f108,plain,(
% 1.26/0.54    $false | spl2_1),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f44,f99,f23])).
% 1.26/0.54  fof(f23,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f11])).
% 1.26/0.54  fof(f11,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.26/0.54  fof(f99,plain,(
% 1.26/0.54    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | spl2_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f97])).
% 1.26/0.54  fof(f97,plain,(
% 1.26/0.54    spl2_1 <=> r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.26/0.54  fof(f104,plain,(
% 1.26/0.54    ~spl2_1 | spl2_2),
% 1.26/0.54    inference(avatar_split_clause,[],[f90,f101,f97])).
% 1.26/0.54  fof(f90,plain,(
% 1.26/0.54    r2_hidden(sK0,sK0) | ~r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 1.26/0.54    inference(resolution,[],[f64,f38])).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f20])).
% 1.26/0.54  fof(f20,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.26/0.54    inference(ennf_transformation,[],[f2])).
% 1.26/0.54  fof(f2,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.26/0.54  fof(f64,plain,(
% 1.26/0.54    ~r2_hidden(sK0,k5_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f41,f47,f39])).
% 1.26/0.54  fof(f39,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f20])).
% 1.26/0.54  fof(f47,plain,(
% 1.26/0.54    ( ! [X0] : (~r2_hidden(sK0,k5_xboole_0(k5_xboole_0(sK0,X0),k2_xboole_0(sK0,X0)))) )),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f42,f41,f26])).
% 1.26/0.54  fof(f26,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f19])).
% 1.26/0.54  fof(f19,plain,(
% 1.26/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f1])).
% 1.26/0.54  fof(f1,axiom,(
% 1.26/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.26/0.54  fof(f42,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k2_xboole_0(X0,X2))) )),
% 1.26/0.54    inference(definition_unfolding,[],[f30,f34])).
% 1.26/0.54  fof(f34,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f5])).
% 1.26/0.54  fof(f5,axiom,(
% 1.26/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.26/0.54  fof(f30,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f4])).
% 1.26/0.54  fof(f4,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 1.26/0.54  fof(f41,plain,(
% 1.26/0.54    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 1.26/0.54    inference(definition_unfolding,[],[f21,f40])).
% 1.26/0.54  fof(f40,plain,(
% 1.26/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 1.26/0.54    inference(definition_unfolding,[],[f29,f35])).
% 1.26/0.54  fof(f35,plain,(
% 1.26/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f6])).
% 1.26/0.54  fof(f6,axiom,(
% 1.26/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.26/0.54  fof(f29,plain,(
% 1.26/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f13])).
% 1.26/0.54  fof(f13,axiom,(
% 1.26/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.26/0.54  fof(f21,plain,(
% 1.26/0.54    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 1.26/0.54    inference(cnf_transformation,[],[f17])).
% 1.26/0.54  fof(f17,plain,(
% 1.26/0.54    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0))),
% 1.26/0.54    inference(ennf_transformation,[],[f16])).
% 1.26/0.54  fof(f16,negated_conjecture,(
% 1.26/0.54    ~! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.26/0.54    inference(negated_conjecture,[],[f15])).
% 1.26/0.54  fof(f15,conjecture,(
% 1.26/0.54    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (19174)------------------------------
% 1.26/0.54  % (19174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (19174)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (19174)Memory used [KB]: 6268
% 1.26/0.54  % (19174)Time elapsed: 0.125 s
% 1.26/0.54  % (19174)------------------------------
% 1.26/0.54  % (19174)------------------------------
% 1.26/0.54  % (19169)Success in time 0.178 s
%------------------------------------------------------------------------------
