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
% DateTime   : Thu Dec  3 12:53:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 132 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  180 ( 339 expanded)
%              Number of equality atoms :   20 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f212,f263])).

fof(f263,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f254,f245])).

fof(f245,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f219,f220])).

fof(f220,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f79,f113])).

fof(f113,plain,(
    ! [X4] :
      ( ~ sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,X4))
      | r1_xboole_0(k2_relat_1(sK1),X4) ) ),
    inference(resolution,[],[f67,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | sQ4_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f67,plain,(
    ! [X1] :
      ( ~ sQ4_eqProxy(k10_relat_1(sK1,X1),k1_xboole_0)
      | r1_xboole_0(k2_relat_1(sK1),X1) ) ),
    inference(resolution,[],[f19,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ sQ4_eqProxy(k10_relat_1(X1,X0),k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f26,f46])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f79,plain,
    ( sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_2
  <=> sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f219,plain,
    ( ! [X4] :
        ( ~ r1_xboole_0(k2_relat_1(sK1),X4)
        | ~ r2_hidden(sK0,X4) )
    | ~ spl5_1 ),
    inference(resolution,[],[f74,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f74,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f254,plain,
    ( r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f216,f45])).

fof(f45,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f216,plain,
    ( ! [X2] :
        ( r2_hidden(sK0,k4_xboole_0(k2_relat_1(sK1),X2))
        | r2_hidden(sK0,X2) )
    | ~ spl5_1 ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f212,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f208,f210])).

fof(f210,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f209,f178])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl5_1 ),
    inference(resolution,[],[f152,f22])).

fof(f152,plain,
    ( r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))
    | spl5_1 ),
    inference(resolution,[],[f107,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(k4_xboole_0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f27,f46])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f107,plain,
    ( sQ4_eqProxy(k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)),k1_tarski(sK0))
    | spl5_1 ),
    inference(resolution,[],[f84,f64])).

fof(f84,plain,
    ( sQ4_eqProxy(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)))
    | spl5_1 ),
    inference(resolution,[],[f75,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | sQ4_eqProxy(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) ) ),
    inference(equality_proxy_replacement,[],[f29,f46])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

% (19760)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f75,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f209,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k1_tarski(sK0))
    | spl5_2 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k1_tarski(sK0))
    | ~ r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl5_2 ),
    inference(resolution,[],[f116,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | sQ4_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f32,f46])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f116,plain,
    ( ~ sQ4_eqProxy(k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)),k2_relat_1(sK1))
    | spl5_2 ),
    inference(resolution,[],[f95,f56])).

fof(f95,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl5_2 ),
    inference(resolution,[],[f87,f66])).

fof(f66,plain,(
    ! [X0] :
      ( sQ4_eqProxy(k10_relat_1(sK1,X0),k1_xboole_0)
      | ~ r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f19,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | sQ4_eqProxy(k10_relat_1(X1,X0),k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f25,f46])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,
    ( ~ sQ4_eqProxy(k10_relat_1(sK1,k1_tarski(sK0)),k1_xboole_0)
    | spl5_2 ),
    inference(resolution,[],[f78,f64])).

fof(f78,plain,
    ( ~ sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f208,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl5_2 ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl5_2 ),
    inference(resolution,[],[f116,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sQ4_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f33,f46])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f52,f77,f73])).

fof(f52,plain,
    ( ~ sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0)))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f17,f46])).

fof(f17,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f51,f77,f73])).

fof(f51,plain,
    ( sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f18,f46])).

fof(f18,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:54:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (19742)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (19749)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (19748)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (19759)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (19751)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (19765)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (19759)Refutation not found, incomplete strategy% (19759)------------------------------
% 0.21/0.51  % (19759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19740)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19759)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19759)Memory used [KB]: 10746
% 0.21/0.51  % (19759)Time elapsed: 0.054 s
% 0.21/0.51  % (19759)------------------------------
% 0.21/0.51  % (19759)------------------------------
% 0.21/0.51  % (19741)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (19757)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (19738)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19749)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f80,f85,f212,f263])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f262])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f254,f245])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k1_tarski(sK0)) | (~spl5_1 | ~spl5_2)),
% 0.21/0.52    inference(resolution,[],[f219,f220])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f79,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X4] : (~sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,X4)) | r1_xboole_0(k2_relat_1(sK1),X4)) )),
% 0.21/0.52    inference(resolution,[],[f67,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sQ4_eqProxy(X0,X1) | sQ4_eqProxy(X1,X0)) )),
% 0.21/0.52    inference(equality_proxy_axiom,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.52    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X1] : (~sQ4_eqProxy(k10_relat_1(sK1,X1),k1_xboole_0) | r1_xboole_0(k2_relat_1(sK1),X1)) )),
% 0.21/0.52    inference(resolution,[],[f19,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k2_relat_1(X1),X0) | ~sQ4_eqProxy(k10_relat_1(X1,X0),k1_xboole_0)) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f26,f46])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0))) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl5_2 <=> sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    ( ! [X4] : (~r1_xboole_0(k2_relat_1(sK1),X4) | ~r2_hidden(sK0,X4)) ) | ~spl5_1),
% 0.21/0.52    inference(resolution,[],[f74,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl5_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    r2_hidden(sK0,k1_tarski(sK0)) | ~spl5_1),
% 0.21/0.52    inference(resolution,[],[f216,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(sK0,k4_xboole_0(k2_relat_1(sK1),X2)) | r2_hidden(sK0,X2)) ) | ~spl5_1),
% 0.21/0.52    inference(resolution,[],[f74,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    spl5_1 | spl5_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    $false | (spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f208,f210])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | (spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f152,f22])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f107,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sQ4_eqProxy(k4_xboole_0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f27,f46])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    sQ4_eqProxy(k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)),k1_tarski(sK0)) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f84,f64])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    sQ4_eqProxy(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f75,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | sQ4_eqProxy(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1))) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f29,f46])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  % (19760)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k1_tarski(sK0)) | spl5_2),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f202])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k1_tarski(sK0)) | ~r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | spl5_2),
% 0.21/0.52    inference(resolution,[],[f116,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | sQ4_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f32,f46])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ~sQ4_eqProxy(k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)),k2_relat_1(sK1)) | spl5_2),
% 0.21/0.52    inference(resolution,[],[f95,f56])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl5_2),
% 0.21/0.52    inference(resolution,[],[f87,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (sQ4_eqProxy(k10_relat_1(sK1,X0),k1_xboole_0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 0.21/0.52    inference(resolution,[],[f19,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | sQ4_eqProxy(k10_relat_1(X1,X0),k1_xboole_0)) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f25,f46])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~sQ4_eqProxy(k10_relat_1(sK1,k1_tarski(sK0)),k1_xboole_0) | spl5_2),
% 0.21/0.52    inference(resolution,[],[f78,f64])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0))) | spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | spl5_2),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f203])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | r2_hidden(sK3(k2_relat_1(sK1),k1_tarski(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | spl5_2),
% 0.21/0.52    inference(resolution,[],[f116,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | sQ4_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f33,f46])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl5_1 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f52,f77,f73])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0))) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f17,f46])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~spl5_1 | spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f77,f73])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    sQ4_eqProxy(k1_xboole_0,k10_relat_1(sK1,k1_tarski(sK0))) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f18,f46])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19749)------------------------------
% 0.21/0.53  % (19749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19756)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (19755)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (19737)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (19747)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (19743)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (19749)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19749)Memory used [KB]: 6268
% 0.21/0.53  % (19749)Time elapsed: 0.111 s
% 0.21/0.53  % (19749)------------------------------
% 0.21/0.53  % (19749)------------------------------
% 0.21/0.54  % (19735)Success in time 0.173 s
%------------------------------------------------------------------------------
