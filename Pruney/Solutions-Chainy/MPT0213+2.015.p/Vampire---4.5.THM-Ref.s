%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  60 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 137 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f215,f241])).

fof(f241,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f236,f37])).

fof(f37,plain,(
    ! [X0] : sQ5_eqProxy(k4_xboole_0(X0,k1_xboole_0),X0) ),
    inference(equality_proxy_replacement,[],[f16,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f236,plain,
    ( ~ sQ5_eqProxy(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_1 ),
    inference(resolution,[],[f217,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sQ5_eqProxy(k4_xboole_0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f22,f33])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f217,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_1 ),
    inference(resolution,[],[f173,f115])).

fof(f115,plain,
    ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_1
  <=> r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f173,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X4)
        | ~ r1_xboole_0(X4,k1_xboole_0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f115,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f215,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f210,f37])).

fof(f210,plain,
    ( ~ sQ5_eqProxy(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f206,f40])).

fof(f206,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f124,f119])).

fof(f119,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_2
  <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f124,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4(k1_xboole_0,k1_xboole_0),X3)
        | ~ r1_xboole_0(X3,k1_xboole_0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f119,f19])).

fof(f120,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f52,f117,f113])).

fof(f52,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f48,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | sQ5_eqProxy(k3_tarski(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f26,f33])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f48,plain,(
    ~ sQ5_eqProxy(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ sQ5_eqProxy(X0,X1)
      | sQ5_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f33])).

fof(f35,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,k3_tarski(k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f14,f33])).

fof(f14,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f9])).

fof(f9,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (17992)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (17999)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (17999)Refutation not found, incomplete strategy% (17999)------------------------------
% 0.21/0.54  % (17999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17991)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (18007)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (17992)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (17999)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17999)Memory used [KB]: 10618
% 0.21/0.55  % (17999)Time elapsed: 0.114 s
% 0.21/0.55  % (17999)------------------------------
% 0.21/0.55  % (17999)------------------------------
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f242,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f120,f215,f241])).
% 0.21/0.55  fof(f241,plain,(
% 0.21/0.55    ~spl6_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f240])).
% 0.21/0.55  fof(f240,plain,(
% 0.21/0.55    $false | ~spl6_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f236,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0] : (sQ5_eqProxy(k4_xboole_0(X0,k1_xboole_0),X0)) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f16,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.55    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_1),
% 0.21/0.55    inference(resolution,[],[f217,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sQ5_eqProxy(k4_xboole_0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f22,f33])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_1),
% 0.21/0.55    inference(resolution,[],[f173,f115])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f113])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    spl6_1 <=> r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.55  fof(f173,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X4) | ~r1_xboole_0(X4,k1_xboole_0)) ) | ~spl6_1),
% 0.21/0.55    inference(resolution,[],[f115,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.55  fof(f215,plain,(
% 0.21/0.55    ~spl6_2),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f214])).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    $false | ~spl6_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f210,f37])).
% 0.21/0.55  fof(f210,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f206,f40])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f124,f119])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f117])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    spl6_2 <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(sK4(k1_xboole_0,k1_xboole_0),X3) | ~r1_xboole_0(X3,k1_xboole_0)) ) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f119,f19])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    spl6_1 | spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f52,f117,f113])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.55    inference(resolution,[],[f48,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1) | sQ5_eqProxy(k3_tarski(X0),X1)) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f26,f33])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k3_tarski(k1_xboole_0),k1_xboole_0)),
% 0.21/0.55    inference(resolution,[],[f35,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sQ5_eqProxy(X0,X1) | sQ5_eqProxy(X1,X0)) )),
% 0.21/0.55    inference(equality_proxy_axiom,[],[f33])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k1_xboole_0,k3_tarski(k1_xboole_0))),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f14,f33])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.55    inference(flattening,[],[f9])).
% 0.21/0.55  fof(f9,negated_conjecture,(
% 0.21/0.55    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.55    inference(negated_conjecture,[],[f8])).
% 0.21/0.55  fof(f8,conjecture,(
% 0.21/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (17979)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (17992)------------------------------
% 0.21/0.55  % (17992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17992)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (17992)Memory used [KB]: 6268
% 0.21/0.55  % (17992)Time elapsed: 0.130 s
% 0.21/0.55  % (17992)------------------------------
% 0.21/0.55  % (17992)------------------------------
% 0.21/0.56  % (17978)Success in time 0.192 s
%------------------------------------------------------------------------------
