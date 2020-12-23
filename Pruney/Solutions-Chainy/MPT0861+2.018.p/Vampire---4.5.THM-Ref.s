%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  97 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 239 expanded)
%              Number of equality atoms :   26 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f55,f62,f216])).

fof(f216,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f14,f190,f41])).

fof(f41,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK0,X2),k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)),X3))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f14,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f190,plain,
    ( ! [X4,X5] : ~ r2_hidden(X4,X5)
    | spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f189,f128])).

fof(f128,plain,
    ( ! [X0] : ~ sQ4_eqProxy(k2_mcart_1(k4_tarski(X0,k1_mcart_1(sK0))),sK2)
    | spl5_2 ),
    inference(resolution,[],[f75,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | sQ4_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f75,plain,
    ( ! [X4] : ~ sQ4_eqProxy(sK2,k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))))
    | spl5_2 ),
    inference(resolution,[],[f57,f31])).

fof(f31,plain,(
    ! [X0,X1] : sQ4_eqProxy(k2_mcart_1(k4_tarski(X0,X1)),X1) ),
    inference(equality_proxy_replacement,[],[f18,f26])).

fof(f18,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

% (26769)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f57,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(X0,k1_mcart_1(sK0))
        | ~ sQ4_eqProxy(sK2,X0) )
    | spl5_2 ),
    inference(resolution,[],[f52,f37])).

% (26761)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (26756)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (26755)Refutation not found, incomplete strategy% (26755)------------------------------
% (26755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | ~ sQ4_eqProxy(X1,X2)
      | sQ4_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f26])).

fof(f52,plain,
    ( ~ sQ4_eqProxy(sK2,k1_mcart_1(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_2
  <=> sQ4_eqProxy(sK2,k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f189,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,X5)
        | sQ4_eqProxy(k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))),sK2) )
    | spl5_3 ),
    inference(subsumption_resolution,[],[f185,f135])).

fof(f135,plain,
    ( ! [X0] : ~ sQ4_eqProxy(k2_mcart_1(k4_tarski(X0,k1_mcart_1(sK0))),sK1)
    | spl5_3 ),
    inference(resolution,[],[f83,f36])).

fof(f83,plain,
    ( ! [X4] : ~ sQ4_eqProxy(sK1,k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))))
    | spl5_3 ),
    inference(resolution,[],[f64,f31])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(X0,k1_mcart_1(sK0))
        | ~ sQ4_eqProxy(sK1,X0) )
    | spl5_3 ),
    inference(resolution,[],[f61,f37])).

fof(f61,plain,
    ( ~ sQ4_eqProxy(sK1,k1_mcart_1(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_3
  <=> sQ4_eqProxy(sK1,k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f185,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | sQ4_eqProxy(k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))),sK1)
      | sQ4_eqProxy(k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))),sK2) ) ),
    inference(resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
      | sQ4_eqProxy(k2_mcart_1(X0),X2)
      | sQ4_eqProxy(k2_mcart_1(X0),X3) ) ),
    inference(equality_proxy_replacement,[],[f21,f26,f26])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,k1_mcart_1(sK0)),k2_zfmisc_1(X1,k2_tarski(sK1,sK2)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f38,f25])).

fof(f38,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f14,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f14,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f62,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f29,f59,f46])).

fof(f46,plain,
    ( spl5_1
  <=> sQ4_eqProxy(sK3,k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f29,plain,
    ( ~ sQ4_eqProxy(sK1,k1_mcart_1(sK0))
    | ~ sQ4_eqProxy(sK3,k2_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f12,f26,f26])).

fof(f12,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f48,f42])).

fof(f42,plain,(
    sQ4_eqProxy(sK3,k2_mcart_1(sK0)) ),
    inference(resolution,[],[f39,f36])).

fof(f39,plain,(
    sQ4_eqProxy(k2_mcart_1(sK0),sK3) ),
    inference(resolution,[],[f14,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | sQ4_eqProxy(k2_mcart_1(X0),X2) ) ),
    inference(equality_proxy_replacement,[],[f20,f26])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,
    ( ~ sQ4_eqProxy(sK3,k2_mcart_1(sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f53,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f28,f50,f46])).

fof(f28,plain,
    ( ~ sQ4_eqProxy(sK2,k1_mcart_1(sK0))
    | ~ sQ4_eqProxy(sK3,k2_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f13,f26,f26])).

fof(f13,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (26751)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (26748)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (26759)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (26749)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (26757)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (26759)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (26755)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f217,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f53,f55,f62,f216])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    spl5_2 | spl5_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f197])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    $false | (spl5_2 | spl5_3)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f14,f190,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK0,X2),k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)),X3)) | ~r2_hidden(X2,X3)) )),
% 0.20/0.52    inference(resolution,[],[f14,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    ( ! [X4,X5] : (~r2_hidden(X4,X5)) ) | (spl5_2 | spl5_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f189,f128])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ( ! [X0] : (~sQ4_eqProxy(k2_mcart_1(k4_tarski(X0,k1_mcart_1(sK0))),sK2)) ) | spl5_2),
% 0.20/0.52    inference(resolution,[],[f75,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sQ4_eqProxy(X0,X1) | sQ4_eqProxy(X1,X0)) )),
% 0.20/0.52    inference(equality_proxy_axiom,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.52    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X4] : (~sQ4_eqProxy(sK2,k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))))) ) | spl5_2),
% 0.20/0.52    inference(resolution,[],[f57,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sQ4_eqProxy(k2_mcart_1(k4_tarski(X0,X1)),X1)) )),
% 0.20/0.52    inference(equality_proxy_replacement,[],[f18,f26])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  % (26769)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0] : (~sQ4_eqProxy(X0,k1_mcart_1(sK0)) | ~sQ4_eqProxy(sK2,X0)) ) | spl5_2),
% 0.20/0.52    inference(resolution,[],[f52,f37])).
% 0.20/0.52  % (26761)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (26756)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (26755)Refutation not found, incomplete strategy% (26755)------------------------------
% 0.20/0.52  % (26755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sQ4_eqProxy(X0,X1) | ~sQ4_eqProxy(X1,X2) | sQ4_eqProxy(X0,X2)) )),
% 0.20/0.52    inference(equality_proxy_axiom,[],[f26])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ~sQ4_eqProxy(sK2,k1_mcart_1(sK0)) | spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    spl5_2 <=> sQ4_eqProxy(sK2,k1_mcart_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    ( ! [X4,X5] : (~r2_hidden(X4,X5) | sQ4_eqProxy(k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))),sK2)) ) | spl5_3),
% 0.20/0.52    inference(subsumption_resolution,[],[f185,f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    ( ! [X0] : (~sQ4_eqProxy(k2_mcart_1(k4_tarski(X0,k1_mcart_1(sK0))),sK1)) ) | spl5_3),
% 0.20/0.52    inference(resolution,[],[f83,f36])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X4] : (~sQ4_eqProxy(sK1,k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))))) ) | spl5_3),
% 0.20/0.52    inference(resolution,[],[f64,f31])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0] : (~sQ4_eqProxy(X0,k1_mcart_1(sK0)) | ~sQ4_eqProxy(sK1,X0)) ) | spl5_3),
% 0.20/0.52    inference(resolution,[],[f61,f37])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ~sQ4_eqProxy(sK1,k1_mcart_1(sK0)) | spl5_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl5_3 <=> sQ4_eqProxy(sK1,k1_mcart_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    ( ! [X4,X5] : (~r2_hidden(X4,X5) | sQ4_eqProxy(k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))),sK1) | sQ4_eqProxy(k2_mcart_1(k4_tarski(X4,k1_mcart_1(sK0))),sK2)) )),
% 0.20/0.52    inference(resolution,[],[f69,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) | sQ4_eqProxy(k2_mcart_1(X0),X2) | sQ4_eqProxy(k2_mcart_1(X0),X3)) )),
% 0.20/0.52    inference(equality_proxy_replacement,[],[f21,f26,f26])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,k1_mcart_1(sK0)),k2_zfmisc_1(X1,k2_tarski(sK1,sK2))) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(resolution,[],[f38,f25])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))),
% 0.20/0.52    inference(resolution,[],[f14,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ~spl5_1 | ~spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f29,f59,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    spl5_1 <=> sQ4_eqProxy(sK3,k2_mcart_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~sQ4_eqProxy(sK1,k1_mcart_1(sK0)) | ~sQ4_eqProxy(sK3,k2_mcart_1(sK0))),
% 0.20/0.52    inference(equality_proxy_replacement,[],[f12,f26,f26])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    sK1 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    spl5_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    $false | spl5_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f48,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    sQ4_eqProxy(sK3,k2_mcart_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f39,f36])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    sQ4_eqProxy(k2_mcart_1(sK0),sK3)),
% 0.20/0.52    inference(resolution,[],[f14,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | sQ4_eqProxy(k2_mcart_1(X0),X2)) )),
% 0.20/0.52    inference(equality_proxy_replacement,[],[f20,f26])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | k2_mcart_1(X0) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ~sQ4_eqProxy(sK3,k2_mcart_1(sK0)) | spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f46])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ~spl5_1 | ~spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f50,f46])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ~sQ4_eqProxy(sK2,k1_mcart_1(sK0)) | ~sQ4_eqProxy(sK3,k2_mcart_1(sK0))),
% 0.20/0.52    inference(equality_proxy_replacement,[],[f13,f26,f26])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    sK2 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (26759)------------------------------
% 0.20/0.52  % (26759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26759)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (26759)Memory used [KB]: 6268
% 0.20/0.52  % (26759)Time elapsed: 0.105 s
% 0.20/0.52  % (26759)------------------------------
% 0.20/0.52  % (26759)------------------------------
% 0.20/0.52  % (26756)Refutation not found, incomplete strategy% (26756)------------------------------
% 0.20/0.52  % (26756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26756)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26756)Memory used [KB]: 10618
% 0.20/0.52  % (26756)Time elapsed: 0.118 s
% 0.20/0.52  % (26756)------------------------------
% 0.20/0.52  % (26756)------------------------------
% 0.20/0.53  % (26739)Success in time 0.166 s
%------------------------------------------------------------------------------
