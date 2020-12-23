%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 129 expanded)
%              Number of leaves         :   10 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 303 expanded)
%              Number of equality atoms :   25 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10545)Refutation not found, incomplete strategy% (10545)------------------------------
% (10545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f210,f369])).

fof(f369,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f73,f230,f231,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f231,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))
    | spl10_2 ),
    inference(subsumption_resolution,[],[f226,f230])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK0),sK0) )
    | spl10_2 ),
    inference(resolution,[],[f218,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | sQ9_eqProxy(k1_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f24,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

% (10555)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f218,plain,
    ( ~ sQ9_eqProxy(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0)
    | spl10_2 ),
    inference(resolution,[],[f65,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ sQ9_eqProxy(X0,X1)
      | sQ9_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f38])).

fof(f65,plain,
    ( ~ sQ9_eqProxy(sK0,k1_relat_1(k2_zfmisc_1(sK0,sK1)))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl10_2
  <=> sQ9_eqProxy(sK0,k1_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f230,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f225,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f225,plain,
    ( r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK0),sK5(k2_zfmisc_1(sK0,sK1),sK0)),k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl10_2 ),
    inference(resolution,[],[f218,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | sQ9_eqProxy(k1_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f23,f38])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    r2_hidden(sK2(sK1,k1_xboole_0),sK1) ),
    inference(resolution,[],[f53,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f53,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f50,f14])).

fof(f14,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(resolution,[],[f39,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | sQ9_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f17,f38])).

% (10545)Termination reason: Refutation not found, incomplete strategy

% (10545)Memory used [KB]: 10618
% (10545)Time elapsed: 0.125 s
% (10545)------------------------------
% (10545)------------------------------
fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f39,plain,(
    ~ sQ9_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f13,f38])).

fof(f13,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f210,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f78,f95,f96,f31])).

fof(f96,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f91,f95])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),sK1),sK1) )
    | spl10_1 ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | sQ9_eqProxy(k2_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f28,f38])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f68,plain,
    ( ~ sQ9_eqProxy(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)
    | spl10_1 ),
    inference(resolution,[],[f61,f48])).

fof(f61,plain,
    ( ~ sQ9_eqProxy(sK1,k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl10_1
  <=> sQ9_eqProxy(sK1,k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f95,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),sK1),sK1)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,
    ( r2_hidden(k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK1),sK6(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),sK1),sK1)
    | spl10_1 ),
    inference(resolution,[],[f68,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | sQ9_eqProxy(k2_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f27,f38])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    r2_hidden(sK2(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f57,f19])).

fof(f57,plain,(
    ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f54,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(resolution,[],[f40,f42])).

fof(f40,plain,(
    ~ sQ9_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f12,f38])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

% (10553)Refutation not found, incomplete strategy% (10553)------------------------------
% (10553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f66,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f41,f63,f59])).

fof(f41,plain,
    ( ~ sQ9_eqProxy(sK0,k1_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ sQ9_eqProxy(sK1,k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f11,f38,f38])).

fof(f11,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:29:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (10549)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (10566)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (10550)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (10572)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (10558)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (10565)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (10554)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (10545)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (10569)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (10564)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (10551)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (10556)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (10570)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (10565)Refutation not found, incomplete strategy% (10565)------------------------------
% 0.22/0.54  % (10565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10543)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (10553)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (10557)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (10547)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (10556)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (10544)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (10551)Refutation not found, incomplete strategy% (10551)------------------------------
% 0.22/0.54  % (10551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10551)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10551)Memory used [KB]: 10618
% 0.22/0.54  % (10551)Time elapsed: 0.126 s
% 0.22/0.54  % (10551)------------------------------
% 0.22/0.54  % (10551)------------------------------
% 0.22/0.54  % (10563)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (10571)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (10561)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  % (10545)Refutation not found, incomplete strategy% (10545)------------------------------
% 0.22/0.55  % (10545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  fof(f371,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f66,f210,f369])).
% 0.22/0.55  fof(f369,plain,(
% 0.22/0.55    spl10_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f362])).
% 0.22/0.55  fof(f362,plain,(
% 0.22/0.55    $false | spl10_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f73,f230,f231,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.55  fof(f231,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))) ) | spl10_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f226,f230])).
% 0.22/0.55  fof(f226,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK0),sK0)) ) | spl10_2),
% 0.22/0.55    inference(resolution,[],[f218,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1) | sQ9_eqProxy(k1_relat_1(X0),X1)) )),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f24,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X1,X0] : (sQ9_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.55    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).
% 0.22/0.55  % (10555)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.55  fof(f218,plain,(
% 0.22/0.55    ~sQ9_eqProxy(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0) | spl10_2),
% 0.22/0.55    inference(resolution,[],[f65,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~sQ9_eqProxy(X0,X1) | sQ9_eqProxy(X1,X0)) )),
% 0.22/0.55    inference(equality_proxy_axiom,[],[f38])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ~sQ9_eqProxy(sK0,k1_relat_1(k2_zfmisc_1(sK0,sK1))) | spl10_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    spl10_2 <=> sQ9_eqProxy(sK0,k1_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.55  fof(f230,plain,(
% 0.22/0.55    r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK0),sK0) | spl10_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f225,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f225,plain,(
% 0.22/0.55    r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK0),sK5(k2_zfmisc_1(sK0,sK1),sK0)),k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK0),sK0) | spl10_2),
% 0.22/0.55    inference(resolution,[],[f218,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | sQ9_eqProxy(k1_relat_1(X0),X1)) )),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f23,f38])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    r2_hidden(sK2(sK1,k1_xboole_0),sK1)),
% 0.22/0.55    inference(resolution,[],[f53,f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ~r1_tarski(sK1,k1_xboole_0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f50,f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,sK1) | ~r1_tarski(sK1,k1_xboole_0)),
% 0.22/0.55    inference(resolution,[],[f39,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | sQ9_eqProxy(X0,X1)) )),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f17,f38])).
% 0.22/0.55  % (10545)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10545)Memory used [KB]: 10618
% 0.22/0.55  % (10545)Time elapsed: 0.125 s
% 0.22/0.55  % (10545)------------------------------
% 0.22/0.55  % (10545)------------------------------
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ~sQ9_eqProxy(k1_xboole_0,sK1)),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f13,f38])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    inference(negated_conjecture,[],[f7])).
% 0.22/0.55  fof(f7,conjecture,(
% 0.22/0.55    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    spl10_1),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    $false | spl10_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f78,f95,f96,f31])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))) ) | spl10_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f91,f95])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),sK1),sK1)) ) | spl10_1),
% 0.22/0.55    inference(resolution,[],[f68,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1) | sQ9_eqProxy(k2_relat_1(X0),X1)) )),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f28,f38])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ~sQ9_eqProxy(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1) | spl10_1),
% 0.22/0.55    inference(resolution,[],[f61,f48])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ~sQ9_eqProxy(sK1,k2_relat_1(k2_zfmisc_1(sK0,sK1))) | spl10_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    spl10_1 <=> sQ9_eqProxy(sK1,k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),sK1),sK1) | spl10_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f90,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    r2_hidden(k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK1),sK6(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),sK1),sK1) | spl10_1),
% 0.22/0.55    inference(resolution,[],[f68,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1) | sQ9_eqProxy(k2_relat_1(X0),X1)) )),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f27,f38])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    r2_hidden(sK2(sK0,k1_xboole_0),sK0)),
% 0.22/0.55    inference(resolution,[],[f57,f19])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ~r1_tarski(sK0,k1_xboole_0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f54,f14])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,sK0) | ~r1_tarski(sK0,k1_xboole_0)),
% 0.22/0.55    inference(resolution,[],[f40,f42])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ~sQ9_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f12,f38])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    k1_xboole_0 != sK0),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  % (10553)Refutation not found, incomplete strategy% (10553)------------------------------
% 0.22/0.55  % (10553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ~spl10_1 | ~spl10_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f41,f63,f59])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ~sQ9_eqProxy(sK0,k1_relat_1(k2_zfmisc_1(sK0,sK1))) | ~sQ9_eqProxy(sK1,k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f11,f38,f38])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (10556)------------------------------
% 0.22/0.55  % (10556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10556)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (10556)Memory used [KB]: 6396
% 0.22/0.55  % (10556)Time elapsed: 0.120 s
% 0.22/0.55  % (10556)------------------------------
% 0.22/0.55  % (10556)------------------------------
% 0.22/0.55  % (10553)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10553)Memory used [KB]: 10618
% 0.22/0.55  % (10553)Time elapsed: 0.128 s
% 0.22/0.55  % (10553)------------------------------
% 0.22/0.55  % (10553)------------------------------
% 0.22/0.55  % (10567)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (10560)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (10542)Success in time 0.179 s
%------------------------------------------------------------------------------
