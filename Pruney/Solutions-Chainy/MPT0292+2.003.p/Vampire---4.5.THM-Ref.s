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
% DateTime   : Thu Dec  3 12:41:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 (  99 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f174,f195])).

fof(f195,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f188,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
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

fof(f188,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_2 ),
    inference(resolution,[],[f182,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f182,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl6_2 ),
    inference(resolution,[],[f160,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f160,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k1_zfmisc_1(sK0)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_2
  <=> r1_tarski(sK0,k3_tarski(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f174,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f170,f162])).

fof(f162,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0))
    | spl6_1 ),
    inference(resolution,[],[f156,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f156,plain,
    ( ~ r1_tarski(k3_tarski(k1_zfmisc_1(sK0)),sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_1
  <=> r1_tarski(k3_tarski(k1_zfmisc_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f170,plain,
    ( ~ r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0))
    | spl6_1 ),
    inference(resolution,[],[f163,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f163,plain,
    ( ~ r1_tarski(sK1(k1_zfmisc_1(sK0),sK0),sK0)
    | spl6_1 ),
    inference(resolution,[],[f156,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f161,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f119,f158,f154])).

fof(f119,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ r1_tarski(k3_tarski(k1_zfmisc_1(sK0)),sK0) ),
    inference(resolution,[],[f98,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | sQ5_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f55,f94])).

fof(f94,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f98,plain,(
    ~ sQ5_eqProxy(sK0,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f37,f94])).

fof(f37,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (17744)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (17737)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (17737)Refutation not found, incomplete strategy% (17737)------------------------------
% 0.20/0.50  % (17737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (17749)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (17757)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (17737)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (17737)Memory used [KB]: 1663
% 0.20/0.50  % (17737)Time elapsed: 0.083 s
% 0.20/0.50  % (17737)------------------------------
% 0.20/0.50  % (17737)------------------------------
% 0.20/0.50  % (17739)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (17741)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (17763)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (17759)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (17757)Refutation not found, incomplete strategy% (17757)------------------------------
% 0.20/0.51  % (17757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17757)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17757)Memory used [KB]: 10746
% 0.20/0.51  % (17757)Time elapsed: 0.099 s
% 0.20/0.51  % (17757)------------------------------
% 0.20/0.51  % (17757)------------------------------
% 0.20/0.51  % (17759)Refutation not found, incomplete strategy% (17759)------------------------------
% 0.20/0.51  % (17759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17759)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17759)Memory used [KB]: 10746
% 0.20/0.51  % (17759)Time elapsed: 0.069 s
% 0.20/0.51  % (17759)------------------------------
% 0.20/0.51  % (17759)------------------------------
% 0.20/0.51  % (17755)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (17762)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (17765)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (17750)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (17750)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f161,f174,f195])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    spl6_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    $false | spl6_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f188,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ~r1_tarski(sK0,sK0) | spl6_2),
% 0.20/0.52    inference(resolution,[],[f182,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(equality_resolution,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl6_2),
% 0.20/0.52    inference(resolution,[],[f160,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    ~r1_tarski(sK0,k3_tarski(k1_zfmisc_1(sK0))) | spl6_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f158])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    spl6_2 <=> r1_tarski(sK0,k3_tarski(k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    spl6_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    $false | spl6_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f170,f162])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0)) | spl6_1),
% 0.20/0.52    inference(resolution,[],[f156,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,axiom,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ~r1_tarski(k3_tarski(k1_zfmisc_1(sK0)),sK0) | spl6_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f154])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    spl6_1 <=> r1_tarski(k3_tarski(k1_zfmisc_1(sK0)),sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    ~r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0)) | spl6_1),
% 0.20/0.52    inference(resolution,[],[f163,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(equality_resolution,[],[f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    ~r1_tarski(sK1(k1_zfmisc_1(sK0),sK0),sK0) | spl6_1),
% 0.20/0.52    inference(resolution,[],[f156,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(sK1(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    ~spl6_1 | ~spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f119,f158,f154])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ~r1_tarski(sK0,k3_tarski(k1_zfmisc_1(sK0))) | ~r1_tarski(k3_tarski(k1_zfmisc_1(sK0)),sK0)),
% 0.20/0.52    inference(resolution,[],[f98,f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | sQ5_eqProxy(X0,X1)) )),
% 0.20/0.52    inference(equality_proxy_replacement,[],[f55,f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.52    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ~sQ5_eqProxy(sK0,k3_tarski(k1_zfmisc_1(sK0)))),
% 0.20/0.52    inference(equality_proxy_replacement,[],[f37,f94])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    sK0 != k3_tarski(k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0),
% 0.20/0.52    inference(ennf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,negated_conjecture,(
% 0.20/0.52    ~! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.52    inference(negated_conjecture,[],[f23])).
% 0.20/0.52  fof(f23,conjecture,(
% 0.20/0.52    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (17750)------------------------------
% 0.20/0.52  % (17750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17750)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (17750)Memory used [KB]: 6268
% 0.20/0.52  % (17750)Time elapsed: 0.108 s
% 0.20/0.52  % (17750)------------------------------
% 0.20/0.52  % (17750)------------------------------
% 0.20/0.52  % (17751)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (17754)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (17736)Success in time 0.166 s
%------------------------------------------------------------------------------
