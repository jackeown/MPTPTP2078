%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:13 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 110 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f195,f204,f206])).

fof(f206,plain,
    ( ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f190,f194])).

fof(f194,plain,
    ( ! [X2] : ~ r2_hidden(sK0,X2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_5
  <=> ! [X2] : ~ r2_hidden(sK0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f190,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f204,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f201,f117])).

fof(f117,plain,(
    ~ sQ5_eqProxy(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK1)) ),
    inference(resolution,[],[f110,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ sQ5_eqProxy(k4_xboole_0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f29,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f110,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(resolution,[],[f94,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | sQ5_eqProxy(k2_xboole_0(k4_xboole_0(X2,X0),X1),k4_xboole_0(k2_xboole_0(X2,X1),X0)) ) ),
    inference(equality_proxy_replacement,[],[f35,f58])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f94,plain,(
    ~ sQ5_eqProxy(k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)),k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1))) ),
    inference(resolution,[],[f64,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ sQ5_eqProxy(X0,X1)
      | sQ5_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f64,plain,(
    ~ sQ5_eqProxy(k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)),k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))) ),
    inference(equality_proxy_replacement,[],[f22,f58])).

fof(f22,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f201,plain,
    ( sQ5_eqProxy(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK1))
    | spl6_4 ),
    inference(resolution,[],[f191,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | sQ5_eqProxy(k4_xboole_0(X0,k1_tarski(X1)),X0) ) ),
    inference(equality_proxy_replacement,[],[f30,f58])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f191,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f189])).

fof(f195,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f102,f193,f189])).

fof(f102,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK0,X2)
      | ~ r2_hidden(sK0,k1_tarski(sK1)) ) ),
    inference(resolution,[],[f84,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f84,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k4_xboole_0(X0,k1_tarski(sK1)))
      | ~ r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f65,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sQ5_eqProxy(X0,X2)
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(equality_proxy_replacement,[],[f50,f58])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f65,plain,(
    ~ sQ5_eqProxy(sK0,sK1) ),
    inference(equality_proxy_replacement,[],[f21,f58])).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (1865)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (1890)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.48  % (1863)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % (1863)Refutation not found, incomplete strategy% (1863)------------------------------
% 0.20/0.48  % (1863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1863)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (1863)Memory used [KB]: 10746
% 0.20/0.48  % (1863)Time elapsed: 0.096 s
% 0.20/0.48  % (1863)------------------------------
% 0.20/0.48  % (1863)------------------------------
% 0.20/0.49  % (1873)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (1865)Refutation not found, incomplete strategy% (1865)------------------------------
% 0.20/0.49  % (1865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1865)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1865)Memory used [KB]: 6140
% 0.20/0.49  % (1865)Time elapsed: 0.086 s
% 0.20/0.49  % (1865)------------------------------
% 0.20/0.49  % (1865)------------------------------
% 0.20/0.50  % (1864)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (1870)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (1866)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (1887)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (1879)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (1883)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (1888)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (1862)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.52  % (1868)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.52  % (1869)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.52  % (1881)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.53  % (1869)Refutation not found, incomplete strategy% (1869)------------------------------
% 1.27/0.53  % (1869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (1874)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.53  % (1881)Refutation not found, incomplete strategy% (1881)------------------------------
% 1.27/0.53  % (1881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (1881)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (1881)Memory used [KB]: 10746
% 1.27/0.53  % (1881)Time elapsed: 0.111 s
% 1.27/0.53  % (1881)------------------------------
% 1.27/0.53  % (1881)------------------------------
% 1.27/0.53  % (1869)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (1869)Memory used [KB]: 10746
% 1.27/0.53  % (1869)Time elapsed: 0.125 s
% 1.27/0.53  % (1869)------------------------------
% 1.27/0.53  % (1869)------------------------------
% 1.27/0.53  % (1872)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.53  % (1861)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (1884)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.53  % (1867)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (1880)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.53  % (1871)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.53  % (1871)Refutation not found, incomplete strategy% (1871)------------------------------
% 1.27/0.53  % (1871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (1871)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (1871)Memory used [KB]: 10618
% 1.27/0.53  % (1871)Time elapsed: 0.144 s
% 1.27/0.53  % (1871)------------------------------
% 1.27/0.53  % (1871)------------------------------
% 1.27/0.53  % (1885)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.54  % (1875)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.54  % (1886)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % (1882)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.54  % (1882)Refutation not found, incomplete strategy% (1882)------------------------------
% 1.27/0.54  % (1882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (1882)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (1882)Memory used [KB]: 1663
% 1.27/0.54  % (1882)Time elapsed: 0.141 s
% 1.27/0.54  % (1882)------------------------------
% 1.27/0.54  % (1882)------------------------------
% 1.27/0.54  % (1886)Refutation not found, incomplete strategy% (1886)------------------------------
% 1.27/0.54  % (1886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (1886)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (1886)Memory used [KB]: 6268
% 1.27/0.54  % (1886)Time elapsed: 0.140 s
% 1.27/0.54  % (1886)------------------------------
% 1.27/0.54  % (1886)------------------------------
% 1.27/0.54  % (1876)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.54  % (1891)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.54  % (1874)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f207,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(avatar_sat_refutation,[],[f195,f204,f206])).
% 1.27/0.54  fof(f206,plain,(
% 1.27/0.54    ~spl6_4 | ~spl6_5),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f205])).
% 1.27/0.54  fof(f205,plain,(
% 1.27/0.54    $false | (~spl6_4 | ~spl6_5)),
% 1.27/0.54    inference(subsumption_resolution,[],[f190,f194])).
% 1.27/0.54  fof(f194,plain,(
% 1.27/0.54    ( ! [X2] : (~r2_hidden(sK0,X2)) ) | ~spl6_5),
% 1.27/0.54    inference(avatar_component_clause,[],[f193])).
% 1.27/0.54  fof(f193,plain,(
% 1.27/0.54    spl6_5 <=> ! [X2] : ~r2_hidden(sK0,X2)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.27/0.54  fof(f190,plain,(
% 1.27/0.54    r2_hidden(sK0,k1_tarski(sK1)) | ~spl6_4),
% 1.27/0.54    inference(avatar_component_clause,[],[f189])).
% 1.27/0.54  fof(f189,plain,(
% 1.27/0.54    spl6_4 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.27/0.54  fof(f204,plain,(
% 1.27/0.54    spl6_4),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f203])).
% 1.27/0.54  fof(f203,plain,(
% 1.27/0.54    $false | spl6_4),
% 1.27/0.54    inference(subsumption_resolution,[],[f201,f117])).
% 1.27/0.54  fof(f117,plain,(
% 1.27/0.54    ~sQ5_eqProxy(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK1))),
% 1.27/0.54    inference(resolution,[],[f110,f68])).
% 1.27/0.54  fof(f68,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~sQ5_eqProxy(k4_xboole_0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.27/0.54    inference(equality_proxy_replacement,[],[f29,f58])).
% 1.27/0.54  fof(f58,plain,(
% 1.27/0.54    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 1.27/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 1.27/0.54    inference(ennf_transformation,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 1.27/0.54    inference(unused_predicate_definition_removal,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.27/0.54  fof(f110,plain,(
% 1.27/0.54    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 1.27/0.54    inference(resolution,[],[f94,f73])).
% 1.27/0.54  fof(f73,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | sQ5_eqProxy(k2_xboole_0(k4_xboole_0(X2,X0),X1),k4_xboole_0(k2_xboole_0(X2,X1),X0))) )),
% 1.27/0.54    inference(equality_proxy_replacement,[],[f35,f58])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 1.27/0.54  fof(f94,plain,(
% 1.27/0.54    ~sQ5_eqProxy(k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)),k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)))),
% 1.27/0.54    inference(resolution,[],[f64,f82])).
% 1.27/0.54  fof(f82,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~sQ5_eqProxy(X0,X1) | sQ5_eqProxy(X1,X0)) )),
% 1.27/0.54    inference(equality_proxy_axiom,[],[f58])).
% 1.27/0.54  fof(f64,plain,(
% 1.27/0.54    ~sQ5_eqProxy(k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)),k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)))),
% 1.27/0.54    inference(equality_proxy_replacement,[],[f22,f58])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 1.27/0.54    inference(ennf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,negated_conjecture,(
% 1.27/0.54    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 1.27/0.54    inference(negated_conjecture,[],[f15])).
% 1.27/0.54  fof(f15,conjecture,(
% 1.27/0.54    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 1.42/0.54  fof(f201,plain,(
% 1.42/0.54    sQ5_eqProxy(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK1)) | spl6_4),
% 1.42/0.54    inference(resolution,[],[f191,f70])).
% 1.42/0.54  fof(f70,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | sQ5_eqProxy(k4_xboole_0(X0,k1_tarski(X1)),X0)) )),
% 1.42/0.54    inference(equality_proxy_replacement,[],[f30,f58])).
% 1.42/0.54  fof(f30,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 1.42/0.54    inference(cnf_transformation,[],[f14])).
% 1.42/0.54  fof(f14,axiom,(
% 1.42/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.42/0.54  fof(f191,plain,(
% 1.42/0.54    ~r2_hidden(sK0,k1_tarski(sK1)) | spl6_4),
% 1.42/0.54    inference(avatar_component_clause,[],[f189])).
% 1.42/0.54  fof(f195,plain,(
% 1.42/0.54    ~spl6_4 | spl6_5),
% 1.42/0.54    inference(avatar_split_clause,[],[f102,f193,f189])).
% 1.42/0.54  fof(f102,plain,(
% 1.42/0.54    ( ! [X2] : (~r2_hidden(sK0,X2) | ~r2_hidden(sK0,k1_tarski(sK1))) )),
% 1.42/0.54    inference(resolution,[],[f84,f55])).
% 1.42/0.54  fof(f55,plain,(
% 1.42/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.42/0.54    inference(equality_resolution,[],[f46])).
% 1.42/0.54  fof(f46,plain,(
% 1.42/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.42/0.54    inference(cnf_transformation,[],[f3])).
% 1.42/0.54  fof(f3,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.42/0.54  fof(f84,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK0,k4_xboole_0(X0,k1_tarski(sK1))) | ~r2_hidden(sK0,X0)) )),
% 1.42/0.54    inference(resolution,[],[f65,f80])).
% 1.42/0.54  fof(f80,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | sQ5_eqProxy(X0,X2) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.42/0.54    inference(equality_proxy_replacement,[],[f50,f58])).
% 1.42/0.54  fof(f50,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f13])).
% 1.42/0.54  fof(f13,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.42/0.54  fof(f65,plain,(
% 1.42/0.54    ~sQ5_eqProxy(sK0,sK1)),
% 1.42/0.54    inference(equality_proxy_replacement,[],[f21,f58])).
% 1.42/0.54  fof(f21,plain,(
% 1.42/0.54    sK0 != sK1),
% 1.42/0.54    inference(cnf_transformation,[],[f18])).
% 1.42/0.54  % SZS output end Proof for theBenchmark
% 1.42/0.54  % (1874)------------------------------
% 1.42/0.54  % (1874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (1874)Termination reason: Refutation
% 1.42/0.54  
% 1.42/0.54  % (1874)Memory used [KB]: 6268
% 1.42/0.54  % (1874)Time elapsed: 0.144 s
% 1.42/0.54  % (1874)------------------------------
% 1.42/0.54  % (1874)------------------------------
% 1.42/0.54  % (1860)Success in time 0.184 s
%------------------------------------------------------------------------------
