%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:19 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   56 (  80 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 189 expanded)
%              Number of equality atoms :   44 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f78,f84,f94,f116,f140,f246])).

fof(f246,plain,
    ( ~ spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f244,f83])).

fof(f83,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_4
  <=> k1_tarski(sK3) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f244,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f234,f139])).

fof(f139,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_7
  <=> k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f234,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3))
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(superposition,[],[f121,f77])).

fof(f77,plain,
    ( k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_3
  <=> k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f121,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))
    | ~ spl7_6 ),
    inference(superposition,[],[f42,f115])).

fof(f115,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_6
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f140,plain,
    ( spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f119,f64,f137])).

fof(f64,plain,
    ( spl7_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f119,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f118,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f118,plain,
    ( k2_tarski(sK3,sK3) = k3_xboole_0(sK0,k2_tarski(sK3,sK3))
    | ~ spl7_2 ),
    inference(resolution,[],[f73,f66])).

fof(f66,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f73,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | k2_tarski(sK3,X2) = k3_xboole_0(sK0,k2_tarski(sK3,X2)) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f72,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f72,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | k2_tarski(sK3,X2) = k3_xboole_0(k2_tarski(sK3,X2),sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f116,plain,
    ( spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f95,f91,f113])).

fof(f91,plain,
    ( spl7_5
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f95,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl7_5 ),
    inference(superposition,[],[f37,f93])).

fof(f93,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f94,plain,
    ( spl7_5
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f69,f59,f91])).

fof(f59,plain,
    ( spl7_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f69,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f61,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f84,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f31,f81])).

fof(f31,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f78,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (819068929)
% 0.20/0.37  ipcrm: permission denied for id (819134467)
% 0.20/0.37  ipcrm: permission denied for id (820084740)
% 0.20/0.37  ipcrm: permission denied for id (820117509)
% 0.20/0.37  ipcrm: permission denied for id (820183047)
% 0.20/0.37  ipcrm: permission denied for id (820215816)
% 0.20/0.38  ipcrm: permission denied for id (820379661)
% 0.20/0.38  ipcrm: permission denied for id (820412430)
% 0.20/0.38  ipcrm: permission denied for id (819232783)
% 0.20/0.38  ipcrm: permission denied for id (820477969)
% 0.20/0.38  ipcrm: permission denied for id (820510738)
% 0.20/0.38  ipcrm: permission denied for id (820543507)
% 0.20/0.38  ipcrm: permission denied for id (820576276)
% 0.20/0.38  ipcrm: permission denied for id (820641814)
% 0.20/0.38  ipcrm: permission denied for id (820674583)
% 0.20/0.38  ipcrm: permission denied for id (820707352)
% 0.20/0.39  ipcrm: permission denied for id (820772890)
% 0.20/0.39  ipcrm: permission denied for id (820805659)
% 0.20/0.39  ipcrm: permission denied for id (820838428)
% 0.20/0.39  ipcrm: permission denied for id (820871197)
% 0.20/0.39  ipcrm: permission denied for id (820903966)
% 0.20/0.39  ipcrm: permission denied for id (819331103)
% 0.20/0.39  ipcrm: permission denied for id (820936736)
% 0.20/0.39  ipcrm: permission denied for id (820969505)
% 0.20/0.39  ipcrm: permission denied for id (819363874)
% 0.20/0.39  ipcrm: permission denied for id (819396644)
% 0.20/0.40  ipcrm: permission denied for id (821133352)
% 0.20/0.40  ipcrm: permission denied for id (821231659)
% 0.20/0.40  ipcrm: permission denied for id (821264428)
% 0.20/0.40  ipcrm: permission denied for id (821461042)
% 0.20/0.40  ipcrm: permission denied for id (821526579)
% 0.20/0.41  ipcrm: permission denied for id (821559348)
% 0.20/0.41  ipcrm: permission denied for id (821592117)
% 0.20/0.41  ipcrm: permission denied for id (821657655)
% 0.20/0.41  ipcrm: permission denied for id (821690424)
% 0.20/0.41  ipcrm: permission denied for id (821755962)
% 0.20/0.41  ipcrm: permission denied for id (819560507)
% 0.20/0.41  ipcrm: permission denied for id (821788732)
% 0.20/0.41  ipcrm: permission denied for id (821887039)
% 0.20/0.42  ipcrm: permission denied for id (821985346)
% 0.20/0.42  ipcrm: permission denied for id (822149191)
% 0.20/0.42  ipcrm: permission denied for id (822181960)
% 0.20/0.42  ipcrm: permission denied for id (819626057)
% 0.20/0.43  ipcrm: permission denied for id (822247499)
% 0.20/0.43  ipcrm: permission denied for id (822280268)
% 0.20/0.43  ipcrm: permission denied for id (819658830)
% 0.20/0.43  ipcrm: permission denied for id (822345807)
% 0.20/0.43  ipcrm: permission denied for id (819691600)
% 0.20/0.44  ipcrm: permission denied for id (822411346)
% 0.20/0.44  ipcrm: permission denied for id (822444115)
% 0.20/0.44  ipcrm: permission denied for id (822575191)
% 0.20/0.44  ipcrm: permission denied for id (822607960)
% 0.20/0.44  ipcrm: permission denied for id (822673498)
% 0.20/0.45  ipcrm: permission denied for id (819724379)
% 0.20/0.45  ipcrm: permission denied for id (822739037)
% 0.20/0.45  ipcrm: permission denied for id (819757151)
% 0.20/0.45  ipcrm: permission denied for id (822837345)
% 0.20/0.45  ipcrm: permission denied for id (822902883)
% 0.20/0.46  ipcrm: permission denied for id (822935652)
% 0.20/0.46  ipcrm: permission denied for id (819789928)
% 0.20/0.46  ipcrm: permission denied for id (823066729)
% 0.20/0.47  ipcrm: permission denied for id (823197805)
% 0.20/0.47  ipcrm: permission denied for id (819822703)
% 0.20/0.47  ipcrm: permission denied for id (823263344)
% 0.20/0.47  ipcrm: permission denied for id (823328882)
% 0.20/0.47  ipcrm: permission denied for id (823394420)
% 0.20/0.48  ipcrm: permission denied for id (823427189)
% 0.20/0.48  ipcrm: permission denied for id (823459958)
% 0.20/0.48  ipcrm: permission denied for id (823492727)
% 0.20/0.48  ipcrm: permission denied for id (823656571)
% 0.20/0.49  ipcrm: permission denied for id (823787647)
% 0.88/0.62  % (28071)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.88/0.63  % (28072)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.88/0.64  % (28069)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.88/0.64  % (28088)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.88/0.64  % (28089)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.88/0.64  % (28081)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.88/0.65  % (28075)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.88/0.65  % (28086)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.88/0.65  % (28070)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.88/0.65  % (28078)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.88/0.65  % (28096)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.88/0.66  % (28079)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.66  % (28090)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.66  % (28087)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.67  % (28066)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.67  % (28068)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.47/0.67  % (28067)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.47/0.67  % (28082)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.67  % (28091)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.68  % (28074)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.68  % (28085)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.68  % (28095)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.68  % (28083)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.68  % (28077)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.68  % (28073)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.68  % (28093)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.68  % (28087)Refutation found. Thanks to Tanya!
% 1.47/0.68  % SZS status Theorem for theBenchmark
% 1.47/0.68  % (28076)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.69  % (28094)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.69  % (28092)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.69  % (28084)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.70  % SZS output start Proof for theBenchmark
% 1.47/0.70  fof(f252,plain,(
% 1.47/0.70    $false),
% 1.47/0.70    inference(avatar_sat_refutation,[],[f62,f67,f78,f84,f94,f116,f140,f246])).
% 1.47/0.70  fof(f246,plain,(
% 1.47/0.70    ~spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7),
% 1.47/0.70    inference(avatar_contradiction_clause,[],[f245])).
% 1.47/0.70  fof(f245,plain,(
% 1.47/0.70    $false | (~spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 1.47/0.70    inference(subsumption_resolution,[],[f244,f83])).
% 1.47/0.70  fof(f83,plain,(
% 1.47/0.70    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) | spl7_4),
% 1.47/0.70    inference(avatar_component_clause,[],[f81])).
% 1.47/0.70  fof(f81,plain,(
% 1.47/0.70    spl7_4 <=> k1_tarski(sK3) = k3_xboole_0(sK0,sK2)),
% 1.47/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.47/0.70  fof(f244,plain,(
% 1.47/0.70    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | (~spl7_3 | ~spl7_6 | ~spl7_7)),
% 1.47/0.70    inference(forward_demodulation,[],[f234,f139])).
% 1.47/0.70  fof(f139,plain,(
% 1.47/0.70    k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3)) | ~spl7_7),
% 1.47/0.70    inference(avatar_component_clause,[],[f137])).
% 1.47/0.70  fof(f137,plain,(
% 1.47/0.70    spl7_7 <=> k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 1.47/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.47/0.70  fof(f234,plain,(
% 1.47/0.70    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3)) | (~spl7_3 | ~spl7_6)),
% 1.47/0.70    inference(superposition,[],[f121,f77])).
% 1.47/0.70  fof(f77,plain,(
% 1.47/0.70    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) | ~spl7_3),
% 1.47/0.70    inference(avatar_component_clause,[],[f75])).
% 1.47/0.70  fof(f75,plain,(
% 1.47/0.70    spl7_3 <=> k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 1.47/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.47/0.70  fof(f121,plain,(
% 1.47/0.70    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) ) | ~spl7_6),
% 1.47/0.70    inference(superposition,[],[f42,f115])).
% 1.47/0.70  fof(f115,plain,(
% 1.47/0.70    sK0 = k3_xboole_0(sK0,sK1) | ~spl7_6),
% 1.47/0.70    inference(avatar_component_clause,[],[f113])).
% 1.47/0.70  fof(f113,plain,(
% 1.47/0.70    spl7_6 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 1.47/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.47/0.70  fof(f42,plain,(
% 1.47/0.70    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.47/0.70    inference(cnf_transformation,[],[f6])).
% 1.47/0.70  fof(f6,axiom,(
% 1.47/0.70    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.47/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.47/0.70  fof(f140,plain,(
% 1.47/0.70    spl7_7 | ~spl7_2),
% 1.47/0.70    inference(avatar_split_clause,[],[f119,f64,f137])).
% 1.47/0.70  fof(f64,plain,(
% 1.47/0.70    spl7_2 <=> r2_hidden(sK3,sK0)),
% 1.47/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.47/0.70  fof(f119,plain,(
% 1.47/0.70    k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3)) | ~spl7_2),
% 1.47/0.70    inference(forward_demodulation,[],[f118,f33])).
% 1.47/0.70  fof(f33,plain,(
% 1.47/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.47/0.70    inference(cnf_transformation,[],[f11])).
% 1.47/0.70  fof(f11,axiom,(
% 1.47/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.47/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.70  fof(f118,plain,(
% 1.47/0.70    k2_tarski(sK3,sK3) = k3_xboole_0(sK0,k2_tarski(sK3,sK3)) | ~spl7_2),
% 1.47/0.70    inference(resolution,[],[f73,f66])).
% 1.47/0.70  fof(f66,plain,(
% 1.47/0.70    r2_hidden(sK3,sK0) | ~spl7_2),
% 1.47/0.70    inference(avatar_component_clause,[],[f64])).
% 1.47/0.70  fof(f73,plain,(
% 1.47/0.70    ( ! [X2] : (~r2_hidden(X2,sK0) | k2_tarski(sK3,X2) = k3_xboole_0(sK0,k2_tarski(sK3,X2))) ) | ~spl7_2),
% 1.47/0.70    inference(forward_demodulation,[],[f72,f36])).
% 1.47/0.70  fof(f36,plain,(
% 1.47/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.47/0.70    inference(cnf_transformation,[],[f1])).
% 1.47/0.70  fof(f1,axiom,(
% 1.47/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.47/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.47/0.70  fof(f72,plain,(
% 1.47/0.70    ( ! [X2] : (~r2_hidden(X2,sK0) | k2_tarski(sK3,X2) = k3_xboole_0(k2_tarski(sK3,X2),sK0)) ) | ~spl7_2),
% 1.47/0.70    inference(resolution,[],[f66,f44])).
% 1.47/0.70  fof(f44,plain,(
% 1.47/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 1.47/0.70    inference(cnf_transformation,[],[f27])).
% 1.47/0.70  fof(f27,plain,(
% 1.47/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 1.47/0.70    inference(flattening,[],[f26])).
% 1.47/0.70  fof(f26,plain,(
% 1.47/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 1.47/0.70    inference(ennf_transformation,[],[f18])).
% 1.47/0.70  fof(f18,axiom,(
% 1.47/0.70    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.47/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 1.47/0.70  fof(f116,plain,(
% 1.47/0.70    spl7_6 | ~spl7_5),
% 1.47/0.70    inference(avatar_split_clause,[],[f95,f91,f113])).
% 1.47/0.70  fof(f91,plain,(
% 1.47/0.70    spl7_5 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 1.47/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.47/0.70  fof(f95,plain,(
% 1.47/0.70    sK0 = k3_xboole_0(sK0,sK1) | ~spl7_5),
% 1.47/0.70    inference(superposition,[],[f37,f93])).
% 1.47/0.70  fof(f93,plain,(
% 1.47/0.70    sK1 = k2_xboole_0(sK0,sK1) | ~spl7_5),
% 1.47/0.70    inference(avatar_component_clause,[],[f91])).
% 1.47/0.70  fof(f37,plain,(
% 1.47/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.47/0.70    inference(cnf_transformation,[],[f7])).
% 1.47/0.70  fof(f7,axiom,(
% 1.47/0.70    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.47/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.47/0.70  fof(f94,plain,(
% 1.47/0.70    spl7_5 | ~spl7_1),
% 1.47/0.70    inference(avatar_split_clause,[],[f69,f59,f91])).
% 1.47/0.70  fof(f59,plain,(
% 1.47/0.70    spl7_1 <=> r1_tarski(sK0,sK1)),
% 1.47/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.47/0.70  fof(f69,plain,(
% 1.47/0.70    sK1 = k2_xboole_0(sK0,sK1) | ~spl7_1),
% 1.47/0.70    inference(resolution,[],[f61,f40])).
% 1.47/0.70  fof(f40,plain,(
% 1.47/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.47/0.70    inference(cnf_transformation,[],[f24])).
% 1.47/0.70  fof(f24,plain,(
% 1.47/0.70    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.47/0.70    inference(ennf_transformation,[],[f5])).
% 1.47/0.70  fof(f5,axiom,(
% 1.47/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.47/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.47/0.70  fof(f61,plain,(
% 1.47/0.70    r1_tarski(sK0,sK1) | ~spl7_1),
% 1.47/0.70    inference(avatar_component_clause,[],[f59])).
% 1.47/0.70  fof(f84,plain,(
% 1.47/0.70    ~spl7_4),
% 1.47/0.70    inference(avatar_split_clause,[],[f31,f81])).
% 1.47/0.70  fof(f31,plain,(
% 1.47/0.70    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.47/0.70    inference(cnf_transformation,[],[f22])).
% 1.47/0.70  fof(f22,plain,(
% 1.47/0.70    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.47/0.70    inference(flattening,[],[f21])).
% 1.47/0.70  fof(f21,plain,(
% 1.47/0.70    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.47/0.70    inference(ennf_transformation,[],[f20])).
% 1.47/0.70  fof(f20,negated_conjecture,(
% 1.47/0.70    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.47/0.70    inference(negated_conjecture,[],[f19])).
% 1.47/0.70  fof(f19,conjecture,(
% 1.47/0.70    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.47/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.47/0.70  fof(f78,plain,(
% 1.47/0.70    spl7_3),
% 1.47/0.70    inference(avatar_split_clause,[],[f29,f75])).
% 1.47/0.70  fof(f29,plain,(
% 1.47/0.70    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 1.47/0.70    inference(cnf_transformation,[],[f22])).
% 1.47/0.70  fof(f67,plain,(
% 1.47/0.70    spl7_2),
% 1.47/0.70    inference(avatar_split_clause,[],[f30,f64])).
% 1.47/0.70  fof(f30,plain,(
% 1.47/0.70    r2_hidden(sK3,sK0)),
% 1.47/0.70    inference(cnf_transformation,[],[f22])).
% 1.47/0.70  fof(f62,plain,(
% 1.47/0.70    spl7_1),
% 1.47/0.70    inference(avatar_split_clause,[],[f28,f59])).
% 1.47/0.70  fof(f28,plain,(
% 1.47/0.70    r1_tarski(sK0,sK1)),
% 1.47/0.70    inference(cnf_transformation,[],[f22])).
% 1.47/0.70  % SZS output end Proof for theBenchmark
% 1.47/0.70  % (28087)------------------------------
% 1.47/0.70  % (28087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.70  % (28087)Termination reason: Refutation
% 1.47/0.70  
% 1.47/0.70  % (28087)Memory used [KB]: 10874
% 1.47/0.70  % (28087)Time elapsed: 0.152 s
% 1.47/0.70  % (28087)------------------------------
% 1.47/0.70  % (28087)------------------------------
% 1.47/0.70  % (27907)Success in time 0.342 s
%------------------------------------------------------------------------------
