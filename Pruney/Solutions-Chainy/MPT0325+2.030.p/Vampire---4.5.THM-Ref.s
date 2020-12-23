%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 103 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 267 expanded)
%              Number of equality atoms :   13 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25154)Time elapsed: 0.125 s
% (25154)------------------------------
% (25154)------------------------------
fof(f724,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f372,f723])).

% (25152)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f723,plain,(
    spl14_2 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | spl14_2 ),
    inference(unit_resulting_resolution,[],[f65,f680,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

% (25169)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f680,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK1)
    | spl14_2 ),
    inference(subsumption_resolution,[],[f666,f385])).

fof(f385,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK6(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl14_2 ),
    inference(resolution,[],[f375,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f375,plain,
    ( ~ r2_hidden(sK6(sK0,sK2),sK2)
    | spl14_2 ),
    inference(resolution,[],[f81,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f81,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl14_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl14_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f666,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r2_hidden(k4_tarski(sK6(sK0,sK2),X5),k2_zfmisc_1(sK2,sK3)) )
    | spl14_2 ),
    inference(resolution,[],[f377,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f17,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f377,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(sK6(sK0,sK2),X1),k2_zfmisc_1(sK0,X2))
        | ~ r2_hidden(X1,X2) )
    | spl14_2 ),
    inference(resolution,[],[f374,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f374,plain,
    ( r2_hidden(sK6(sK0,sK2),sK0)
    | spl14_2 ),
    inference(resolution,[],[f81,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0] :
      ( sQ13_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f20,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( sQ13_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).

% (25169)Refutation not found, incomplete strategy% (25169)------------------------------
% (25169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f52,plain,(
    ~ sQ13_eqProxy(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(equality_proxy_replacement,[],[f18,f51])).

fof(f18,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f372,plain,(
    spl14_1 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl14_1 ),
    inference(unit_resulting_resolution,[],[f65,f332,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f332,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK0)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f322,f96])).

fof(f96,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,sK6(sK1,sK3)),k2_zfmisc_1(X3,sK3))
    | spl14_1 ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f84,plain,
    ( ~ r2_hidden(sK6(sK1,sK3),sK3)
    | spl14_1 ),
    inference(resolution,[],[f77,f25])).

fof(f77,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl14_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f322,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,sK0)
        | r2_hidden(k4_tarski(X10,sK6(sK1,sK3)),k2_zfmisc_1(sK2,sK3)) )
    | spl14_1 ),
    inference(resolution,[],[f88,f85])).

fof(f88,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k4_tarski(X3,sK6(sK1,sK3)),k2_zfmisc_1(X4,sK1))
        | ~ r2_hidden(X3,X4) )
    | spl14_1 ),
    inference(resolution,[],[f83,f42])).

% (25171)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f83,plain,
    ( r2_hidden(sK6(sK1,sK3),sK1)
    | spl14_1 ),
    inference(resolution,[],[f77,f24])).

fof(f82,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f16,f79,f75])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:28:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (25173)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (25176)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (25163)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (25165)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (25153)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (25173)Refutation not found, incomplete strategy% (25173)------------------------------
% 0.20/0.52  % (25173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25173)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25173)Memory used [KB]: 1663
% 0.20/0.52  % (25173)Time elapsed: 0.115 s
% 0.20/0.52  % (25173)------------------------------
% 0.20/0.52  % (25173)------------------------------
% 0.20/0.52  % (25181)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (25156)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (25180)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (25164)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (25178)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (25160)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (25155)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (25166)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (25154)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (25170)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (25154)Refutation not found, incomplete strategy% (25154)------------------------------
% 0.20/0.54  % (25154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25172)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (25177)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (25162)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (25168)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (25157)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (25158)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (25174)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (25167)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (25175)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (25174)Refutation not found, incomplete strategy% (25174)------------------------------
% 0.20/0.54  % (25174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25174)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25174)Memory used [KB]: 10746
% 0.20/0.54  % (25174)Time elapsed: 0.087 s
% 0.20/0.54  % (25174)------------------------------
% 0.20/0.54  % (25174)------------------------------
% 0.20/0.54  % (25154)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25165)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (25154)Memory used [KB]: 10618
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (25154)Time elapsed: 0.125 s
% 0.20/0.54  % (25154)------------------------------
% 0.20/0.54  % (25154)------------------------------
% 0.20/0.54  fof(f724,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f82,f372,f723])).
% 0.20/0.54  % (25152)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  fof(f723,plain,(
% 0.20/0.54    spl14_2),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f699])).
% 0.20/0.54  fof(f699,plain,(
% 0.20/0.54    $false | spl14_2),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f65,f680,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK10(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(sK10(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.54  % (25169)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  fof(f680,plain,(
% 0.20/0.54    ( ! [X5] : (~r2_hidden(X5,sK1)) ) | spl14_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f666,f385])).
% 0.20/0.54  fof(f385,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK6(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl14_2),
% 0.20/0.54    inference(resolution,[],[f375,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.54  fof(f375,plain,(
% 0.20/0.54    ~r2_hidden(sK6(sK0,sK2),sK2) | spl14_2),
% 0.20/0.54    inference(resolution,[],[f81,f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ~r1_tarski(sK0,sK2) | spl14_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    spl14_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.20/0.54  fof(f666,plain,(
% 0.20/0.54    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(k4_tarski(sK6(sK0,sK2),X5),k2_zfmisc_1(sK2,sK3))) ) | spl14_2),
% 0.20/0.54    inference(resolution,[],[f377,f85])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,k2_zfmisc_1(sK2,sK3))) )),
% 0.20/0.54    inference(resolution,[],[f17,f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.54    inference(flattening,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(negated_conjecture,[],[f8])).
% 0.20/0.54  fof(f8,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.20/0.54  fof(f377,plain,(
% 0.20/0.54    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK6(sK0,sK2),X1),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X1,X2)) ) | spl14_2),
% 0.20/0.54    inference(resolution,[],[f374,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f374,plain,(
% 0.20/0.54    r2_hidden(sK6(sK0,sK2),sK0) | spl14_2),
% 0.20/0.54    inference(resolution,[],[f81,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 0.20/0.54    inference(resolution,[],[f52,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0] : (sQ13_eqProxy(k1_xboole_0,X0) | r2_hidden(sK4(X0),X0)) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f20,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X1,X0] : (sQ13_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).
% 0.20/0.55  % (25169)Refutation not found, incomplete strategy% (25169)------------------------------
% 0.20/0.55  % (25169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ~sQ13_eqProxy(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.55    inference(equality_proxy_replacement,[],[f18,f51])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f372,plain,(
% 0.20/0.55    spl14_1),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f348])).
% 0.20/0.55  fof(f348,plain,(
% 0.20/0.55    $false | spl14_1),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f65,f332,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f332,plain,(
% 0.20/0.55    ( ! [X10] : (~r2_hidden(X10,sK0)) ) | spl14_1),
% 0.20/0.55    inference(subsumption_resolution,[],[f322,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,sK6(sK1,sK3)),k2_zfmisc_1(X3,sK3))) ) | spl14_1),
% 0.20/0.55    inference(resolution,[],[f84,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ~r2_hidden(sK6(sK1,sK3),sK3) | spl14_1),
% 0.20/0.55    inference(resolution,[],[f77,f25])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ~r1_tarski(sK1,sK3) | spl14_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    spl14_1 <=> r1_tarski(sK1,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.20/0.55  fof(f322,plain,(
% 0.20/0.55    ( ! [X10] : (~r2_hidden(X10,sK0) | r2_hidden(k4_tarski(X10,sK6(sK1,sK3)),k2_zfmisc_1(sK2,sK3))) ) | spl14_1),
% 0.20/0.55    inference(resolution,[],[f88,f85])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,sK6(sK1,sK3)),k2_zfmisc_1(X4,sK1)) | ~r2_hidden(X3,X4)) ) | spl14_1),
% 0.20/0.55    inference(resolution,[],[f83,f42])).
% 0.20/0.55  % (25171)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    r2_hidden(sK6(sK1,sK3),sK1) | spl14_1),
% 0.20/0.55    inference(resolution,[],[f77,f24])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ~spl14_1 | ~spl14_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f16,f79,f75])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (25165)------------------------------
% 0.20/0.55  % (25165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25165)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (25165)Memory used [KB]: 6780
% 0.20/0.55  % (25165)Time elapsed: 0.131 s
% 0.20/0.55  % (25165)------------------------------
% 0.20/0.55  % (25165)------------------------------
% 0.20/0.55  % (25150)Success in time 0.184 s
%------------------------------------------------------------------------------
