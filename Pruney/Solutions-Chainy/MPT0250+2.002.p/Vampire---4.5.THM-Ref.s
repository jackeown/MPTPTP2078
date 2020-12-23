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
% DateTime   : Thu Dec  3 12:38:19 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   59 (  88 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :  110 ( 165 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f80,f127,f170,f189,f211,f220,f236])).

fof(f236,plain,(
    ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f231,f86])).

fof(f86,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f49,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f231,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f104,f122])).

fof(f122,plain,
    ( r2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_4
  <=> r2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f220,plain,
    ( ~ spl2_8
    | spl2_6 ),
    inference(avatar_split_clause,[],[f214,f167,f217])).

fof(f217,plain,
    ( spl2_8
  <=> r2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f167,plain,
    ( spl2_6
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f214,plain,
    ( ~ r2_xboole_0(k1_tarski(sK0),sK1)
    | spl2_6 ),
    inference(resolution,[],[f168,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f168,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f211,plain,
    ( spl2_1
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl2_1
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f205,f65])).

fof(f65,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f205,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_6 ),
    inference(resolution,[],[f97,f169])).

fof(f169,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f36,f56])).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f189,plain,
    ( ~ spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f164,f124,f186])).

fof(f186,plain,
    ( spl2_7
  <=> r2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f124,plain,
    ( spl2_5
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f164,plain,
    ( ~ r2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_5 ),
    inference(superposition,[],[f73,f126])).

fof(f126,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f73,plain,(
    ! [X0,X1] : ~ r2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f45,f49])).

fof(f170,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f151,f124,f167])).

fof(f151,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f49,f126])).

fof(f127,plain,
    ( spl2_4
    | spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f112,f68,f124,f120])).

fof(f68,plain,
    ( spl2_2
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f112,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | r2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,
    ( ~ spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f72,f68,f77])).

fof(f77,plain,
    ( spl2_3
  <=> r2_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f72,plain,
    ( ~ r2_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f45,f70])).

fof(f71,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f66,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (26690)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.49  % (26698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (26687)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (26694)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.26/0.52  % (26691)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.26/0.52  % (26702)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.52  % (26686)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.53  % (26688)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.53  % (26683)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.53  % (26705)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.53  % (26697)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.53  % (26711)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.53  % (26684)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.53  % (26712)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.53  % (26706)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.53  % (26710)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (26709)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (26692)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.54  % (26689)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.54  % (26703)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (26704)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.54  % (26701)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.54  % (26703)Refutation not found, incomplete strategy% (26703)------------------------------
% 1.36/0.54  % (26703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (26703)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (26703)Memory used [KB]: 10746
% 1.36/0.54  % (26703)Time elapsed: 0.143 s
% 1.36/0.54  % (26703)------------------------------
% 1.36/0.54  % (26703)------------------------------
% 1.36/0.54  % (26699)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (26693)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.54  % (26695)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (26708)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (26705)Refutation not found, incomplete strategy% (26705)------------------------------
% 1.36/0.54  % (26705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (26705)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.55  % (26705)Memory used [KB]: 10874
% 1.36/0.55  % (26705)Time elapsed: 0.096 s
% 1.36/0.55  % (26705)------------------------------
% 1.36/0.55  % (26705)------------------------------
% 1.36/0.55  % (26696)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (26685)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.55  % (26707)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.56  % (26700)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.04/0.68  % (26713)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.52/0.69  % (26714)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.52/0.70  % (26684)Refutation found. Thanks to Tanya!
% 2.52/0.70  % SZS status Theorem for theBenchmark
% 2.52/0.70  % SZS output start Proof for theBenchmark
% 2.52/0.70  fof(f237,plain,(
% 2.52/0.70    $false),
% 2.52/0.70    inference(avatar_sat_refutation,[],[f66,f71,f80,f127,f170,f189,f211,f220,f236])).
% 2.52/0.70  fof(f236,plain,(
% 2.52/0.70    ~spl2_4),
% 2.52/0.70    inference(avatar_contradiction_clause,[],[f235])).
% 2.52/0.70  fof(f235,plain,(
% 2.52/0.70    $false | ~spl2_4),
% 2.52/0.70    inference(subsumption_resolution,[],[f231,f86])).
% 2.52/0.70  fof(f86,plain,(
% 2.52/0.70    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.52/0.70    inference(superposition,[],[f49,f53])).
% 2.52/0.70  fof(f53,plain,(
% 2.52/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.52/0.70    inference(cnf_transformation,[],[f8])).
% 2.52/0.70  fof(f8,axiom,(
% 2.52/0.70    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.52/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.52/0.70  fof(f49,plain,(
% 2.52/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.52/0.70    inference(cnf_transformation,[],[f14])).
% 2.52/0.70  fof(f14,axiom,(
% 2.52/0.70    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.52/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.52/0.70  fof(f231,plain,(
% 2.52/0.70    ~r1_tarski(sK1,sK1) | ~spl2_4),
% 2.52/0.70    inference(resolution,[],[f104,f122])).
% 2.52/0.70  fof(f122,plain,(
% 2.52/0.70    r2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl2_4),
% 2.52/0.70    inference(avatar_component_clause,[],[f120])).
% 2.52/0.70  fof(f120,plain,(
% 2.52/0.70    spl2_4 <=> r2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.52/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.52/0.70  fof(f104,plain,(
% 2.52/0.70    ( ! [X2,X0,X1] : (~r2_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_tarski(X0,X1)) )),
% 2.52/0.70    inference(resolution,[],[f44,f45])).
% 2.52/0.70  fof(f45,plain,(
% 2.52/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 2.52/0.70    inference(cnf_transformation,[],[f33])).
% 2.52/0.70  fof(f33,plain,(
% 2.52/0.70    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 2.52/0.70    inference(ennf_transformation,[],[f13])).
% 2.52/0.70  fof(f13,axiom,(
% 2.52/0.70    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 2.52/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 2.52/0.70  fof(f44,plain,(
% 2.52/0.70    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.52/0.70    inference(cnf_transformation,[],[f32])).
% 2.52/0.70  fof(f32,plain,(
% 2.52/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.52/0.70    inference(ennf_transformation,[],[f6])).
% 2.52/0.70  fof(f6,axiom,(
% 2.52/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.52/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.52/0.70  fof(f220,plain,(
% 2.52/0.70    ~spl2_8 | spl2_6),
% 2.52/0.70    inference(avatar_split_clause,[],[f214,f167,f217])).
% 2.52/0.70  fof(f217,plain,(
% 2.52/0.70    spl2_8 <=> r2_xboole_0(k1_tarski(sK0),sK1)),
% 2.52/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.52/0.70  fof(f167,plain,(
% 2.52/0.70    spl2_6 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 2.52/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.52/0.70  fof(f214,plain,(
% 2.52/0.70    ~r2_xboole_0(k1_tarski(sK0),sK1) | spl2_6),
% 2.52/0.70    inference(resolution,[],[f168,f46])).
% 2.52/0.70  fof(f46,plain,(
% 2.52/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.52/0.70    inference(cnf_transformation,[],[f3])).
% 2.52/0.70  fof(f3,axiom,(
% 2.52/0.70    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.52/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 2.52/0.70  fof(f168,plain,(
% 2.52/0.70    ~r1_tarski(k1_tarski(sK0),sK1) | spl2_6),
% 2.52/0.70    inference(avatar_component_clause,[],[f167])).
% 2.52/0.70  fof(f211,plain,(
% 2.52/0.70    spl2_1 | ~spl2_6),
% 2.52/0.70    inference(avatar_contradiction_clause,[],[f210])).
% 2.52/0.70  fof(f210,plain,(
% 2.52/0.70    $false | (spl2_1 | ~spl2_6)),
% 2.52/0.70    inference(subsumption_resolution,[],[f205,f65])).
% 2.52/0.70  fof(f65,plain,(
% 2.52/0.70    ~r2_hidden(sK0,sK1) | spl2_1),
% 2.52/0.70    inference(avatar_component_clause,[],[f63])).
% 2.52/0.70  fof(f63,plain,(
% 2.52/0.70    spl2_1 <=> r2_hidden(sK0,sK1)),
% 2.52/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.52/0.70  fof(f205,plain,(
% 2.52/0.70    r2_hidden(sK0,sK1) | ~spl2_6),
% 2.52/0.70    inference(resolution,[],[f97,f169])).
% 2.52/0.70  fof(f169,plain,(
% 2.52/0.70    r1_tarski(k1_tarski(sK0),sK1) | ~spl2_6),
% 2.52/0.70    inference(avatar_component_clause,[],[f167])).
% 2.52/0.70  fof(f97,plain,(
% 2.52/0.70    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.52/0.70    inference(superposition,[],[f36,f56])).
% 2.52/0.70  fof(f56,plain,(
% 2.52/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.52/0.70    inference(cnf_transformation,[],[f18])).
% 2.52/0.70  fof(f18,axiom,(
% 2.52/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.52/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.52/0.70  fof(f36,plain,(
% 2.52/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.52/0.70    inference(cnf_transformation,[],[f27])).
% 2.52/0.70  fof(f27,axiom,(
% 2.52/0.70    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.52/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.52/0.70  fof(f189,plain,(
% 2.52/0.70    ~spl2_7 | ~spl2_5),
% 2.52/0.70    inference(avatar_split_clause,[],[f164,f124,f186])).
% 2.52/0.70  fof(f186,plain,(
% 2.52/0.70    spl2_7 <=> r2_xboole_0(sK1,k1_tarski(sK0))),
% 2.52/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.52/0.70  fof(f124,plain,(
% 2.52/0.70    spl2_5 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 2.52/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.52/0.70  fof(f164,plain,(
% 2.52/0.70    ~r2_xboole_0(sK1,k1_tarski(sK0)) | ~spl2_5),
% 2.52/0.70    inference(superposition,[],[f73,f126])).
% 2.52/0.70  fof(f126,plain,(
% 2.52/0.70    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl2_5),
% 2.52/0.70    inference(avatar_component_clause,[],[f124])).
% 2.52/0.70  fof(f73,plain,(
% 2.52/0.70    ( ! [X0,X1] : (~r2_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 2.52/0.70    inference(resolution,[],[f45,f49])).
% 2.52/0.70  fof(f170,plain,(
% 2.52/0.70    spl2_6 | ~spl2_5),
% 2.52/0.70    inference(avatar_split_clause,[],[f151,f124,f167])).
% 2.52/0.70  fof(f151,plain,(
% 2.52/0.70    r1_tarski(k1_tarski(sK0),sK1) | ~spl2_5),
% 2.52/0.70    inference(superposition,[],[f49,f126])).
% 2.52/0.70  fof(f127,plain,(
% 2.52/0.70    spl2_4 | spl2_5 | ~spl2_2),
% 2.52/0.70    inference(avatar_split_clause,[],[f112,f68,f124,f120])).
% 2.52/0.70  fof(f68,plain,(
% 2.52/0.70    spl2_2 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.52/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.52/0.70  fof(f112,plain,(
% 2.52/0.70    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | r2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl2_2),
% 2.52/0.70    inference(resolution,[],[f48,f70])).
% 2.52/0.70  fof(f70,plain,(
% 2.52/0.70    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl2_2),
% 2.52/0.70    inference(avatar_component_clause,[],[f68])).
% 2.52/0.70  fof(f48,plain,(
% 2.52/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 2.52/0.70    inference(cnf_transformation,[],[f3])).
% 2.52/0.70  fof(f80,plain,(
% 2.52/0.70    ~spl2_3 | ~spl2_2),
% 2.52/0.70    inference(avatar_split_clause,[],[f72,f68,f77])).
% 2.52/0.70  fof(f77,plain,(
% 2.52/0.70    spl2_3 <=> r2_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))),
% 2.52/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.52/0.70  fof(f72,plain,(
% 2.52/0.70    ~r2_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) | ~spl2_2),
% 2.52/0.70    inference(resolution,[],[f45,f70])).
% 2.52/0.70  fof(f71,plain,(
% 2.52/0.70    spl2_2),
% 2.52/0.70    inference(avatar_split_clause,[],[f34,f68])).
% 2.52/0.70  fof(f34,plain,(
% 2.52/0.70    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.52/0.70    inference(cnf_transformation,[],[f30])).
% 2.52/0.70  fof(f30,plain,(
% 2.52/0.70    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 2.52/0.70    inference(ennf_transformation,[],[f29])).
% 2.52/0.70  fof(f29,negated_conjecture,(
% 2.52/0.70    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.52/0.70    inference(negated_conjecture,[],[f28])).
% 2.52/0.70  fof(f28,conjecture,(
% 2.52/0.70    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.52/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 2.52/0.70  fof(f66,plain,(
% 2.52/0.70    ~spl2_1),
% 2.52/0.70    inference(avatar_split_clause,[],[f35,f63])).
% 2.52/0.70  fof(f35,plain,(
% 2.52/0.70    ~r2_hidden(sK0,sK1)),
% 2.52/0.70    inference(cnf_transformation,[],[f30])).
% 2.52/0.70  % SZS output end Proof for theBenchmark
% 2.52/0.70  % (26684)------------------------------
% 2.52/0.70  % (26684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.70  % (26684)Termination reason: Refutation
% 2.52/0.70  
% 2.52/0.70  % (26684)Memory used [KB]: 6268
% 2.52/0.70  % (26684)Time elapsed: 0.291 s
% 2.52/0.70  % (26684)------------------------------
% 2.52/0.70  % (26684)------------------------------
% 2.52/0.70  % (26682)Success in time 0.345 s
%------------------------------------------------------------------------------
