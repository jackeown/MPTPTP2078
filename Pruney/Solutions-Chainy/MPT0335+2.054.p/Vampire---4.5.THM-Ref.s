%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 120 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  142 ( 331 expanded)
%              Number of equality atoms :   25 (  98 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f605,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f311,f495,f501,f548,f604])).

fof(f604,plain,
    ( spl5_9
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f602,f305])).

fof(f305,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl5_9
  <=> r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f602,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f597,f514])).

fof(f514,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK1)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f310,f86])).

fof(f86,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK1)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(superposition,[],[f31,f33])).

fof(f33,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f17,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f310,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl5_10
  <=> r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f597,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK1)
    | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | spl5_9 ),
    inference(resolution,[],[f551,f53])).

fof(f53,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,k1_tarski(sK3)) ) ),
    inference(superposition,[],[f30,f18])).

fof(f18,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f551,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f312,f305])).

fof(f312,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)
    | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2] :
      ( k1_tarski(sK3) != X2
      | r2_hidden(sK4(sK0,sK2,X2),sK2)
      | r2_hidden(sK4(sK0,sK2,X2),X2) ) ),
    inference(superposition,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f548,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f536,f546])).

fof(f546,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | spl5_11 ),
    inference(subsumption_resolution,[],[f540,f20])).

fof(f540,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | spl5_11 ),
    inference(resolution,[],[f500,f23])).

fof(f500,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl5_11
  <=> r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f536,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f500,f54])).

fof(f54,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_tarski(sK3))
      | r2_hidden(X4,sK2) ) ),
    inference(superposition,[],[f31,f18])).

fof(f501,plain,
    ( ~ spl5_11
    | ~ spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f496,f304,f308,f498])).

fof(f496,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f343,f306])).

fof(f306,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f304])).

fof(f343,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)
    | ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_tarski(sK3) != X0
      | ~ r2_hidden(sK4(sK0,sK2,X0),sK0)
      | ~ r2_hidden(sK4(sK0,sK2,X0),sK2)
      | ~ r2_hidden(sK4(sK0,sK2,X0),X0) ) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f495,plain,
    ( ~ spl5_9
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f486,f306])).

fof(f486,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f309,f351])).

fof(f351,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_tarski(sK3))
      | r2_hidden(X4,sK0) ) ),
    inference(superposition,[],[f31,f42])).

fof(f42,plain,(
    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f35,f29])).

fof(f35,plain,(
    r1_tarski(k1_tarski(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f19,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f19,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f309,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f308])).

fof(f311,plain,
    ( spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f291,f308,f304])).

fof(f291,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)
    | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X1] :
      ( k1_tarski(sK3) != X1
      | r2_hidden(sK4(sK0,sK2,X1),sK0)
      | r2_hidden(sK4(sK0,sK2,X1),X1) ) ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (9300)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (9314)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (9317)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (9306)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (9297)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (9309)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (9296)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (9290)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (9295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (9311)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (9299)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (9302)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (9292)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (9293)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (9289)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (9303)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (9291)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (9303)Refutation not found, incomplete strategy% (9303)------------------------------
% 0.21/0.53  % (9303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9303)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9303)Memory used [KB]: 6140
% 0.21/0.53  % (9303)Time elapsed: 0.001 s
% 0.21/0.53  % (9303)------------------------------
% 0.21/0.53  % (9303)------------------------------
% 0.21/0.53  % (9294)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (9288)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (9316)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (9313)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (9318)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (9307)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (9308)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (9310)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (9312)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (9298)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (9305)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (9301)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (9315)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (9297)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f605,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f311,f495,f501,f548,f604])).
% 0.21/0.55  fof(f604,plain,(
% 0.21/0.55    spl5_9 | ~spl5_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f603])).
% 0.21/0.55  fof(f603,plain,(
% 0.21/0.55    $false | (spl5_9 | ~spl5_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f602,f305])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) | spl5_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f304])).
% 0.21/0.55  fof(f304,plain,(
% 0.21/0.55    spl5_9 <=> r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.55  fof(f602,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) | (spl5_9 | ~spl5_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f597,f514])).
% 0.21/0.55  fof(f514,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK1) | ~spl5_10),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f310,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X4] : (r2_hidden(X4,sK1) | ~r2_hidden(X4,sK0)) )),
% 0.21/0.55    inference(superposition,[],[f31,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f17,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.55  fof(f310,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) | ~spl5_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f308])).
% 0.21/0.55  fof(f308,plain,(
% 0.21/0.55    spl5_10 <=> r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.55  fof(f597,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK1) | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) | spl5_9),
% 0.21/0.55    inference(resolution,[],[f551,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(X3,k1_tarski(sK3))) )),
% 0.21/0.55    inference(superposition,[],[f30,f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f551,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) | spl5_9),
% 0.21/0.55    inference(subsumption_resolution,[],[f312,f305])).
% 0.21/0.55  fof(f312,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 0.21/0.55    inference(equality_resolution,[],[f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X2] : (k1_tarski(sK3) != X2 | r2_hidden(sK4(sK0,sK2,X2),sK2) | r2_hidden(sK4(sK0,sK2,X2),X2)) )),
% 0.21/0.55    inference(superposition,[],[f20,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f548,plain,(
% 0.21/0.55    spl5_11),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f547])).
% 0.21/0.55  fof(f547,plain,(
% 0.21/0.55    $false | spl5_11),
% 0.21/0.55    inference(subsumption_resolution,[],[f536,f546])).
% 0.21/0.55  fof(f546,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) | spl5_11),
% 0.21/0.55    inference(subsumption_resolution,[],[f540,f20])).
% 0.21/0.55  fof(f540,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) | k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | spl5_11),
% 0.21/0.55    inference(resolution,[],[f500,f23])).
% 0.21/0.55  fof(f500,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) | spl5_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f498])).
% 0.21/0.55  fof(f498,plain,(
% 0.21/0.55    spl5_11 <=> r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.55  fof(f536,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) | spl5_11),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f500,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK3)) | r2_hidden(X4,sK2)) )),
% 0.21/0.55    inference(superposition,[],[f31,f18])).
% 0.21/0.55  fof(f501,plain,(
% 0.21/0.55    ~spl5_11 | ~spl5_10 | ~spl5_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f496,f304,f308,f498])).
% 0.21/0.55  fof(f496,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) | ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) | ~spl5_9),
% 0.21/0.55    inference(subsumption_resolution,[],[f343,f306])).
% 0.21/0.55  fof(f306,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) | ~spl5_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f304])).
% 0.21/0.55  fof(f343,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) | ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) | ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 0.21/0.55    inference(equality_resolution,[],[f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(sK3) != X0 | ~r2_hidden(sK4(sK0,sK2,X0),sK0) | ~r2_hidden(sK4(sK0,sK2,X0),sK2) | ~r2_hidden(sK4(sK0,sK2,X0),X0)) )),
% 0.21/0.55    inference(superposition,[],[f20,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f495,plain,(
% 0.21/0.55    ~spl5_9 | spl5_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f494])).
% 0.21/0.55  fof(f494,plain,(
% 0.21/0.55    $false | (~spl5_9 | spl5_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f486,f306])).
% 0.21/0.55  fof(f486,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) | spl5_10),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f309,f351])).
% 0.21/0.55  fof(f351,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK3)) | r2_hidden(X4,sK0)) )),
% 0.21/0.55    inference(superposition,[],[f31,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f35,f29])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    r1_tarski(k1_tarski(sK3),sK0)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f19,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    r2_hidden(sK3,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f309,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) | spl5_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f308])).
% 0.21/0.55  fof(f311,plain,(
% 0.21/0.55    spl5_9 | spl5_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f291,f308,f304])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 0.21/0.55    inference(equality_resolution,[],[f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X1] : (k1_tarski(sK3) != X1 | r2_hidden(sK4(sK0,sK2,X1),sK0) | r2_hidden(sK4(sK0,sK2,X1),X1)) )),
% 0.21/0.55    inference(superposition,[],[f20,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (9297)------------------------------
% 0.21/0.55  % (9297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9297)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (9297)Memory used [KB]: 11001
% 0.21/0.55  % (9297)Time elapsed: 0.137 s
% 0.21/0.55  % (9297)------------------------------
% 0.21/0.55  % (9297)------------------------------
% 0.21/0.56  % (9287)Success in time 0.197 s
%------------------------------------------------------------------------------
