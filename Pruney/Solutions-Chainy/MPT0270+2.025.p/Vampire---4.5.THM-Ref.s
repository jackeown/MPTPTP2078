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
% DateTime   : Thu Dec  3 12:40:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 247 expanded)
%              Number of equality atoms :   25 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f50,f177,f811])).

fof(f811,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f810])).

fof(f810,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f772,f279])).

fof(f279,plain,
    ( ~ r2_hidden(sK3(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f215,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f215,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f27,f180,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f180,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f48,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f772,plain,
    ( r2_hidden(sK3(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f278,f731,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f731,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_tarski(sK0))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f729])).

fof(f729,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_tarski(sK0))
        | ~ r2_hidden(X4,k1_tarski(sK0)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f37,f242])).

fof(f242,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f212,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f212,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f181,f43])).

fof(f43,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f181,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK1))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f278,plain,
    ( r2_hidden(sK3(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f215,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f177,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f175,f154])).

fof(f154,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f153,f92])).

fof(f92,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X4,k1_tarski(sK0)) )
    | spl4_2 ),
    inference(superposition,[],[f37,f54])).

fof(f54,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f47,f28])).

fof(f47,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f153,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl4_1 ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,
    ( ! [X2] :
        ( k1_tarski(sK0) != X2
        | ~ r2_hidden(sK2(k1_tarski(sK0),sK1,X2),sK1)
        | r2_hidden(sK2(k1_tarski(sK0),sK1,X2),X2) )
    | spl4_1 ),
    inference(superposition,[],[f44,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f175,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f174,f164])).

fof(f164,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl4_1 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl4_1 ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,
    ( ! [X1] :
        ( k1_tarski(sK0) != X1
        | r2_hidden(sK2(k1_tarski(sK0),sK1,X1),k1_tarski(sK0))
        | r2_hidden(sK2(k1_tarski(sK0),sK1,X1),X1) )
    | spl4_1 ),
    inference(superposition,[],[f44,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f174,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | spl4_1 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl4_1 ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) != X0
        | ~ r2_hidden(sK2(k1_tarski(sK0),sK1,X0),k1_tarski(sK0))
        | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),sK1)
        | ~ r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0) )
    | spl4_1 ),
    inference(superposition,[],[f44,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f19,f46,f42])).

fof(f19,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f49,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f20,f46,f42])).

fof(f20,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:13:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (18559)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (18571)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (18558)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (18554)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (18555)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (18560)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (18577)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (18563)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (18564)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (18569)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (18556)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (18561)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (18566)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (18557)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (18568)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (18574)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (18570)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (18572)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (18567)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (18576)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (18578)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (18581)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (18562)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (18583)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (18582)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (18579)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (18573)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (18580)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (18575)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (18575)Refutation not found, incomplete strategy% (18575)------------------------------
% 0.20/0.54  % (18575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18575)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18575)Memory used [KB]: 1791
% 0.20/0.54  % (18575)Time elapsed: 0.149 s
% 0.20/0.54  % (18575)------------------------------
% 0.20/0.54  % (18575)------------------------------
% 0.20/0.55  % (18565)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (18563)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f816,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f49,f50,f177,f811])).
% 0.20/0.56  fof(f811,plain,(
% 0.20/0.56    ~spl4_1 | ~spl4_2),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f810])).
% 0.20/0.56  fof(f810,plain,(
% 0.20/0.56    $false | (~spl4_1 | ~spl4_2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f772,f279])).
% 0.20/0.56  fof(f279,plain,(
% 0.20/0.56    ~r2_hidden(sK3(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),k4_xboole_0(sK1,k1_tarski(sK0))) | ~spl4_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f215,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f215,plain,(
% 0.20/0.56    ~r1_tarski(sK1,k4_xboole_0(sK1,k1_tarski(sK0))) | ~spl4_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f27,f180,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f180,plain,(
% 0.20/0.56    sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f48,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    r2_hidden(sK0,sK1) | ~spl4_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    spl4_2 <=> r2_hidden(sK0,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.56  fof(f772,plain,(
% 0.20/0.56    r2_hidden(sK3(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),k4_xboole_0(sK1,k1_tarski(sK0))) | (~spl4_1 | ~spl4_2)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f278,f731,f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(equality_resolution,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.56  fof(f731,plain,(
% 0.20/0.56    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK0))) ) | (~spl4_1 | ~spl4_2)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f729])).
% 0.20/0.56  fof(f729,plain,(
% 0.20/0.56    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK0)) | ~r2_hidden(X4,k1_tarski(sK0))) ) | (~spl4_1 | ~spl4_2)),
% 0.20/0.56    inference(superposition,[],[f37,f242])).
% 0.20/0.56  fof(f242,plain,(
% 0.20/0.56    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (~spl4_1 | ~spl4_2)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f212,f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f212,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k1_tarski(sK0)) | (~spl4_1 | ~spl4_2)),
% 0.20/0.56    inference(superposition,[],[f181,f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    spl4_1 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.56  fof(f181,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1))) ) | ~spl4_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f48,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(equality_resolution,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f278,plain,(
% 0.20/0.56    r2_hidden(sK3(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),sK1) | ~spl4_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f215,f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f177,plain,(
% 0.20/0.56    spl4_1 | spl4_2),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f176])).
% 0.20/0.56  fof(f176,plain,(
% 0.20/0.56    $false | (spl4_1 | spl4_2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f175,f154])).
% 0.20/0.56  fof(f154,plain,(
% 0.20/0.56    ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | (spl4_1 | spl4_2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f153,f92])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    ( ! [X4] : (~r2_hidden(X4,sK1) | ~r2_hidden(X4,k1_tarski(sK0))) ) | spl4_2),
% 0.20/0.56    inference(superposition,[],[f37,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) | spl4_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f47,f28])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ~r2_hidden(sK0,sK1) | spl4_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f46])).
% 0.20/0.56  fof(f153,plain,(
% 0.20/0.56    ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl4_1),
% 0.20/0.56    inference(equality_resolution,[],[f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X2] : (k1_tarski(sK0) != X2 | ~r2_hidden(sK2(k1_tarski(sK0),sK1,X2),sK1) | r2_hidden(sK2(k1_tarski(sK0),sK1,X2),X2)) ) | spl4_1),
% 0.20/0.56    inference(superposition,[],[f44,f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl4_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f42])).
% 0.20/0.56  fof(f175,plain,(
% 0.20/0.56    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | spl4_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f174,f164])).
% 0.20/0.56  fof(f164,plain,(
% 0.20/0.56    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl4_1),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f163])).
% 0.20/0.56  fof(f163,plain,(
% 0.20/0.56    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl4_1),
% 0.20/0.56    inference(equality_resolution,[],[f63])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ( ! [X1] : (k1_tarski(sK0) != X1 | r2_hidden(sK2(k1_tarski(sK0),sK1,X1),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,X1),X1)) ) | spl4_1),
% 0.20/0.56    inference(superposition,[],[f44,f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f174,plain,(
% 0.20/0.56    ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | spl4_1),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f173])).
% 0.20/0.56  fof(f173,plain,(
% 0.20/0.56    ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl4_1),
% 0.20/0.56    inference(equality_resolution,[],[f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X0] : (k1_tarski(sK0) != X0 | ~r2_hidden(sK2(k1_tarski(sK0),sK1,X0),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),sK1) | ~r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0)) ) | spl4_1),
% 0.20/0.56    inference(superposition,[],[f44,f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    spl4_1 | ~spl4_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f19,f46,f42])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(negated_conjecture,[],[f15])).
% 0.20/0.56  fof(f15,conjecture,(
% 0.20/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ~spl4_1 | spl4_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f20,f46,f42])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (18563)------------------------------
% 0.20/0.56  % (18563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18563)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (18563)Memory used [KB]: 11001
% 0.20/0.56  % (18563)Time elapsed: 0.144 s
% 0.20/0.56  % (18563)------------------------------
% 0.20/0.56  % (18563)------------------------------
% 0.20/0.56  % (18553)Success in time 0.209 s
%------------------------------------------------------------------------------
