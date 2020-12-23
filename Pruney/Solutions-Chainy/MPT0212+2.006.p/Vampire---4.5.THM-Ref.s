%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  92 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 149 expanded)
%              Number of equality atoms :   39 (  75 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f75,f90,f100])).

fof(f100,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f85,f92])).

fof(f92,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_1
    | spl2_2 ),
    inference(forward_demodulation,[],[f64,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f64,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_4
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f90,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f44,f86,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f86,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f44,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f24,f12])).

fof(f12,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f75,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f65,f28,f68,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f26])).

% (24557)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (24565)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (24565)Refutation not found, incomplete strategy% (24565)------------------------------
% (24565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24565)Termination reason: Refutation not found, incomplete strategy

% (24565)Memory used [KB]: 1663
% (24565)Time elapsed: 0.110 s
% (24565)------------------------------
% (24565)------------------------------
% (24570)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (24575)Refutation not found, incomplete strategy% (24575)------------------------------
% (24575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24575)Termination reason: Refutation not found, incomplete strategy

% (24575)Memory used [KB]: 6140
% (24573)Refutation not found, incomplete strategy% (24573)------------------------------
% (24573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24573)Termination reason: Refutation not found, incomplete strategy

% (24573)Memory used [KB]: 6140
% (24573)Time elapsed: 0.108 s
% (24573)------------------------------
% (24573)------------------------------
% (24575)Time elapsed: 0.103 s
% (24575)------------------------------
% (24575)------------------------------
% (24549)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (24549)Refutation not found, incomplete strategy% (24549)------------------------------
% (24549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24549)Termination reason: Refutation not found, incomplete strategy

% (24549)Memory used [KB]: 1663
% (24549)Time elapsed: 0.116 s
% (24549)------------------------------
% (24549)------------------------------
% (24554)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (24550)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (24548)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (24568)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (24551)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (24562)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (24553)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (24562)Refutation not found, incomplete strategy% (24562)------------------------------
% (24562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24562)Termination reason: Refutation not found, incomplete strategy

% (24562)Memory used [KB]: 1663
% (24562)Time elapsed: 0.089 s
% (24562)------------------------------
% (24562)------------------------------
% (24556)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (24563)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (24572)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f13,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f68,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_2 ),
    inference(resolution,[],[f67,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f23,f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f67,plain,
    ( r1_tarski(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl2_2 ),
    inference(resolution,[],[f65,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    k1_zfmisc_1(k1_xboole_0) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f11,f27])).

fof(f11,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(flattening,[],[f9])).

fof(f9,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f65,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f66,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f57,f63,f59])).

fof(f57,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X5] :
      ( k1_zfmisc_1(k1_xboole_0) != X5
      | r2_hidden(sK1(k1_xboole_0,X5),X5)
      | k1_xboole_0 = sK1(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK1(X0,X1),X1)
      | sK1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:15:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24559)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (24575)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.50  % (24552)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (24573)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (24560)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (24561)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (24567)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (24559)Refutation not found, incomplete strategy% (24559)------------------------------
% 0.20/0.51  % (24559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24559)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24559)Memory used [KB]: 6140
% 0.20/0.51  % (24559)Time elapsed: 0.103 s
% 0.20/0.51  % (24559)------------------------------
% 0.20/0.51  % (24559)------------------------------
% 0.20/0.51  % (24561)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f66,f75,f90,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ~spl2_1 | spl2_2 | ~spl2_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    $false | (~spl2_1 | spl2_2 | ~spl2_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f85,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl2_1 | spl2_2)),
% 0.20/0.51    inference(forward_demodulation,[],[f64,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl2_1 <=> k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ~r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    spl2_2 <=> r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl2_4 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl2_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    $false | spl2_4),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f44,f86,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f84])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.51    inference(equality_resolution,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(superposition,[],[f24,f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ~spl2_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    $false | ~spl2_2),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f65,f28,f68,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1) | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 0.20/0.51    inference(definition_unfolding,[],[f22,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f13,f26])).
% 0.20/0.51  % (24557)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (24565)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (24565)Refutation not found, incomplete strategy% (24565)------------------------------
% 0.20/0.51  % (24565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24565)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24565)Memory used [KB]: 1663
% 0.20/0.51  % (24565)Time elapsed: 0.110 s
% 0.20/0.51  % (24565)------------------------------
% 0.20/0.51  % (24565)------------------------------
% 0.20/0.51  % (24570)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (24575)Refutation not found, incomplete strategy% (24575)------------------------------
% 0.20/0.51  % (24575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24575)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24575)Memory used [KB]: 6140
% 0.20/0.51  % (24573)Refutation not found, incomplete strategy% (24573)------------------------------
% 0.20/0.51  % (24573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24573)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24573)Memory used [KB]: 6140
% 0.20/0.51  % (24573)Time elapsed: 0.108 s
% 0.20/0.51  % (24573)------------------------------
% 0.20/0.51  % (24573)------------------------------
% 0.20/0.51  % (24575)Time elapsed: 0.103 s
% 0.20/0.51  % (24575)------------------------------
% 0.20/0.51  % (24575)------------------------------
% 0.20/0.52  % (24549)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (24549)Refutation not found, incomplete strategy% (24549)------------------------------
% 0.20/0.52  % (24549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24549)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24549)Memory used [KB]: 1663
% 0.20/0.52  % (24549)Time elapsed: 0.116 s
% 0.20/0.52  % (24549)------------------------------
% 0.20/0.52  % (24549)------------------------------
% 0.20/0.52  % (24554)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (24550)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (24548)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (24568)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (24551)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (24562)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (24553)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (24562)Refutation not found, incomplete strategy% (24562)------------------------------
% 0.20/0.53  % (24562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24562)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24562)Memory used [KB]: 1663
% 0.20/0.53  % (24562)Time elapsed: 0.089 s
% 0.20/0.53  % (24562)------------------------------
% 0.20/0.53  % (24562)------------------------------
% 0.20/0.53  % (24556)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (24563)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (24572)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f14,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl2_2),
% 0.20/0.53    inference(resolution,[],[f67,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(superposition,[],[f23,f12])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    r1_tarski(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) | ~spl2_2),
% 0.20/0.53    inference(resolution,[],[f65,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    k1_zfmisc_1(k1_xboole_0) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    inference(definition_unfolding,[],[f11,f27])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.20/0.53    inference(flattening,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~spl2_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f63])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl2_1 | spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f57,f63,f59])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.53    inference(equality_resolution,[],[f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X5] : (k1_zfmisc_1(k1_xboole_0) != X5 | r2_hidden(sK1(k1_xboole_0,X5),X5) | k1_xboole_0 = sK1(k1_xboole_0,X5)) )),
% 0.20/0.53    inference(superposition,[],[f28,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f21,f27])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (24561)------------------------------
% 0.20/0.53  % (24561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24561)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (24561)Memory used [KB]: 6268
% 0.20/0.53  % (24561)Time elapsed: 0.110 s
% 0.20/0.53  % (24561)------------------------------
% 0.20/0.53  % (24561)------------------------------
% 0.20/0.53  % (24572)Refutation not found, incomplete strategy% (24572)------------------------------
% 0.20/0.53  % (24572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24572)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24572)Memory used [KB]: 10618
% 0.20/0.53  % (24572)Time elapsed: 0.130 s
% 0.20/0.53  % (24572)------------------------------
% 0.20/0.53  % (24572)------------------------------
% 0.20/0.53  % (24547)Success in time 0.177 s
%------------------------------------------------------------------------------
