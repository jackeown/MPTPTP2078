%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 507 expanded)
%              Number of leaves         :    7 ( 147 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 (1337 expanded)
%              Number of equality atoms :   21 ( 152 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f280,f524])).

fof(f524,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f460,f460,f458,f32])).

% (28249)Refutation not found, incomplete strategy% (28249)------------------------------
% (28249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28249)Termination reason: Refutation not found, incomplete strategy

% (28249)Memory used [KB]: 10618
% (28249)Time elapsed: 0.147 s
% (28249)------------------------------
% (28249)------------------------------
fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f458,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl11_2 ),
    inference(backward_demodulation,[],[f18,f447])).

fof(f447,plain,
    ( k1_xboole_0 = sK1
    | spl11_2 ),
    inference(superposition,[],[f394,f40])).

% (28238)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f21])).

% (28243)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f394,plain,
    ( ! [X0] : sK1 = k2_zfmisc_1(sK1,X0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f380,f380,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f380,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f283,f312,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f312,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f17,f297,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f297,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f284,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f284,plain,
    ( ~ r2_hidden(sK4(sK0,sK2),sK2)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f58,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl11_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f17,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f283,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f58,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f460,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_2 ),
    inference(backward_demodulation,[],[f380,f447])).

fof(f280,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f218,f218,f217,f31])).

fof(f217,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl11_1 ),
    inference(backward_demodulation,[],[f18,f206])).

fof(f206,plain,
    ( k1_xboole_0 = sK0
    | spl11_1 ),
    inference(superposition,[],[f145,f40])).

fof(f145,plain,
    ( ! [X0] : sK0 = k2_zfmisc_1(sK0,X0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f101,f101,f31])).

fof(f101,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f60,f94,f29])).

fof(f94,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f17,f71,f24])).

fof(f71,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f61,plain,
    ( ~ r2_hidden(sK4(sK1,sK3),sK3)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f54,f26])).

fof(f54,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl11_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f60,plain,
    ( r2_hidden(sK4(sK1,sK3),sK1)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f54,f25])).

fof(f218,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_1 ),
    inference(backward_demodulation,[],[f101,f206])).

fof(f59,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f16,f56,f52])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (28254)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (28245)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (28237)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (28254)Refutation not found, incomplete strategy% (28254)------------------------------
% 0.22/0.52  % (28254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28241)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (28254)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28254)Memory used [KB]: 10746
% 0.22/0.52  % (28254)Time elapsed: 0.069 s
% 0.22/0.52  % (28254)------------------------------
% 0.22/0.52  % (28254)------------------------------
% 0.22/0.52  % (28242)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (28231)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (28235)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (28236)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (28232)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (28233)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (28258)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (28234)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (28233)Refutation not found, incomplete strategy% (28233)------------------------------
% 0.22/0.54  % (28233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28233)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28233)Memory used [KB]: 10618
% 0.22/0.54  % (28233)Time elapsed: 0.134 s
% 0.22/0.54  % (28233)------------------------------
% 0.22/0.54  % (28233)------------------------------
% 0.22/0.54  % (28260)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (28255)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (28244)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (28261)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (28256)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (28246)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (28252)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (28247)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (28253)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (28249)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (28257)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (28235)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f527,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f59,f280,f524])).
% 0.22/0.55  fof(f524,plain,(
% 0.22/0.55    spl11_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f518])).
% 0.22/0.55  fof(f518,plain,(
% 0.22/0.55    $false | spl11_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f460,f460,f458,f32])).
% 0.22/0.55  % (28249)Refutation not found, incomplete strategy% (28249)------------------------------
% 0.22/0.55  % (28249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28249)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28249)Memory used [KB]: 10618
% 0.22/0.55  % (28249)Time elapsed: 0.147 s
% 0.22/0.55  % (28249)------------------------------
% 0.22/0.55  % (28249)------------------------------
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.55  fof(f458,plain,(
% 0.22/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl11_2),
% 0.22/0.55    inference(backward_demodulation,[],[f18,f447])).
% 0.22/0.55  fof(f447,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | spl11_2),
% 0.22/0.55    inference(superposition,[],[f394,f40])).
% 0.22/0.56  % (28238)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f21])).
% 0.22/0.56  % (28243)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f394,plain,(
% 0.22/0.56    ( ! [X0] : (sK1 = k2_zfmisc_1(sK1,X0)) ) | spl11_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f380,f380,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f380,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl11_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f283,f312,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.56  fof(f312,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ) | spl11_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f17,f297,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f297,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl11_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f284,f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f284,plain,(
% 0.22/0.56    ~r2_hidden(sK4(sK0,sK2),sK2) | spl11_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f58,f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK2) | spl11_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    spl11_2 <=> r1_tarski(sK0,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.56    inference(flattening,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(negated_conjecture,[],[f9])).
% 0.22/0.56  fof(f9,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.22/0.56  fof(f283,plain,(
% 0.22/0.56    r2_hidden(sK4(sK0,sK2),sK0) | spl11_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f58,f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f460,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_2),
% 0.22/0.56    inference(backward_demodulation,[],[f380,f447])).
% 0.22/0.56  fof(f280,plain,(
% 0.22/0.56    spl11_1),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f273])).
% 0.22/0.56  fof(f273,plain,(
% 0.22/0.56    $false | spl11_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f218,f218,f217,f31])).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl11_1),
% 0.22/0.56    inference(backward_demodulation,[],[f18,f206])).
% 0.22/0.56  fof(f206,plain,(
% 0.22/0.56    k1_xboole_0 = sK0 | spl11_1),
% 0.22/0.56    inference(superposition,[],[f145,f40])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    ( ! [X0] : (sK0 = k2_zfmisc_1(sK0,X0)) ) | spl11_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f101,f101,f31])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl11_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f60,f94,f29])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) ) | spl11_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f17,f71,f24])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl11_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f61,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ~r2_hidden(sK4(sK1,sK3),sK3) | spl11_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f54,f26])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ~r1_tarski(sK1,sK3) | spl11_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    spl11_1 <=> r1_tarski(sK1,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    r2_hidden(sK4(sK1,sK3),sK1) | spl11_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f54,f25])).
% 0.22/0.56  fof(f218,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_1),
% 0.22/0.56    inference(backward_demodulation,[],[f101,f206])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ~spl11_1 | ~spl11_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f16,f56,f52])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (28235)------------------------------
% 0.22/0.56  % (28235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28235)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (28235)Memory used [KB]: 6396
% 0.22/0.56  % (28235)Time elapsed: 0.129 s
% 0.22/0.56  % (28235)------------------------------
% 0.22/0.56  % (28235)------------------------------
% 0.22/0.56  % (28240)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (28227)Success in time 0.192 s
%------------------------------------------------------------------------------
