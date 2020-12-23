%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:43 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
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
fof(f530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f283,f527])).

fof(f527,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f521])).

fof(f521,plain,
    ( $false
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f463,f463,f461,f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f461,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl11_2 ),
    inference(backward_demodulation,[],[f18,f450])).

fof(f450,plain,
    ( k1_xboole_0 = sK1
    | spl11_2 ),
    inference(superposition,[],[f397,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f21])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f397,plain,
    ( ! [X0] : sK1 = k2_zfmisc_1(sK1,X0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f383,f383,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f383,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f286,f315,f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f315,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f17,f300,f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f300,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f287,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f287,plain,
    ( ~ r2_hidden(sK4(sK0,sK2),sK2)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f61,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f286,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f61,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f463,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_2 ),
    inference(backward_demodulation,[],[f383,f450])).

fof(f283,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f221,f221,f220,f31])).

fof(f220,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl11_1 ),
    inference(backward_demodulation,[],[f18,f209])).

fof(f209,plain,
    ( k1_xboole_0 = sK0
    | spl11_1 ),
    inference(superposition,[],[f148,f43])).

fof(f148,plain,
    ( ! [X0] : sK0 = k2_zfmisc_1(sK0,X0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f104,f104,f31])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f63,f97,f29])).

fof(f97,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f17,f74,f24])).

fof(f74,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f64,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,
    ( ~ r2_hidden(sK4(sK1,sK3),sK3)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f57,f26])).

fof(f57,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl11_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f63,plain,
    ( r2_hidden(sK4(sK1,sK3),sK1)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f57,f25])).

fof(f221,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_1 ),
    inference(backward_demodulation,[],[f104,f209])).

fof(f62,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f16,f59,f55])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:38:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (10778)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (10788)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (10785)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (10805)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (10779)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (10783)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (10790)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (10799)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (10795)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (10777)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (10777)Refutation not found, incomplete strategy% (10777)------------------------------
% 0.21/0.53  % (10777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10777)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10777)Memory used [KB]: 10618
% 0.21/0.53  % (10777)Time elapsed: 0.112 s
% 0.21/0.53  % (10777)------------------------------
% 0.21/0.53  % (10777)------------------------------
% 0.21/0.53  % (10780)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (10801)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (10782)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (10796)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (10798)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (10786)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (10793)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (10794)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (10793)Refutation not found, incomplete strategy% (10793)------------------------------
% 0.21/0.54  % (10793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10784)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (10776)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (10797)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (10789)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (10803)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10787)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (10781)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (10802)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (10800)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (10806)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.55  % (10793)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (10793)Memory used [KB]: 10618
% 1.46/0.55  % (10793)Time elapsed: 0.127 s
% 1.46/0.55  % (10793)------------------------------
% 1.46/0.55  % (10793)------------------------------
% 1.46/0.55  % (10775)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.46/0.55  % (10779)Refutation found. Thanks to Tanya!
% 1.46/0.55  % SZS status Theorem for theBenchmark
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  fof(f530,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(avatar_sat_refutation,[],[f62,f283,f527])).
% 1.46/0.55  fof(f527,plain,(
% 1.46/0.55    spl11_2),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f521])).
% 1.46/0.55  fof(f521,plain,(
% 1.46/0.55    $false | spl11_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f463,f463,f461,f32])).
% 1.46/0.55  fof(f32,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.46/0.55    inference(cnf_transformation,[],[f6])).
% 1.46/0.55  fof(f6,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.46/0.55  fof(f461,plain,(
% 1.46/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl11_2),
% 1.46/0.55    inference(backward_demodulation,[],[f18,f450])).
% 1.46/0.55  fof(f450,plain,(
% 1.46/0.55    k1_xboole_0 = sK1 | spl11_2),
% 1.46/0.55    inference(superposition,[],[f397,f43])).
% 1.46/0.55  fof(f43,plain,(
% 1.46/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.46/0.55    inference(equality_resolution,[],[f21])).
% 1.46/0.55  fof(f21,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f8])).
% 1.46/0.55  fof(f8,axiom,(
% 1.46/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.46/0.55  fof(f397,plain,(
% 1.46/0.55    ( ! [X0] : (sK1 = k2_zfmisc_1(sK1,X0)) ) | spl11_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f383,f383,f31])).
% 1.46/0.55  fof(f31,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.46/0.55    inference(cnf_transformation,[],[f6])).
% 1.46/0.55  fof(f383,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl11_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f286,f315,f29])).
% 1.46/0.55  fof(f29,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f7])).
% 1.46/0.55  fof(f7,axiom,(
% 1.46/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.46/0.55  fof(f315,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ) | spl11_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f17,f300,f24])).
% 1.46/0.55  fof(f24,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f14])).
% 1.46/0.55  fof(f14,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.55  fof(f300,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl11_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f287,f27])).
% 1.46/0.55  fof(f27,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f7])).
% 1.46/0.55  fof(f287,plain,(
% 1.46/0.55    ~r2_hidden(sK4(sK0,sK2),sK2) | spl11_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f61,f26])).
% 1.46/0.55  fof(f26,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f14])).
% 1.46/0.55  fof(f61,plain,(
% 1.46/0.55    ~r1_tarski(sK0,sK2) | spl11_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f59])).
% 1.46/0.55  fof(f59,plain,(
% 1.46/0.55    spl11_2 <=> r1_tarski(sK0,sK2)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.46/0.55  fof(f17,plain,(
% 1.46/0.55    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.46/0.55    inference(cnf_transformation,[],[f13])).
% 1.46/0.55  fof(f13,plain,(
% 1.46/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.46/0.55    inference(flattening,[],[f12])).
% 1.46/0.55  fof(f12,plain,(
% 1.46/0.55    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.46/0.55    inference(ennf_transformation,[],[f10])).
% 1.46/0.55  fof(f10,negated_conjecture,(
% 1.46/0.55    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.46/0.55    inference(negated_conjecture,[],[f9])).
% 1.46/0.55  fof(f9,conjecture,(
% 1.46/0.55    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.46/0.55  fof(f286,plain,(
% 1.46/0.55    r2_hidden(sK4(sK0,sK2),sK0) | spl11_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f61,f25])).
% 1.46/0.55  fof(f25,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f14])).
% 1.46/0.55  fof(f18,plain,(
% 1.46/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f13])).
% 1.46/0.55  fof(f463,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_2),
% 1.46/0.55    inference(backward_demodulation,[],[f383,f450])).
% 1.46/0.55  fof(f283,plain,(
% 1.46/0.55    spl11_1),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f276])).
% 1.46/0.55  fof(f276,plain,(
% 1.46/0.55    $false | spl11_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f221,f221,f220,f31])).
% 1.46/0.55  fof(f220,plain,(
% 1.46/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl11_1),
% 1.46/0.55    inference(backward_demodulation,[],[f18,f209])).
% 1.46/0.55  fof(f209,plain,(
% 1.46/0.55    k1_xboole_0 = sK0 | spl11_1),
% 1.46/0.55    inference(superposition,[],[f148,f43])).
% 1.46/0.55  fof(f148,plain,(
% 1.46/0.55    ( ! [X0] : (sK0 = k2_zfmisc_1(sK0,X0)) ) | spl11_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f104,f104,f31])).
% 1.46/0.55  fof(f104,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl11_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f63,f97,f29])).
% 1.46/0.55  fof(f97,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) ) | spl11_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f17,f74,f24])).
% 1.46/0.55  fof(f74,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl11_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f64,f28])).
% 1.46/0.55  fof(f28,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f7])).
% 1.46/0.55  fof(f64,plain,(
% 1.46/0.55    ~r2_hidden(sK4(sK1,sK3),sK3) | spl11_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f57,f26])).
% 1.46/0.55  fof(f57,plain,(
% 1.46/0.55    ~r1_tarski(sK1,sK3) | spl11_1),
% 1.46/0.55    inference(avatar_component_clause,[],[f55])).
% 1.46/0.55  fof(f55,plain,(
% 1.46/0.55    spl11_1 <=> r1_tarski(sK1,sK3)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.46/0.55  fof(f63,plain,(
% 1.46/0.55    r2_hidden(sK4(sK1,sK3),sK1) | spl11_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f57,f25])).
% 1.46/0.55  fof(f221,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_1),
% 1.46/0.55    inference(backward_demodulation,[],[f104,f209])).
% 1.46/0.55  fof(f62,plain,(
% 1.46/0.55    ~spl11_1 | ~spl11_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f16,f59,f55])).
% 1.46/0.55  fof(f16,plain,(
% 1.46/0.55    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 1.46/0.55    inference(cnf_transformation,[],[f13])).
% 1.46/0.55  % SZS output end Proof for theBenchmark
% 1.46/0.55  % (10779)------------------------------
% 1.46/0.55  % (10779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (10779)Termination reason: Refutation
% 1.46/0.55  
% 1.46/0.55  % (10779)Memory used [KB]: 6396
% 1.46/0.55  % (10779)Time elapsed: 0.145 s
% 1.46/0.55  % (10779)------------------------------
% 1.46/0.55  % (10779)------------------------------
% 1.46/0.55  % (10774)Success in time 0.193 s
%------------------------------------------------------------------------------
