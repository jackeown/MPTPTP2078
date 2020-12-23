%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 335 expanded)
%              Number of leaves         :    5 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  122 ( 811 expanded)
%              Number of equality atoms :   57 ( 232 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f242])).

% (6022)Refutation not found, incomplete strategy% (6022)------------------------------
% (6022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6022)Termination reason: Refutation not found, incomplete strategy

% (6022)Memory used [KB]: 11001
% (6022)Time elapsed: 0.167 s
% (6022)------------------------------
% (6022)------------------------------
fof(f242,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f237,f166])).

fof(f166,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f147,f146])).

fof(f146,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f72,f86,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f86,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f79,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
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

fof(f79,plain,(
    ! [X0,X1] : ~ sP5(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f72,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f63,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f33,f17])).

fof(f17,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f32,f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f147,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f85,f86,f18])).

fof(f85,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f78,f35])).

fof(f78,plain,(
    ! [X0,X1] : ~ sP5(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f72,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f237,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f236,f231])).

fof(f231,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f146,f230])).

fof(f230,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f225])).

fof(f225,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f14,f221])).

fof(f221,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f215,f153])).

fof(f153,plain,(
    ! [X11] :
      ( r2_hidden(sK2(X11,k1_xboole_0),X11)
      | k1_xboole_0 = X11 ) ),
    inference(resolution,[],[f18,f72])).

fof(f215,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f208,f153])).

fof(f208,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X3,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f129,f72])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),k1_xboole_0)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f37,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ sP5(X0,sK1,sK0)
      | r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f36,f15])).

fof(f15,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( sP5(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f236,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f13,f231])).

fof(f13,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:10:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (6019)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.49  % (6011)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.49  % (6010)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (6011)Refutation not found, incomplete strategy% (6011)------------------------------
% 0.20/0.50  % (6011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6011)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6011)Memory used [KB]: 10618
% 0.20/0.50  % (6011)Time elapsed: 0.084 s
% 0.20/0.50  % (6011)------------------------------
% 0.20/0.50  % (6011)------------------------------
% 0.20/0.50  % (6026)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (6001)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (6010)Refutation not found, incomplete strategy% (6010)------------------------------
% 0.20/0.51  % (6010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6010)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6010)Memory used [KB]: 10618
% 0.20/0.51  % (6010)Time elapsed: 0.091 s
% 0.20/0.51  % (6010)------------------------------
% 0.20/0.51  % (6010)------------------------------
% 0.20/0.52  % (6012)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (6006)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (6028)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (6007)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (6020)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (6021)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (6021)Refutation not found, incomplete strategy% (6021)------------------------------
% 0.20/0.53  % (6021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6021)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6021)Memory used [KB]: 1663
% 0.20/0.53  % (6021)Time elapsed: 0.096 s
% 0.20/0.53  % (6021)------------------------------
% 0.20/0.53  % (6021)------------------------------
% 0.20/0.53  % (6029)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (6004)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (6004)Refutation not found, incomplete strategy% (6004)------------------------------
% 0.20/0.53  % (6004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6004)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6004)Memory used [KB]: 6268
% 0.20/0.53  % (6004)Time elapsed: 0.125 s
% 0.20/0.53  % (6004)------------------------------
% 0.20/0.53  % (6004)------------------------------
% 0.20/0.53  % (6022)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (6020)Refutation not found, incomplete strategy% (6020)------------------------------
% 0.20/0.53  % (6020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6018)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (6000)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (6015)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (6000)Refutation not found, incomplete strategy% (6000)------------------------------
% 0.20/0.53  % (6000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6000)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6000)Memory used [KB]: 1663
% 0.20/0.53  % (6000)Time elapsed: 0.136 s
% 0.20/0.53  % (6000)------------------------------
% 0.20/0.53  % (6000)------------------------------
% 0.20/0.54  % (6013)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (6003)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (6020)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6020)Memory used [KB]: 10746
% 0.20/0.54  % (6020)Time elapsed: 0.121 s
% 0.20/0.54  % (6020)------------------------------
% 0.20/0.54  % (6020)------------------------------
% 0.20/0.54  % (6014)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (6023)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (6008)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (6017)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (6005)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (6008)Refutation not found, incomplete strategy% (6008)------------------------------
% 0.20/0.54  % (6008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6008)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6008)Memory used [KB]: 10618
% 0.20/0.54  % (6008)Time elapsed: 0.146 s
% 0.20/0.54  % (6008)------------------------------
% 0.20/0.54  % (6008)------------------------------
% 0.20/0.54  % (6017)Refutation not found, incomplete strategy% (6017)------------------------------
% 0.20/0.54  % (6017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6017)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6017)Memory used [KB]: 10618
% 0.20/0.54  % (6017)Time elapsed: 0.148 s
% 0.20/0.54  % (6017)------------------------------
% 0.20/0.54  % (6017)------------------------------
% 0.20/0.55  % (6009)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (6009)Refutation not found, incomplete strategy% (6009)------------------------------
% 0.20/0.55  % (6009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6009)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6009)Memory used [KB]: 10618
% 0.20/0.55  % (6009)Time elapsed: 0.149 s
% 0.20/0.55  % (6009)------------------------------
% 0.20/0.55  % (6009)------------------------------
% 0.20/0.55  % (6016)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (6025)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (6025)Refutation not found, incomplete strategy% (6025)------------------------------
% 0.20/0.55  % (6025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6025)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6025)Memory used [KB]: 6268
% 0.20/0.55  % (6025)Time elapsed: 0.161 s
% 0.20/0.55  % (6025)------------------------------
% 0.20/0.55  % (6025)------------------------------
% 0.20/0.56  % (6027)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (6002)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (6002)Refutation not found, incomplete strategy% (6002)------------------------------
% 0.20/0.56  % (6002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (6002)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (6002)Memory used [KB]: 10618
% 0.20/0.56  % (6002)Time elapsed: 0.160 s
% 0.20/0.56  % (6002)------------------------------
% 0.20/0.56  % (6002)------------------------------
% 0.20/0.56  % (6024)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.57  % (6024)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f243,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f242])).
% 0.20/0.58  % (6022)Refutation not found, incomplete strategy% (6022)------------------------------
% 0.20/0.58  % (6022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (6022)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (6022)Memory used [KB]: 11001
% 0.20/0.58  % (6022)Time elapsed: 0.167 s
% 0.20/0.58  % (6022)------------------------------
% 0.20/0.58  % (6022)------------------------------
% 0.20/0.59  fof(f242,plain,(
% 0.20/0.59    k1_xboole_0 != k1_xboole_0),
% 0.20/0.59    inference(superposition,[],[f237,f166])).
% 0.20/0.59  fof(f166,plain,(
% 0.20/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.59    inference(backward_demodulation,[],[f147,f146])).
% 0.20/0.59  fof(f146,plain,(
% 0.20/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f72,f86,f18])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f10])).
% 0.20/0.59  fof(f10,plain,(
% 0.20/0.59    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.59  fof(f86,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f79,f35])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | sP5(X3,X1,X0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.59  fof(f79,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~sP5(X0,k1_xboole_0,X1)) )),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f72,f25])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~sP5(X3,X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.59    inference(global_subsumption,[],[f63,f69])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.59  fof(f68,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.59    inference(superposition,[],[f33,f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.59  fof(f33,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.59    inference(ennf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.59  fof(f63,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f62])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.59    inference(superposition,[],[f32,f17])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f147,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f85,f86,f18])).
% 0.20/0.59  fof(f85,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f78,f35])).
% 0.20/0.59  fof(f78,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~sP5(X0,X1,k1_xboole_0)) )),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f72,f24])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~sP5(X3,X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f237,plain,(
% 0.20/0.59    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.59    inference(forward_demodulation,[],[f236,f231])).
% 0.20/0.59  fof(f231,plain,(
% 0.20/0.59    k1_xboole_0 = sK0),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f146,f230])).
% 0.20/0.59  fof(f230,plain,(
% 0.20/0.59    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f225])).
% 0.20/0.59  fof(f225,plain,(
% 0.20/0.59    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.20/0.59    inference(superposition,[],[f14,f221])).
% 0.20/0.59  fof(f221,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f217])).
% 0.20/0.59  fof(f217,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.20/0.59    inference(resolution,[],[f215,f153])).
% 0.20/0.59  fof(f153,plain,(
% 0.20/0.59    ( ! [X11] : (r2_hidden(sK2(X11,k1_xboole_0),X11) | k1_xboole_0 = X11) )),
% 0.20/0.59    inference(resolution,[],[f18,f72])).
% 0.20/0.59  fof(f215,plain,(
% 0.20/0.59    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f211])).
% 0.20/0.59  fof(f211,plain,(
% 0.20/0.59    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.20/0.59    inference(resolution,[],[f208,f153])).
% 0.20/0.59  fof(f208,plain,(
% 0.20/0.59    ( ! [X4,X3] : (~r2_hidden(X4,sK1) | ~r2_hidden(X3,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.59    inference(resolution,[],[f129,f72])).
% 0.20/0.59  fof(f129,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),k1_xboole_0) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.59    inference(resolution,[],[f37,f48])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ( ! [X0] : (~sP5(X0,sK1,sK0) | r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.59    inference(superposition,[],[f36,f15])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.59    inference(cnf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,plain,(
% 0.20/0.59    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.59    inference(negated_conjecture,[],[f7])).
% 0.20/0.59  fof(f7,conjecture,(
% 0.20/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_zfmisc_1(X0,X1)) | ~sP5(X3,X1,X0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ( ! [X4,X0,X5,X1] : (sP5(k4_tarski(X4,X5),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f23])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP5(X3,X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK1),
% 0.20/0.59    inference(cnf_transformation,[],[f9])).
% 0.20/0.59  fof(f236,plain,(
% 0.20/0.59    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f234])).
% 0.20/0.59  fof(f234,plain,(
% 0.20/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.59    inference(backward_demodulation,[],[f13,f231])).
% 0.20/0.59  fof(f13,plain,(
% 0.20/0.59    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK0),
% 0.20/0.59    inference(cnf_transformation,[],[f9])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (6024)------------------------------
% 0.20/0.59  % (6024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (6024)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (6024)Memory used [KB]: 6396
% 0.20/0.59  % (6024)Time elapsed: 0.177 s
% 0.20/0.59  % (6024)------------------------------
% 0.20/0.59  % (6024)------------------------------
% 0.20/0.59  % (5999)Success in time 0.228 s
%------------------------------------------------------------------------------
