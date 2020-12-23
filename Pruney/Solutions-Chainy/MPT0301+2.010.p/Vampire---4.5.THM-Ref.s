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
% DateTime   : Thu Dec  3 12:41:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 376 expanded)
%              Number of leaves         :    7 ( 111 expanded)
%              Depth                    :   24
%              Number of atoms          :  135 ( 808 expanded)
%              Number of equality atoms :   63 ( 283 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f436])).

fof(f436,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f421,f246])).

fof(f246,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f18,f230,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f150,f150])).

fof(f150,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f92,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f34,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

% (26226)Refutation not found, incomplete strategy% (26226)------------------------------
% (26226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26226)Termination reason: Refutation not found, incomplete strategy

% (26226)Memory used [KB]: 10618
% (26226)Time elapsed: 0.133 s
% (26226)------------------------------
% (26226)------------------------------
fof(f230,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f225,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f225,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f219,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | sP8(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f219,plain,(
    ! [X0,X1] : ~ sP8(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f49,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X0)
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f18,f21])).

fof(f18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f421,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f420,f405])).

fof(f405,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f18,f398,f173])).

fof(f398,plain,(
    v1_xboole_0(sK0) ),
    inference(trivial_inequality_removal,[],[f397])).

fof(f397,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f396,f246])).

fof(f396,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | v1_xboole_0(sK0) ),
    inference(trivial_inequality_removal,[],[f391])).

fof(f391,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 != k1_xboole_0
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f15,f381])).

fof(f381,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0) ),
    inference(trivial_inequality_removal,[],[f380])).

fof(f380,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f379,f290])).

fof(f290,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f18,f272,f173])).

fof(f272,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f267,f20])).

fof(f267,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f261,f46])).

fof(f261,plain,(
    ! [X0,X1] : ~ sP8(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f49,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f379,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f369])).

fof(f369,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f16,f367])).

fof(f367,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f334,f92])).

fof(f334,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | k1_xboole_0 = sK0
      | v1_xboole_0(sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f328,f25])).

fof(f328,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f306,f20])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f48,f209])).

fof(f209,plain,(
    ! [X0] :
      ( ~ sP8(X0,sK1,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(global_subsumption,[],[f49,f208])).

fof(f208,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP8(X0,sK1,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f47,f17])).

fof(f17,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | ~ sP8(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( sP8(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f420,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f15,f405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (26225)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (26225)Refutation not found, incomplete strategy% (26225)------------------------------
% 0.20/0.50  % (26225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26241)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (26233)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (26225)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26225)Memory used [KB]: 10746
% 0.20/0.51  % (26225)Time elapsed: 0.086 s
% 0.20/0.51  % (26225)------------------------------
% 0.20/0.51  % (26225)------------------------------
% 0.20/0.52  % (26227)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (26227)Refutation not found, incomplete strategy% (26227)------------------------------
% 0.20/0.52  % (26227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26227)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26227)Memory used [KB]: 10618
% 0.20/0.52  % (26227)Time elapsed: 0.107 s
% 0.20/0.52  % (26227)------------------------------
% 0.20/0.52  % (26227)------------------------------
% 0.20/0.52  % (26217)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (26230)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (26231)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (26217)Refutation not found, incomplete strategy% (26217)------------------------------
% 0.20/0.53  % (26217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26238)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (26217)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26217)Memory used [KB]: 1663
% 0.20/0.53  % (26217)Time elapsed: 0.088 s
% 0.20/0.53  % (26217)------------------------------
% 0.20/0.53  % (26217)------------------------------
% 0.20/0.53  % (26238)Refutation not found, incomplete strategy% (26238)------------------------------
% 0.20/0.53  % (26238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26238)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26238)Memory used [KB]: 1663
% 0.20/0.53  % (26238)Time elapsed: 0.086 s
% 0.20/0.53  % (26238)------------------------------
% 0.20/0.53  % (26238)------------------------------
% 0.20/0.53  % (26229)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (26220)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (26222)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (26239)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (26218)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (26246)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (26223)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (26219)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (26241)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (26243)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (26226)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f437,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f436])).
% 0.20/0.54  fof(f436,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0),
% 0.20/0.54    inference(superposition,[],[f421,f246])).
% 0.20/0.54  fof(f246,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f18,f230,f173])).
% 0.20/0.54  fof(f173,plain,(
% 0.20/0.54    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(superposition,[],[f150,f150])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(resolution,[],[f92,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(resolution,[],[f25,f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(superposition,[],[f34,f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.54  % (26226)Refutation not found, incomplete strategy% (26226)------------------------------
% 0.20/0.54  % (26226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26226)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26226)Memory used [KB]: 10618
% 0.20/0.54  % (26226)Time elapsed: 0.133 s
% 0.20/0.54  % (26226)------------------------------
% 0.20/0.54  % (26226)------------------------------
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f225,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f225,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f219,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | sP8(X3,X1,X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~sP8(X0,X1,k1_xboole_0)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f49,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X0) | ~sP8(X3,X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f18,f21])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.54  fof(f421,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.54    inference(forward_demodulation,[],[f420,f405])).
% 0.20/0.54  fof(f405,plain,(
% 0.20/0.54    k1_xboole_0 = sK0),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f18,f398,f173])).
% 0.20/0.54  fof(f398,plain,(
% 0.20/0.54    v1_xboole_0(sK0)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f397])).
% 0.20/0.54  fof(f397,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f396,f246])).
% 0.20/0.54  fof(f396,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | v1_xboole_0(sK0)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f391])).
% 0.20/0.54  fof(f391,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK0)),
% 0.20/0.54    inference(superposition,[],[f15,f381])).
% 0.20/0.54  fof(f381,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | v1_xboole_0(sK0)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f380])).
% 0.20/0.54  fof(f380,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK0) | k1_xboole_0 = sK0),
% 0.20/0.54    inference(forward_demodulation,[],[f379,f290])).
% 0.20/0.54  fof(f290,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f18,f272,f173])).
% 0.20/0.54  fof(f272,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f267,f20])).
% 0.20/0.54  fof(f267,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f261,f46])).
% 0.20/0.54  fof(f261,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~sP8(X0,k1_xboole_0,X1)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f49,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK10(X0,X1,X3),X1) | ~sP8(X3,X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f379,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | v1_xboole_0(sK0) | k1_xboole_0 = sK0),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f369])).
% 0.20/0.54  fof(f369,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK0) | k1_xboole_0 = sK0),
% 0.20/0.54    inference(superposition,[],[f16,f367])).
% 0.20/0.54  fof(f367,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | v1_xboole_0(sK0) | k1_xboole_0 = sK0),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f365])).
% 0.20/0.54  fof(f365,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | v1_xboole_0(sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.20/0.54    inference(resolution,[],[f334,f92])).
% 0.20/0.54  fof(f334,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(sK1,X0) | k1_xboole_0 = sK0 | v1_xboole_0(sK0) | k1_xboole_0 = sK1) )),
% 0.20/0.54    inference(resolution,[],[f328,f25])).
% 0.20/0.54  fof(f328,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | v1_xboole_0(sK0)) )),
% 0.20/0.54    inference(resolution,[],[f306,f20])).
% 0.20/0.54  fof(f306,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.54    inference(resolution,[],[f48,f209])).
% 0.20/0.54  fof(f209,plain,(
% 0.20/0.54    ( ! [X0] : (~sP8(X0,sK1,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.54    inference(global_subsumption,[],[f49,f208])).
% 0.20/0.54  fof(f208,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP8(X0,sK1,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.54    inference(superposition,[],[f47,f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    inference(negated_conjecture,[],[f10])).
% 0.20/0.54  fof(f10,conjecture,(
% 0.20/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_zfmisc_1(X0,X1)) | ~sP8(X3,X1,X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~sP8(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X4,X0,X5,X1] : (sP8(k4_tarski(X4,X5),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP8(X3,X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK0),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f420,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f412])).
% 0.20/0.55  fof(f412,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.55    inference(backward_demodulation,[],[f15,f405])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (26241)------------------------------
% 0.20/0.55  % (26241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26241)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (26241)Memory used [KB]: 6396
% 0.20/0.55  % (26241)Time elapsed: 0.121 s
% 0.20/0.55  % (26241)------------------------------
% 0.20/0.55  % (26241)------------------------------
% 0.20/0.55  % (26245)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (26244)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (26235)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (26221)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (26216)Success in time 0.186 s
%------------------------------------------------------------------------------
