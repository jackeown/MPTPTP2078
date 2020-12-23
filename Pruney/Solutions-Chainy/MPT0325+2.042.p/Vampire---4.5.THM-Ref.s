%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  91 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   16
%              Number of atoms          :  102 ( 257 expanded)
%              Number of equality atoms :   26 (  49 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(subsumption_resolution,[],[f224,f26])).

fof(f26,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f224,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f13,f221])).

fof(f221,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f209,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f209,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f13,f198])).

fof(f198,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f194,f172])).

fof(f172,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f166,f11])).

fof(f11,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f166,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f165,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f165,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | r1_tarski(sK1,sK3) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | r1_tarski(sK1,sK3)
      | r1_tarski(sK1,sK3) ) ),
    inference(resolution,[],[f150,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f150,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK0,X0)
      | r2_hidden(sK4(sK1,X1),sK3)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f144,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f144,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(sK0,X0),sK4(sK1,X1)),k2_zfmisc_1(sK2,sK3))
      | r1_tarski(sK0,X0)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f58,f12])).

fof(f12,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X28,X26,X29,X27,X25] :
      ( ~ r1_tarski(k2_zfmisc_1(X27,X25),X29)
      | r1_tarski(X27,X28)
      | r2_hidden(k4_tarski(sK4(X27,X28),sK4(X25,X26)),X29)
      | r1_tarski(X25,X26) ) ),
    inference(resolution,[],[f49,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK4(X2,X3)),k2_zfmisc_1(X0,X2))
      | r1_tarski(X2,X3)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f41,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

% (1380)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X0,sK4(X2,X3)),k2_zfmisc_1(X1,X2))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f24,f17])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f194,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f192,f14])).

fof(f192,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | r1_tarski(sK0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | r1_tarski(sK0,sK2)
      | r1_tarski(sK0,sK2) ) ),
    inference(resolution,[],[f151,f18])).

fof(f151,plain,(
    ! [X2,X3] :
      ( r1_tarski(sK1,X3)
      | r2_hidden(sK4(sK0,X2),sK2)
      | r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f144,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 11:47:56 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.52  % (1398)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (1390)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (1382)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (1374)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (1379)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (1390)Refutation not found, incomplete strategy% (1390)------------------------------
% 0.22/0.53  % (1390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1376)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (1390)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1390)Memory used [KB]: 10618
% 0.22/0.54  % (1390)Time elapsed: 0.116 s
% 0.22/0.54  % (1390)------------------------------
% 0.22/0.54  % (1390)------------------------------
% 0.22/0.55  % (1373)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (1378)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (1373)Refutation not found, incomplete strategy% (1373)------------------------------
% 0.22/0.55  % (1373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1373)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1373)Memory used [KB]: 1663
% 0.22/0.55  % (1373)Time elapsed: 0.093 s
% 0.22/0.55  % (1373)------------------------------
% 0.22/0.55  % (1373)------------------------------
% 0.22/0.55  % (1375)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (1375)Refutation not found, incomplete strategy% (1375)------------------------------
% 0.22/0.55  % (1375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1375)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1375)Memory used [KB]: 10618
% 0.22/0.55  % (1375)Time elapsed: 0.134 s
% 0.22/0.55  % (1375)------------------------------
% 0.22/0.55  % (1375)------------------------------
% 0.22/0.55  % (1379)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f265,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f224,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f224,plain,(
% 0.22/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.22/0.55    inference(backward_demodulation,[],[f13,f221])).
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    k1_xboole_0 = sK0),
% 0.22/0.55    inference(subsumption_resolution,[],[f209,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.22/0.55    inference(superposition,[],[f13,f198])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.55    inference(resolution,[],[f194,f172])).
% 0.22/0.55  fof(f172,plain,(
% 0.22/0.55    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0),
% 0.22/0.55    inference(resolution,[],[f166,f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0 & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.55    inference(flattening,[],[f7])).
% 0.22/0.55  fof(f7,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 0.22/0.55    inference(negated_conjecture,[],[f5])).
% 0.22/0.55  fof(f5,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 0.22/0.55    inference(resolution,[],[f165,f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(sK0,X0) | r1_tarski(sK1,sK3)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f160])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(sK0,X0) | r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3)) )),
% 0.22/0.55    inference(resolution,[],[f150,f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(sK0,X0) | r2_hidden(sK4(sK1,X1),sK3) | r1_tarski(sK1,X1)) )),
% 0.22/0.55    inference(resolution,[],[f144,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(sK0,X0),sK4(sK1,X1)),k2_zfmisc_1(sK2,sK3)) | r1_tarski(sK0,X0) | r1_tarski(sK1,X1)) )),
% 0.22/0.55    inference(resolution,[],[f58,f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X28,X26,X29,X27,X25] : (~r1_tarski(k2_zfmisc_1(X27,X25),X29) | r1_tarski(X27,X28) | r2_hidden(k4_tarski(sK4(X27,X28),sK4(X25,X26)),X29) | r1_tarski(X25,X26)) )),
% 0.22/0.55    inference(resolution,[],[f49,f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK4(X2,X3)),k2_zfmisc_1(X0,X2)) | r1_tarski(X2,X3) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f41,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  % (1380)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X0,sK4(X2,X3)),k2_zfmisc_1(X1,X2)) | r1_tarski(X2,X3)) )),
% 0.22/0.55    inference(resolution,[],[f24,f17])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 0.22/0.55    inference(resolution,[],[f192,f14])).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(sK1,X0) | r1_tarski(sK0,sK2)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f187])).
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(sK1,X0) | r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2)) )),
% 0.22/0.55    inference(resolution,[],[f151,f18])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ( ! [X2,X3] : (r1_tarski(sK1,X3) | r2_hidden(sK4(sK0,X2),sK2) | r1_tarski(sK0,X2)) )),
% 0.22/0.55    inference(resolution,[],[f144,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (1379)------------------------------
% 0.22/0.55  % (1379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1379)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (1379)Memory used [KB]: 6396
% 0.22/0.55  % (1379)Time elapsed: 0.121 s
% 0.22/0.55  % (1379)------------------------------
% 0.22/0.55  % (1379)------------------------------
% 0.22/0.55  % (1372)Success in time 0.177 s
%------------------------------------------------------------------------------
