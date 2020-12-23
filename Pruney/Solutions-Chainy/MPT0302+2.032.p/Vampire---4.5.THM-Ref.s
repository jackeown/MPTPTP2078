%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 620 expanded)
%              Number of leaves         :    4 ( 143 expanded)
%              Depth                    :   23
%              Number of atoms          :  119 (1789 expanded)
%              Number of equality atoms :   49 (1056 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(subsumption_resolution,[],[f371,f12])).

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f371,plain,(
    sK0 = sK1 ),
    inference(forward_demodulation,[],[f370,f287])).

fof(f287,plain,(
    sK0 = k3_xboole_0(sK1,sK1) ),
    inference(subsumption_resolution,[],[f286,f94])).

fof(f94,plain,(
    ! [X17,X16] :
      ( r2_hidden(sK3(sK1,X16,X17),sK0)
      | r2_hidden(sK3(sK1,X16,X17),X17)
      | k3_xboole_0(sK1,X16) = X17 ) ),
    inference(resolution,[],[f84,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f84,plain,(
    ! [X14] :
      ( ~ r2_hidden(X14,sK1)
      | r2_hidden(X14,sK0) ) ),
    inference(subsumption_resolution,[],[f79,f10])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X14] :
      ( r2_hidden(X14,sK0)
      | ~ r2_hidden(X14,sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f59,f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f21,f9])).

fof(f9,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f286,plain,
    ( sK0 = k3_xboole_0(sK1,sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK0),sK0) ),
    inference(subsumption_resolution,[],[f285,f265])).

fof(f265,plain,(
    ! [X14] :
      ( r2_hidden(sK3(X14,sK1,sK0),sK1)
      | sK0 = k3_xboole_0(X14,sK1) ) ),
    inference(resolution,[],[f231,f53])).

fof(f53,plain,(
    r2_hidden(sK2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f48,f11])).

fof(f11,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,
    ( r2_hidden(sK2(sK0),sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f43,f13])).

fof(f43,plain,(
    ! [X14] :
      ( ~ r2_hidden(X14,sK1)
      | r2_hidden(sK2(sK0),sK1) ) ),
    inference(subsumption_resolution,[],[f38,f10])).

fof(f38,plain,(
    ! [X14] :
      ( r2_hidden(sK2(sK0),sK1)
      | ~ r2_hidden(X14,sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f29,f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f26,f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f20,f9])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f231,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,sK1)
      | r2_hidden(sK3(X8,sK1,sK0),sK1)
      | sK0 = k3_xboole_0(X8,sK1) ) ),
    inference(resolution,[],[f220,f29])).

fof(f220,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK1,sK0),sK0)
      | sK0 = k3_xboole_0(X0,sK1) ) ),
    inference(factoring,[],[f91])).

fof(f91,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK3(X10,sK1,X11),sK0)
      | r2_hidden(sK3(X10,sK1,X11),X11)
      | k3_xboole_0(X10,sK1) = X11 ) ),
    inference(resolution,[],[f84,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f285,plain,
    ( sK0 = k3_xboole_0(sK1,sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK0),sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,
    ( sK0 = k3_xboole_0(sK1,sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK0),sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK0),sK0)
    | sK0 = k3_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f265,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f370,plain,(
    sK1 = k3_xboole_0(sK1,sK1) ),
    inference(subsumption_resolution,[],[f369,f313])).

fof(f313,plain,(
    ! [X22] :
      ( r2_hidden(sK3(X22,sK1,sK1),sK1)
      | sK1 = k3_xboole_0(X22,sK1) ) ),
    inference(resolution,[],[f295,f221])).

fof(f221,plain,(
    ! [X30] :
      ( r2_hidden(sK3(X30,sK1,sK1),sK0)
      | sK1 = k3_xboole_0(X30,sK1) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X30] :
      ( r2_hidden(sK3(X30,sK1,sK1),sK0)
      | sK1 = k3_xboole_0(X30,sK1)
      | r2_hidden(sK3(X30,sK1,sK1),sK0) ) ),
    inference(resolution,[],[f91,f84])).

fof(f295,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,sK1) ) ),
    inference(superposition,[],[f25,f287])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f369,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK1),sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK1),sK1)
    | sK1 = k3_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f313,f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:28:24 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.46  % (5709)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (5701)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (5695)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (5700)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (5699)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (5695)Refutation not found, incomplete strategy% (5695)------------------------------
% 0.20/0.47  % (5695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5705)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (5695)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5695)Memory used [KB]: 6140
% 0.20/0.47  % (5695)Time elapsed: 0.064 s
% 0.20/0.47  % (5695)------------------------------
% 0.20/0.47  % (5695)------------------------------
% 0.20/0.47  % (5707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (5705)Refutation not found, incomplete strategy% (5705)------------------------------
% 0.20/0.47  % (5705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5705)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5705)Memory used [KB]: 6012
% 0.20/0.47  % (5705)Time elapsed: 0.063 s
% 0.20/0.47  % (5705)------------------------------
% 0.20/0.47  % (5705)------------------------------
% 0.20/0.47  % (5696)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (5708)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (5696)Refutation not found, incomplete strategy% (5696)------------------------------
% 0.20/0.48  % (5696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5696)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (5696)Memory used [KB]: 10618
% 0.20/0.48  % (5696)Time elapsed: 0.036 s
% 0.20/0.48  % (5696)------------------------------
% 0.20/0.48  % (5696)------------------------------
% 0.20/0.48  % (5710)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (5698)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (5698)Refutation not found, incomplete strategy% (5698)------------------------------
% 0.20/0.48  % (5698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5698)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (5698)Memory used [KB]: 10618
% 0.20/0.48  % (5698)Time elapsed: 0.074 s
% 0.20/0.48  % (5698)------------------------------
% 0.20/0.48  % (5698)------------------------------
% 0.20/0.48  % (5708)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f372,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f371,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    sK0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.20/0.48  fof(f371,plain,(
% 0.20/0.48    sK0 = sK1),
% 0.20/0.48    inference(forward_demodulation,[],[f370,f287])).
% 0.20/0.48  fof(f287,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK1,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f286,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X17,X16] : (r2_hidden(sK3(sK1,X16,X17),sK0) | r2_hidden(sK3(sK1,X16,X17),X17) | k3_xboole_0(sK1,X16) = X17) )),
% 0.20/0.48    inference(resolution,[],[f84,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X14] : (~r2_hidden(X14,sK1) | r2_hidden(X14,sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f79,f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X14] : (r2_hidden(X14,sK0) | ~r2_hidden(X14,sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.48    inference(resolution,[],[f59,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f27,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) )),
% 0.20/0.48    inference(superposition,[],[f21,f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f286,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK1,sK1) | ~r2_hidden(sK3(sK1,sK1,sK0),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f285,f265])).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    ( ! [X14] : (r2_hidden(sK3(X14,sK1,sK0),sK1) | sK0 = k3_xboole_0(X14,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f231,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f48,f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0),sK1) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(resolution,[],[f43,f13])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X14] : (~r2_hidden(X14,sK1) | r2_hidden(sK2(sK0),sK1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f38,f10])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X14] : (r2_hidden(sK2(sK0),sK1) | ~r2_hidden(X14,sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.48    inference(resolution,[],[f29,f13])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f26,f22])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 0.20/0.48    inference(superposition,[],[f20,f9])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    ( ! [X8,X9] : (~r2_hidden(X9,sK1) | r2_hidden(sK3(X8,sK1,sK0),sK1) | sK0 = k3_xboole_0(X8,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f220,f29])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK3(X0,sK1,sK0),sK0) | sK0 = k3_xboole_0(X0,sK1)) )),
% 0.20/0.48    inference(factoring,[],[f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X10,X11] : (r2_hidden(sK3(X10,sK1,X11),sK0) | r2_hidden(sK3(X10,sK1,X11),X11) | k3_xboole_0(X10,sK1) = X11) )),
% 0.20/0.48    inference(resolution,[],[f84,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK1,sK1) | ~r2_hidden(sK3(sK1,sK1,sK0),sK1) | ~r2_hidden(sK3(sK1,sK1,sK0),sK0)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f273])).
% 0.20/0.48  fof(f273,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK1,sK1) | ~r2_hidden(sK3(sK1,sK1,sK0),sK1) | ~r2_hidden(sK3(sK1,sK1,sK0),sK0) | sK0 = k3_xboole_0(sK1,sK1)),
% 0.20/0.48    inference(resolution,[],[f265,f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f370,plain,(
% 0.20/0.48    sK1 = k3_xboole_0(sK1,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f369,f313])).
% 0.20/0.48  fof(f313,plain,(
% 0.20/0.48    ( ! [X22] : (r2_hidden(sK3(X22,sK1,sK1),sK1) | sK1 = k3_xboole_0(X22,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f295,f221])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    ( ! [X30] : (r2_hidden(sK3(X30,sK1,sK1),sK0) | sK1 = k3_xboole_0(X30,sK1)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f217])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    ( ! [X30] : (r2_hidden(sK3(X30,sK1,sK1),sK0) | sK1 = k3_xboole_0(X30,sK1) | r2_hidden(sK3(X30,sK1,sK1),sK0)) )),
% 0.20/0.48    inference(resolution,[],[f91,f84])).
% 0.20/0.48  fof(f295,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,sK0) | r2_hidden(X3,sK1)) )),
% 0.20/0.48    inference(superposition,[],[f25,f287])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f369,plain,(
% 0.20/0.48    sK1 = k3_xboole_0(sK1,sK1) | ~r2_hidden(sK3(sK1,sK1,sK1),sK1)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f355])).
% 0.20/0.48  fof(f355,plain,(
% 0.20/0.48    sK1 = k3_xboole_0(sK1,sK1) | ~r2_hidden(sK3(sK1,sK1,sK1),sK1) | ~r2_hidden(sK3(sK1,sK1,sK1),sK1) | sK1 = k3_xboole_0(sK1,sK1)),
% 0.20/0.48    inference(resolution,[],[f313,f14])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (5708)------------------------------
% 0.20/0.48  % (5708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5708)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (5708)Memory used [KB]: 1791
% 0.20/0.48  % (5708)Time elapsed: 0.080 s
% 0.20/0.48  % (5708)------------------------------
% 0.20/0.48  % (5708)------------------------------
% 0.20/0.48  % (5694)Success in time 0.137 s
%------------------------------------------------------------------------------
