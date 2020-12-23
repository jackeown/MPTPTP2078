%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 237 expanded)
%              Number of leaves         :    9 (  62 expanded)
%              Depth                    :   21
%              Number of atoms          :  123 ( 482 expanded)
%              Number of equality atoms :   61 ( 217 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f196,f102])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f100,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f100,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f96,f40])).

% (29645)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
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

fof(f96,plain,(
    ! [X0,X1] : ~ sP5(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f56,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f53,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f51,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f50,f20])).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f50,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(superposition,[],[f39,f45])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f196,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f195,f190])).

fof(f190,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f118,f189])).

fof(f189,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f18,f183])).

fof(f183,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f173,f22])).

fof(f173,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f169,f22])).

fof(f169,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X25,sK0)
      | ~ r2_hidden(X24,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f42,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ sP5(X0,sK1,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(global_subsumption,[],[f56,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP5(X0,sK1,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f41,f19])).

fof(f19,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X4,X0,X5,X1] :
      ( sP5(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f116,f22])).

fof(f116,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f112,f40])).

fof(f112,plain,(
    ! [X0,X1] : ~ sP5(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f195,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f17,f190])).

fof(f17,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:43:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (29623)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (29631)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (29647)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (29623)Refutation not found, incomplete strategy% (29623)------------------------------
% 0.20/0.50  % (29623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29623)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29623)Memory used [KB]: 1663
% 0.20/0.50  % (29623)Time elapsed: 0.103 s
% 0.20/0.50  % (29623)------------------------------
% 0.20/0.50  % (29623)------------------------------
% 0.20/0.51  % (29627)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (29640)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (29632)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (29639)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (29640)Refutation not found, incomplete strategy% (29640)------------------------------
% 0.20/0.51  % (29640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29640)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29640)Memory used [KB]: 10618
% 0.20/0.51  % (29640)Time elapsed: 0.107 s
% 0.20/0.51  % (29640)------------------------------
% 0.20/0.51  % (29640)------------------------------
% 0.20/0.51  % (29632)Refutation not found, incomplete strategy% (29632)------------------------------
% 0.20/0.51  % (29632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29632)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29632)Memory used [KB]: 10618
% 0.20/0.51  % (29632)Time elapsed: 0.109 s
% 0.20/0.51  % (29632)------------------------------
% 0.20/0.51  % (29632)------------------------------
% 0.20/0.51  % (29631)Refutation not found, incomplete strategy% (29631)------------------------------
% 0.20/0.51  % (29631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29631)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29631)Memory used [KB]: 10618
% 0.20/0.51  % (29631)Time elapsed: 0.103 s
% 0.20/0.51  % (29631)------------------------------
% 0.20/0.51  % (29631)------------------------------
% 0.20/0.51  % (29625)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (29624)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (29625)Refutation not found, incomplete strategy% (29625)------------------------------
% 0.20/0.51  % (29625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29625)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.52  % (29625)Memory used [KB]: 10618
% 0.20/0.52  % (29625)Time elapsed: 0.117 s
% 0.20/0.52  % (29625)------------------------------
% 0.20/0.52  % (29625)------------------------------
% 0.20/0.52  % (29647)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (29643)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (29626)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f200])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0),
% 0.20/0.52    inference(superposition,[],[f196,f102])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f100,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f96,f40])).
% 0.20/0.52  % (29645)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | sP5(X3,X1,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP5(X0,X1,k1_xboole_0)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f56,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~sP5(X3,X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f53,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f23,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f51,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f50,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)) )),
% 0.20/0.52    inference(superposition,[],[f39,f45])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f24,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f195,f190])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    k1_xboole_0 = sK0),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f118,f189])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f187])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(superposition,[],[f18,f183])).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f180])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.20/0.52    inference(resolution,[],[f173,f22])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f170])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0) )),
% 0.20/0.52    inference(resolution,[],[f169,f22])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    ( ! [X24,X25] : (~r2_hidden(X25,sK0) | ~r2_hidden(X24,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.52    inference(resolution,[],[f42,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0] : (~sP5(X0,sK1,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.52    inference(global_subsumption,[],[f56,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP5(X0,sK1,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.52    inference(superposition,[],[f41,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_zfmisc_1(X0,X1)) | ~sP5(X3,X1,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X4,X0,X5,X1] : (sP5(k4_tarski(X4,X5),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP5(X3,X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f116,f22])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f112,f40])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP5(X0,k1_xboole_0,X1)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f56,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~sP5(X3,X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f193])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f17,f190])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (29647)------------------------------
% 0.20/0.52  % (29647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29647)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (29647)Memory used [KB]: 6268
% 0.20/0.52  % (29647)Time elapsed: 0.120 s
% 0.20/0.52  % (29647)------------------------------
% 0.20/0.52  % (29647)------------------------------
% 0.20/0.53  % (29645)Refutation not found, incomplete strategy% (29645)------------------------------
% 0.20/0.53  % (29645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29645)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (29645)Memory used [KB]: 10746
% 0.20/0.53  % (29635)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (29622)Success in time 0.171 s
%------------------------------------------------------------------------------
