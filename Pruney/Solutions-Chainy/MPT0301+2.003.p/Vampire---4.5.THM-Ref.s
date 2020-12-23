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
% DateTime   : Thu Dec  3 12:41:52 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 339 expanded)
%              Number of leaves         :    4 (  91 expanded)
%              Depth                    :   22
%              Number of atoms          :  125 ( 859 expanded)
%              Number of equality atoms :   77 ( 390 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f443])).

fof(f443,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f438,f237])).

fof(f237,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f218,f217])).

fof(f217,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f56,f91,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f91,plain,(
    ! [X2,X0,X1] : ~ sP5(X0,k2_zfmisc_1(X1,k1_xboole_0),X2) ),
    inference(unit_resulting_resolution,[],[f85,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] : ~ sP5(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f56,f31])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f16,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f16,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f218,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_xboole_0,X0) = k2_zfmisc_1(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f70,f91,f35])).

fof(f70,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f67,f43])).

fof(f67,plain,(
    ! [X0,X1] : ~ sP5(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f438,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f437,f432])).

fof(f432,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f238,f422])).

fof(f422,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f413])).

fof(f413,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f14,f410])).

fof(f410,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f400])).

fof(f400,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f390,f15])).

fof(f15,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f390,plain,
    ( sK1 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK1 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f386,f232])).

fof(f232,plain,(
    ! [X22] :
      ( r2_hidden(sK4(sK0,sK1,X22),X22)
      | k2_zfmisc_1(sK0,sK1) = X22
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f35,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ sP5(X0,sK1,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(global_subsumption,[],[f56,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP5(X0,sK1,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f44,f15])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f386,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f378])).

fof(f378,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f375,f15])).

fof(f375,plain,(
    ! [X4] :
      ( sK0 = k2_zfmisc_1(sK0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X4,sK1) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X4] :
      ( sK0 = k2_zfmisc_1(sK0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X4,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f232,f146])).

fof(f146,plain,(
    ! [X23,X22] :
      ( ~ r2_hidden(X23,sK0)
      | ~ r2_hidden(X22,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f45,f62])).

% (24013)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (24001)Termination reason: Refutation not found, incomplete strategy

% (24001)Memory used [KB]: 10746
% (24001)Time elapsed: 0.142 s
% (24001)------------------------------
% (24001)------------------------------
% (24013)Refutation not found, incomplete strategy% (24013)------------------------------
% (24013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24007)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (24013)Termination reason: Refutation not found, incomplete strategy

% (24013)Memory used [KB]: 10746
% (24013)Time elapsed: 0.143 s
% (24013)------------------------------
% (24013)------------------------------
fof(f45,plain,(
    ! [X4,X0,X5,X1] :
      ( sP5(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f238,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f219,f217])).

fof(f219,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X0,k1_xboole_0) = k2_zfmisc_1(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f85,f91,f35])).

fof(f437,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f435])).

fof(f435,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f13,f432])).

fof(f13,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (24004)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.44  % (24004)Refutation not found, incomplete strategy% (24004)------------------------------
% 0.20/0.44  % (24004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23996)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.44  % (24004)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (24004)Memory used [KB]: 10618
% 0.20/0.44  % (24004)Time elapsed: 0.057 s
% 0.20/0.44  % (24004)------------------------------
% 0.20/0.44  % (24004)------------------------------
% 0.20/0.46  % (24018)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.46  % (24018)Refutation not found, incomplete strategy% (24018)------------------------------
% 0.20/0.46  % (24018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (24018)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (24018)Memory used [KB]: 6268
% 0.20/0.46  % (24018)Time elapsed: 0.067 s
% 0.20/0.46  % (24018)------------------------------
% 0.20/0.46  % (24018)------------------------------
% 0.20/0.49  % (24003)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (24008)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (24008)Refutation not found, incomplete strategy% (24008)------------------------------
% 0.20/0.50  % (24008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24008)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24008)Memory used [KB]: 6140
% 0.20/0.50  % (24008)Time elapsed: 0.002 s
% 0.20/0.50  % (24008)------------------------------
% 0.20/0.50  % (24008)------------------------------
% 0.20/0.50  % (24003)Refutation not found, incomplete strategy% (24003)------------------------------
% 0.20/0.50  % (24003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24003)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24003)Memory used [KB]: 10618
% 0.20/0.50  % (24003)Time elapsed: 0.094 s
% 0.20/0.50  % (24003)------------------------------
% 0.20/0.50  % (24003)------------------------------
% 0.20/0.50  % (23995)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (23995)Refutation not found, incomplete strategy% (23995)------------------------------
% 0.20/0.50  % (23995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23995)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (23995)Memory used [KB]: 10618
% 0.20/0.50  % (23995)Time elapsed: 0.103 s
% 0.20/0.50  % (23995)------------------------------
% 0.20/0.50  % (23995)------------------------------
% 0.20/0.51  % (24014)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.17/0.51  % (24015)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.17/0.51  % (24020)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.17/0.51  % (24014)Refutation not found, incomplete strategy% (24014)------------------------------
% 1.17/0.51  % (24014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (24014)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.51  
% 1.17/0.51  % (24014)Memory used [KB]: 1663
% 1.17/0.51  % (24014)Time elapsed: 0.110 s
% 1.17/0.51  % (24014)------------------------------
% 1.17/0.51  % (24014)------------------------------
% 1.17/0.51  % (24015)Refutation not found, incomplete strategy% (24015)------------------------------
% 1.17/0.51  % (24015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (24015)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.51  
% 1.17/0.51  % (24015)Memory used [KB]: 10746
% 1.17/0.51  % (24015)Time elapsed: 0.067 s
% 1.17/0.51  % (24015)------------------------------
% 1.17/0.51  % (24015)------------------------------
% 1.17/0.51  % (24002)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.17/0.51  % (24002)Refutation not found, incomplete strategy% (24002)------------------------------
% 1.17/0.51  % (24002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (24002)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.51  
% 1.17/0.51  % (24002)Memory used [KB]: 10618
% 1.17/0.51  % (24002)Time elapsed: 0.096 s
% 1.17/0.51  % (24002)------------------------------
% 1.17/0.51  % (24002)------------------------------
% 1.17/0.51  % (23998)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.51  % (24000)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.17/0.51  % (23999)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.17/0.51  % (23997)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.52  % (23997)Refutation not found, incomplete strategy% (23997)------------------------------
% 1.17/0.52  % (23997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (24012)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.53  % (24022)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.53  % (24006)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.32/0.53  % (23993)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.53  % (23994)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (23997)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (23997)Memory used [KB]: 6268
% 1.32/0.53  % (23997)Time elapsed: 0.108 s
% 1.32/0.53  % (23997)------------------------------
% 1.32/0.53  % (23997)------------------------------
% 1.32/0.53  % (23993)Refutation not found, incomplete strategy% (23993)------------------------------
% 1.32/0.53  % (23993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (23993)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (23993)Memory used [KB]: 1663
% 1.32/0.53  % (23993)Time elapsed: 0.119 s
% 1.32/0.53  % (23993)------------------------------
% 1.32/0.53  % (23993)------------------------------
% 1.32/0.53  % (24019)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.53  % (24021)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.53  % (24016)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.54  % (24010)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.54  % (24009)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (24010)Refutation not found, incomplete strategy% (24010)------------------------------
% 1.32/0.54  % (24010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (24010)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (24010)Memory used [KB]: 10618
% 1.32/0.54  % (24010)Time elapsed: 0.129 s
% 1.32/0.54  % (24010)------------------------------
% 1.32/0.54  % (24010)------------------------------
% 1.32/0.54  % (24011)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.54  % (24017)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  % (24001)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.54  % (24063)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.32/0.54  % (24063)Refutation not found, incomplete strategy% (24063)------------------------------
% 1.32/0.54  % (24063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (24063)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (24063)Memory used [KB]: 6140
% 1.32/0.54  % (24063)Time elapsed: 0.054 s
% 1.32/0.54  % (24063)------------------------------
% 1.32/0.54  % (24063)------------------------------
% 1.32/0.54  % (24001)Refutation not found, incomplete strategy% (24001)------------------------------
% 1.32/0.54  % (24001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (24005)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.55  % (24017)Refutation found. Thanks to Tanya!
% 1.32/0.55  % SZS status Theorem for theBenchmark
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  fof(f444,plain,(
% 1.32/0.55    $false),
% 1.32/0.55    inference(trivial_inequality_removal,[],[f443])).
% 1.32/0.55  fof(f443,plain,(
% 1.32/0.55    k1_xboole_0 != k1_xboole_0),
% 1.32/0.55    inference(superposition,[],[f438,f237])).
% 1.32/0.55  fof(f237,plain,(
% 1.32/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.32/0.55    inference(backward_demodulation,[],[f218,f217])).
% 1.32/0.55  fof(f217,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f56,f91,f35])).
% 1.32/0.55  fof(f35,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (sP5(sK4(X0,X1,X2),X1,X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.32/0.55    inference(cnf_transformation,[],[f7])).
% 1.32/0.55  fof(f7,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.32/0.55  fof(f91,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~sP5(X0,k2_zfmisc_1(X1,k1_xboole_0),X2)) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f85,f31])).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~sP5(X3,X1,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f7])).
% 1.32/0.55  fof(f85,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f80,f43])).
% 1.32/0.55  fof(f43,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | sP5(X3,X1,X0)) )),
% 1.32/0.55    inference(equality_resolution,[],[f34])).
% 1.32/0.55  fof(f34,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.32/0.55    inference(cnf_transformation,[],[f7])).
% 1.32/0.55  fof(f80,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~sP5(X0,k1_xboole_0,X1)) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f56,f31])).
% 1.32/0.55  fof(f56,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f16,f21])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f12])).
% 1.32/0.55  fof(f12,plain,(
% 1.32/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.32/0.55    inference(ennf_transformation,[],[f8])).
% 1.32/0.55  fof(f8,axiom,(
% 1.32/0.55    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.32/0.55  fof(f16,plain,(
% 1.32/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f6])).
% 1.32/0.55  fof(f6,axiom,(
% 1.32/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.32/0.55  fof(f218,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_xboole_0,X0) = k2_zfmisc_1(X1,k2_zfmisc_1(X2,k1_xboole_0))) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f70,f91,f35])).
% 1.32/0.55  fof(f70,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f67,f43])).
% 1.32/0.55  fof(f67,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~sP5(X0,X1,k1_xboole_0)) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f56,f30])).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~sP5(X3,X1,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f7])).
% 1.32/0.55  fof(f438,plain,(
% 1.32/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.32/0.55    inference(forward_demodulation,[],[f437,f432])).
% 1.32/0.55  fof(f432,plain,(
% 1.32/0.55    k1_xboole_0 = sK0),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f238,f422])).
% 1.32/0.55  fof(f422,plain,(
% 1.32/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.32/0.55    inference(trivial_inequality_removal,[],[f413])).
% 1.32/0.55  fof(f413,plain,(
% 1.32/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.32/0.55    inference(superposition,[],[f14,f410])).
% 1.32/0.55  fof(f410,plain,(
% 1.32/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f400])).
% 1.32/0.55  fof(f400,plain,(
% 1.32/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.32/0.55    inference(superposition,[],[f390,f15])).
% 1.32/0.55  fof(f15,plain,(
% 1.32/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.32/0.55    inference(cnf_transformation,[],[f11])).
% 1.32/0.55  fof(f11,plain,(
% 1.32/0.55    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f10])).
% 1.32/0.55  fof(f10,negated_conjecture,(
% 1.32/0.55    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.55    inference(negated_conjecture,[],[f9])).
% 1.32/0.55  fof(f9,conjecture,(
% 1.32/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.32/0.55  fof(f390,plain,(
% 1.32/0.55    sK1 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f387])).
% 1.32/0.55  fof(f387,plain,(
% 1.32/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK1 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.32/0.55    inference(resolution,[],[f386,f232])).
% 1.32/0.55  fof(f232,plain,(
% 1.32/0.55    ( ! [X22] : (r2_hidden(sK4(sK0,sK1,X22),X22) | k2_zfmisc_1(sK0,sK1) = X22 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.55    inference(resolution,[],[f35,f62])).
% 1.32/0.55  fof(f62,plain,(
% 1.32/0.55    ( ! [X0] : (~sP5(X0,sK1,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.55    inference(global_subsumption,[],[f56,f61])).
% 1.32/0.55  fof(f61,plain,(
% 1.32/0.55    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP5(X0,sK1,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.55    inference(superposition,[],[f44,f15])).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_zfmisc_1(X0,X1)) | ~sP5(X3,X1,X0)) )),
% 1.32/0.55    inference(equality_resolution,[],[f33])).
% 1.32/0.55  fof(f33,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.32/0.55    inference(cnf_transformation,[],[f7])).
% 1.32/0.55  fof(f386,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f378])).
% 1.32/0.55  fof(f378,plain,(
% 1.32/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.55    inference(superposition,[],[f375,f15])).
% 1.32/0.55  fof(f375,plain,(
% 1.32/0.55    ( ! [X4] : (sK0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~r2_hidden(X4,sK1)) )),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f374])).
% 1.32/0.55  fof(f374,plain,(
% 1.32/0.55    ( ! [X4] : (sK0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~r2_hidden(X4,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.55    inference(resolution,[],[f232,f146])).
% 1.32/0.55  fof(f146,plain,(
% 1.32/0.55    ( ! [X23,X22] : (~r2_hidden(X23,sK0) | ~r2_hidden(X22,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.55    inference(resolution,[],[f45,f62])).
% 1.32/0.55  % (24013)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.55  % (24001)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (24001)Memory used [KB]: 10746
% 1.32/0.55  % (24001)Time elapsed: 0.142 s
% 1.32/0.55  % (24001)------------------------------
% 1.32/0.55  % (24001)------------------------------
% 1.32/0.55  % (24013)Refutation not found, incomplete strategy% (24013)------------------------------
% 1.32/0.55  % (24013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (24007)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.56  % (24013)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (24013)Memory used [KB]: 10746
% 1.32/0.56  % (24013)Time elapsed: 0.143 s
% 1.32/0.56  % (24013)------------------------------
% 1.32/0.56  % (24013)------------------------------
% 1.32/0.56  fof(f45,plain,(
% 1.32/0.56    ( ! [X4,X0,X5,X1] : (sP5(k4_tarski(X4,X5),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.32/0.56    inference(equality_resolution,[],[f29])).
% 1.32/0.56  fof(f29,plain,(
% 1.32/0.56    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP5(X3,X1,X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f7])).
% 1.32/0.56  fof(f14,plain,(
% 1.32/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK1),
% 1.32/0.56    inference(cnf_transformation,[],[f11])).
% 1.32/0.56  fof(f238,plain,(
% 1.32/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.32/0.56    inference(backward_demodulation,[],[f219,f217])).
% 1.32/0.56  fof(f219,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,k1_xboole_0) = k2_zfmisc_1(X1,k2_zfmisc_1(X2,k1_xboole_0))) )),
% 1.32/0.56    inference(unit_resulting_resolution,[],[f85,f91,f35])).
% 1.32/0.56  fof(f437,plain,(
% 1.32/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.32/0.56    inference(trivial_inequality_removal,[],[f435])).
% 1.32/0.56  fof(f435,plain,(
% 1.32/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.32/0.56    inference(backward_demodulation,[],[f13,f432])).
% 1.32/0.56  fof(f13,plain,(
% 1.32/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK0),
% 1.32/0.56    inference(cnf_transformation,[],[f11])).
% 1.32/0.56  % SZS output end Proof for theBenchmark
% 1.32/0.56  % (24017)------------------------------
% 1.32/0.56  % (24017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (24017)Termination reason: Refutation
% 1.32/0.56  
% 1.32/0.56  % (24017)Memory used [KB]: 6396
% 1.32/0.56  % (24017)Time elapsed: 0.135 s
% 1.32/0.56  % (24017)------------------------------
% 1.32/0.56  % (24017)------------------------------
% 1.32/0.56  % (23991)Success in time 0.198 s
%------------------------------------------------------------------------------
