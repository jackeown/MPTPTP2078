%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:55 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 483 expanded)
%              Number of leaves         :    8 ( 141 expanded)
%              Depth                    :   21
%              Number of atoms          :  130 ( 999 expanded)
%              Number of equality atoms :   63 ( 326 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f206,f134])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f128,f127])).

fof(f127,plain,(
    ! [X0] : k1_xboole_0 = k3_tarski(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f78,f107,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sP4(sK3(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f107,plain,(
    ! [X0,X1] : ~ sP4(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f97,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK5(X0,X2),X0)
      | ~ sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f83,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f83,plain,(
    ! [X0,X1] : ~ sP7(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f72,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f72,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(unit_resulting_resolution,[],[f44,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f44,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f18,f17])).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f128,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,X0) = k3_tarski(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f92,f107,f27])).

fof(f92,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f82,f41])).

fof(f82,plain,(
    ! [X0,X1] : ~ sP7(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f78,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f206,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f205,f200])).

fof(f200,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f135,f199])).

fof(f199,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f14,f190])).

fof(f190,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f185,f157])).

fof(f157,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f130,f16])).

fof(f16,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f130,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_xboole_0,X0),X0)
      | k3_tarski(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f27,f81])).

fof(f81,plain,(
    ! [X0] : ~ sP4(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f78,f24])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f178,f157])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f114,f78])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),k1_xboole_0)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f43,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ sP7(X0,sK1,sK0)
      | r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f42,f15])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

% (5266)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | ~ sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X4,X0,X5,X1] :
      ( sP7(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f129,f127])).

fof(f129,plain,(
    ! [X0,X1] : k2_zfmisc_1(X0,k1_xboole_0) = k3_tarski(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f97,f107,f27])).

fof(f205,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f13,f200])).

fof(f13,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (5247)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (5248)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (5255)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5247)Refutation not found, incomplete strategy% (5247)------------------------------
% 0.21/0.51  % (5247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5247)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5247)Memory used [KB]: 6268
% 0.21/0.51  % (5247)Time elapsed: 0.110 s
% 0.21/0.51  % (5247)------------------------------
% 0.21/0.51  % (5247)------------------------------
% 0.21/0.51  % (5265)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (5258)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (5264)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (5264)Refutation not found, incomplete strategy% (5264)------------------------------
% 0.21/0.51  % (5264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5264)Memory used [KB]: 10746
% 0.21/0.51  % (5264)Time elapsed: 0.116 s
% 0.21/0.51  % (5264)------------------------------
% 0.21/0.51  % (5264)------------------------------
% 0.21/0.52  % (5256)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.53  % (5254)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.53  % (5254)Refutation not found, incomplete strategy% (5254)------------------------------
% 1.29/0.53  % (5254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (5254)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (5254)Memory used [KB]: 10618
% 1.29/0.53  % (5254)Time elapsed: 0.122 s
% 1.29/0.53  % (5254)------------------------------
% 1.29/0.53  % (5254)------------------------------
% 1.29/0.53  % (5251)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.53  % (5244)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (5243)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (5243)Refutation not found, incomplete strategy% (5243)------------------------------
% 1.29/0.53  % (5243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (5243)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (5243)Memory used [KB]: 1663
% 1.29/0.53  % (5243)Time elapsed: 0.123 s
% 1.29/0.53  % (5243)------------------------------
% 1.29/0.53  % (5243)------------------------------
% 1.29/0.53  % (5265)Refutation not found, incomplete strategy% (5265)------------------------------
% 1.29/0.53  % (5265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (5250)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.53  % (5265)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (5265)Memory used [KB]: 1663
% 1.29/0.53  % (5265)Time elapsed: 0.128 s
% 1.29/0.53  % (5265)------------------------------
% 1.29/0.53  % (5265)------------------------------
% 1.29/0.53  % (5259)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.53  % (5267)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.53  % (5258)Refutation not found, incomplete strategy% (5258)------------------------------
% 1.29/0.53  % (5258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (5258)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (5258)Memory used [KB]: 6140
% 1.29/0.53  % (5258)Time elapsed: 0.002 s
% 1.29/0.53  % (5258)------------------------------
% 1.29/0.53  % (5258)------------------------------
% 1.29/0.54  % (5271)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (5249)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.54  % (5245)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (5273)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.54  % (5252)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (5263)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.54  % (5245)Refutation not found, incomplete strategy% (5245)------------------------------
% 1.29/0.54  % (5245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (5246)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.54  % (5270)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.54  % (5245)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (5245)Memory used [KB]: 10618
% 1.45/0.54  % (5245)Time elapsed: 0.135 s
% 1.45/0.54  % (5245)------------------------------
% 1.45/0.54  % (5245)------------------------------
% 1.45/0.54  % (5269)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.54  % (5251)Refutation not found, incomplete strategy% (5251)------------------------------
% 1.45/0.54  % (5251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (5251)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (5251)Memory used [KB]: 10746
% 1.45/0.54  % (5251)Time elapsed: 0.137 s
% 1.45/0.54  % (5251)------------------------------
% 1.45/0.54  % (5251)------------------------------
% 1.45/0.54  % (5269)Refutation not found, incomplete strategy% (5269)------------------------------
% 1.45/0.54  % (5269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (5269)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (5269)Memory used [KB]: 6268
% 1.45/0.54  % (5269)Time elapsed: 0.137 s
% 1.45/0.54  % (5269)------------------------------
% 1.45/0.54  % (5269)------------------------------
% 1.45/0.54  % (5262)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (5272)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.55  % (5253)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (5268)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.55  % (5261)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (5253)Refutation not found, incomplete strategy% (5253)------------------------------
% 1.45/0.55  % (5253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (5253)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (5253)Memory used [KB]: 10618
% 1.45/0.55  % (5253)Time elapsed: 0.147 s
% 1.45/0.55  % (5253)------------------------------
% 1.45/0.55  % (5253)------------------------------
% 1.45/0.55  % (5268)Refutation found. Thanks to Tanya!
% 1.45/0.55  % SZS status Theorem for theBenchmark
% 1.45/0.55  % SZS output start Proof for theBenchmark
% 1.45/0.55  fof(f210,plain,(
% 1.45/0.55    $false),
% 1.45/0.55    inference(trivial_inequality_removal,[],[f209])).
% 1.45/0.55  fof(f209,plain,(
% 1.45/0.55    k1_xboole_0 != k1_xboole_0),
% 1.45/0.55    inference(superposition,[],[f206,f134])).
% 1.45/0.55  fof(f134,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(backward_demodulation,[],[f128,f127])).
% 1.45/0.55  fof(f127,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 = k3_tarski(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f78,f107,f27])).
% 1.45/0.55  fof(f27,plain,(
% 1.45/0.55    ( ! [X0,X1] : (sP4(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f6])).
% 1.45/0.55  fof(f6,axiom,(
% 1.45/0.55    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.45/0.55  fof(f107,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~sP4(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f97,f24])).
% 1.45/0.55  fof(f24,plain,(
% 1.45/0.55    ( ! [X2,X0] : (r2_hidden(sK5(X0,X2),X0) | ~sP4(X2,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f6])).
% 1.45/0.55  fof(f97,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f83,f41])).
% 1.45/0.55  fof(f41,plain,(
% 1.45/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | sP7(X3,X1,X0)) )),
% 1.45/0.55    inference(equality_resolution,[],[f34])).
% 1.45/0.55  fof(f34,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.45/0.55    inference(cnf_transformation,[],[f5])).
% 1.45/0.55  fof(f5,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.45/0.55  fof(f83,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~sP7(X0,k1_xboole_0,X1)) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f78,f31])).
% 1.45/0.55  fof(f31,plain,(
% 1.45/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~sP7(X3,X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f5])).
% 1.45/0.55  fof(f78,plain,(
% 1.45/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.45/0.55    inference(forward_demodulation,[],[f72,f17])).
% 1.45/0.55  fof(f17,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f3])).
% 1.45/0.55  fof(f3,axiom,(
% 1.45/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.45/0.55  fof(f72,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f44,f38])).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f20,f19])).
% 1.45/0.55  fof(f19,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f2])).
% 1.45/0.55  fof(f2,axiom,(
% 1.45/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.45/0.55  fof(f20,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f12])).
% 1.45/0.55  fof(f12,plain,(
% 1.45/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.45/0.55    inference(ennf_transformation,[],[f10])).
% 1.45/0.55  fof(f10,plain,(
% 1.45/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.55    inference(rectify,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.45/0.55  fof(f44,plain,(
% 1.45/0.55    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.55    inference(superposition,[],[f18,f17])).
% 1.45/0.55  fof(f18,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f4])).
% 1.45/0.55  fof(f4,axiom,(
% 1.45/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.45/0.55  fof(f128,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X0) = k3_tarski(k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f92,f107,f27])).
% 1.45/0.55  fof(f92,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f82,f41])).
% 1.45/0.55  fof(f82,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~sP7(X0,X1,k1_xboole_0)) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f78,f30])).
% 1.45/0.55  fof(f30,plain,(
% 1.45/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~sP7(X3,X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f5])).
% 1.45/0.55  fof(f206,plain,(
% 1.45/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.45/0.55    inference(forward_demodulation,[],[f205,f200])).
% 1.45/0.55  fof(f200,plain,(
% 1.45/0.55    k1_xboole_0 = sK0),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f135,f199])).
% 1.45/0.55  fof(f199,plain,(
% 1.45/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.45/0.55    inference(trivial_inequality_removal,[],[f194])).
% 1.45/0.55  fof(f194,plain,(
% 1.45/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.45/0.55    inference(superposition,[],[f14,f190])).
% 1.45/0.55  fof(f190,plain,(
% 1.45/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.45/0.55    inference(duplicate_literal_removal,[],[f186])).
% 1.45/0.55  fof(f186,plain,(
% 1.45/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.45/0.55    inference(resolution,[],[f185,f157])).
% 1.45/0.55  fof(f157,plain,(
% 1.45/0.55    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 1.45/0.55    inference(forward_demodulation,[],[f130,f16])).
% 1.45/0.55  fof(f16,plain,(
% 1.45/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.45/0.55    inference(cnf_transformation,[],[f7])).
% 1.45/0.55  fof(f7,axiom,(
% 1.45/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.45/0.55  fof(f130,plain,(
% 1.45/0.55    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0,X0),X0) | k3_tarski(k1_xboole_0) = X0) )),
% 1.45/0.55    inference(resolution,[],[f27,f81])).
% 1.45/0.55  fof(f81,plain,(
% 1.45/0.55    ( ! [X0] : (~sP4(X0,k1_xboole_0)) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f78,f24])).
% 1.45/0.55  fof(f185,plain,(
% 1.45/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.45/0.55    inference(duplicate_literal_removal,[],[f181])).
% 1.45/0.55  fof(f181,plain,(
% 1.45/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 1.45/0.55    inference(resolution,[],[f178,f157])).
% 1.45/0.55  fof(f178,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.45/0.55    inference(resolution,[],[f114,f78])).
% 1.45/0.55  fof(f114,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),k1_xboole_0) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.45/0.55    inference(resolution,[],[f43,f60])).
% 1.45/0.55  fof(f60,plain,(
% 1.45/0.55    ( ! [X0] : (~sP7(X0,sK1,sK0) | r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.45/0.55    inference(superposition,[],[f42,f15])).
% 1.45/0.55  fof(f15,plain,(
% 1.45/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.45/0.55    inference(cnf_transformation,[],[f11])).
% 1.45/0.55  fof(f11,plain,(
% 1.45/0.55    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f9])).
% 1.45/0.55  fof(f9,negated_conjecture,(
% 1.45/0.55    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.45/0.55    inference(negated_conjecture,[],[f8])).
% 1.45/0.55  % (5266)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.55  fof(f8,conjecture,(
% 1.45/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.45/0.55  fof(f42,plain,(
% 1.45/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_zfmisc_1(X0,X1)) | ~sP7(X3,X1,X0)) )),
% 1.45/0.55    inference(equality_resolution,[],[f33])).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.45/0.55    inference(cnf_transformation,[],[f5])).
% 1.45/0.55  fof(f43,plain,(
% 1.45/0.55    ( ! [X4,X0,X5,X1] : (sP7(k4_tarski(X4,X5),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.45/0.55    inference(equality_resolution,[],[f29])).
% 1.45/0.55  fof(f29,plain,(
% 1.45/0.55    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP7(X3,X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f5])).
% 1.45/0.55  fof(f14,plain,(
% 1.45/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK1),
% 1.45/0.55    inference(cnf_transformation,[],[f11])).
% 1.45/0.55  fof(f135,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.45/0.55    inference(backward_demodulation,[],[f129,f127])).
% 1.45/0.55  fof(f129,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,k1_xboole_0) = k3_tarski(k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f97,f107,f27])).
% 1.45/0.55  fof(f205,plain,(
% 1.45/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.45/0.55    inference(trivial_inequality_removal,[],[f203])).
% 1.45/0.55  fof(f203,plain,(
% 1.45/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.45/0.55    inference(backward_demodulation,[],[f13,f200])).
% 1.45/0.55  fof(f13,plain,(
% 1.45/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK0),
% 1.45/0.55    inference(cnf_transformation,[],[f11])).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (5268)------------------------------
% 1.45/0.55  % (5268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (5268)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (5268)Memory used [KB]: 6268
% 1.45/0.55  % (5268)Time elapsed: 0.150 s
% 1.45/0.55  % (5268)------------------------------
% 1.45/0.55  % (5268)------------------------------
% 1.45/0.55  % (5240)Success in time 0.191 s
%------------------------------------------------------------------------------
