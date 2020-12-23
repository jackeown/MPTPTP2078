%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:54 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 177 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :   22
%              Number of atoms          :  123 ( 354 expanded)
%              Number of equality atoms :   65 ( 143 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f557,plain,(
    $false ),
    inference(subsumption_resolution,[],[f555,f519])).

fof(f519,plain,(
    ! [X7] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X7) ),
    inference(resolution,[],[f158,f51])).

fof(f51,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f49,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f49,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f48,f18])).

fof(f48,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(resolution,[],[f37,f17])).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f158,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK7(X6,X7,sK3(k1_xboole_0,k2_zfmisc_1(X6,X7))),X6)
      | k1_xboole_0 = k2_zfmisc_1(X6,X7) ) ),
    inference(resolution,[],[f153,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK7(X0,X1,X3),X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
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

fof(f153,plain,(
    ! [X7] :
      ( r2_hidden(sK3(k1_xboole_0,X7),X7)
      | k1_xboole_0 = X7 ) ),
    inference(forward_demodulation,[],[f123,f16])).

fof(f16,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f123,plain,(
    ! [X7] :
      ( r2_hidden(sK3(k1_xboole_0,X7),X7)
      | k3_tarski(k1_xboole_0) = X7 ) ),
    inference(resolution,[],[f24,f51])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
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

fof(f555,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(trivial_inequality_removal,[],[f554])).

fof(f554,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f47,f552])).

fof(f552,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f546])).

fof(f546,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f505,f535])).

fof(f535,plain,(
    ! [X7] : k1_xboole_0 = k2_zfmisc_1(X7,k1_xboole_0) ),
    inference(resolution,[],[f159,f51])).

fof(f159,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK8(X8,X9,sK3(k1_xboole_0,k2_zfmisc_1(X8,X9))),X9)
      | k1_xboole_0 = k2_zfmisc_1(X8,X9) ) ),
    inference(resolution,[],[f153,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK8(X0,X1,X3),X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f505,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f504])).

fof(f504,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f46,f502])).

fof(f502,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f498])).

fof(f498,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f490,f153])).

fof(f490,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f489,f51])).

fof(f489,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,sK1)),k1_xboole_0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f488])).

fof(f488,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,sK1)),k1_xboole_0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f154,f15])).

fof(f15,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f11])).

% (13949)Refutation not found, incomplete strategy% (13949)------------------------------
% (13949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13949)Termination reason: Refutation not found, incomplete strategy

% (13949)Memory used [KB]: 1663
% (13949)Time elapsed: 0.139 s
% (13949)------------------------------
% (13949)------------------------------
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

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,sK3(k1_xboole_0,X0)),k2_zfmisc_1(X2,X0))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f153,f42])).

fof(f42,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f35])).

% (13948)Refutation not found, incomplete strategy% (13948)------------------------------
% (13948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:22:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (13934)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (13932)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (13943)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (13931)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (13943)Refutation not found, incomplete strategy% (13943)------------------------------
% 0.20/0.52  % (13943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13943)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13943)Memory used [KB]: 6140
% 0.20/0.52  % (13943)Time elapsed: 0.002 s
% 0.20/0.52  % (13943)------------------------------
% 0.20/0.52  % (13943)------------------------------
% 0.20/0.52  % (13940)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (13950)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (13932)Refutation not found, incomplete strategy% (13932)------------------------------
% 0.20/0.52  % (13932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13935)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (13950)Refutation not found, incomplete strategy% (13950)------------------------------
% 0.20/0.52  % (13950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13950)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13950)Memory used [KB]: 10746
% 0.20/0.52  % (13950)Time elapsed: 0.104 s
% 0.20/0.52  % (13950)------------------------------
% 0.20/0.52  % (13950)------------------------------
% 0.20/0.52  % (13942)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (13954)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (13955)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (13937)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (13957)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (13953)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (13956)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (13937)Refutation not found, incomplete strategy% (13937)------------------------------
% 0.20/0.53  % (13937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13937)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13937)Memory used [KB]: 10618
% 0.20/0.53  % (13937)Time elapsed: 0.087 s
% 0.20/0.53  % (13937)------------------------------
% 0.20/0.53  % (13937)------------------------------
% 0.20/0.53  % (13928)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (13928)Refutation not found, incomplete strategy% (13928)------------------------------
% 0.20/0.53  % (13928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13928)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13928)Memory used [KB]: 1663
% 0.20/0.53  % (13928)Time elapsed: 0.115 s
% 0.20/0.53  % (13928)------------------------------
% 0.20/0.53  % (13928)------------------------------
% 0.20/0.53  % (13939)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (13953)Refutation not found, incomplete strategy% (13953)------------------------------
% 0.20/0.53  % (13953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13953)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13953)Memory used [KB]: 6268
% 0.20/0.53  % (13953)Time elapsed: 0.097 s
% 0.20/0.53  % (13953)------------------------------
% 0.20/0.53  % (13953)------------------------------
% 0.20/0.53  % (13945)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (13939)Refutation not found, incomplete strategy% (13939)------------------------------
% 0.20/0.53  % (13939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13939)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13939)Memory used [KB]: 10618
% 0.20/0.53  % (13939)Time elapsed: 0.132 s
% 0.20/0.53  % (13939)------------------------------
% 0.20/0.53  % (13939)------------------------------
% 0.20/0.53  % (13945)Refutation not found, incomplete strategy% (13945)------------------------------
% 0.20/0.53  % (13945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13945)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13945)Memory used [KB]: 10618
% 0.20/0.53  % (13945)Time elapsed: 0.095 s
% 0.20/0.53  % (13945)------------------------------
% 0.20/0.53  % (13945)------------------------------
% 0.20/0.53  % (13941)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (13936)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (13936)Refutation not found, incomplete strategy% (13936)------------------------------
% 0.20/0.54  % (13936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13936)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13936)Memory used [KB]: 10746
% 0.20/0.54  % (13936)Time elapsed: 0.132 s
% 0.20/0.54  % (13936)------------------------------
% 0.20/0.54  % (13936)------------------------------
% 1.30/0.54  % (13932)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (13932)Memory used [KB]: 6268
% 1.30/0.54  % (13932)Time elapsed: 0.109 s
% 1.30/0.54  % (13932)------------------------------
% 1.30/0.54  % (13932)------------------------------
% 1.30/0.54  % (13951)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.54  % (13938)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.54  % (13933)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.54  % (13929)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.54  % (13938)Refutation not found, incomplete strategy% (13938)------------------------------
% 1.30/0.54  % (13938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (13938)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (13938)Memory used [KB]: 10618
% 1.30/0.54  % (13938)Time elapsed: 0.132 s
% 1.30/0.54  % (13938)------------------------------
% 1.30/0.54  % (13938)------------------------------
% 1.30/0.54  % (13934)Refutation found. Thanks to Tanya!
% 1.30/0.54  % SZS status Theorem for theBenchmark
% 1.30/0.54  % (13944)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.54  % (13930)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (13930)Refutation not found, incomplete strategy% (13930)------------------------------
% 1.30/0.54  % (13930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (13930)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (13930)Memory used [KB]: 10618
% 1.30/0.54  % (13930)Time elapsed: 0.138 s
% 1.30/0.54  % (13930)------------------------------
% 1.30/0.54  % (13930)------------------------------
% 1.30/0.54  % (13948)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.54  % (13949)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f557,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(subsumption_resolution,[],[f555,f519])).
% 1.30/0.54  fof(f519,plain,(
% 1.30/0.54    ( ! [X7] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X7)) )),
% 1.30/0.54    inference(resolution,[],[f158,f51])).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(superposition,[],[f49,f18])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 1.30/0.54    inference(forward_demodulation,[],[f48,f18])).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 1.30/0.54    inference(resolution,[],[f37,f17])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f20,f19])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,plain,(
% 1.30/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(ennf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,plain,(
% 1.30/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(rectify,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.30/0.54  fof(f158,plain,(
% 1.30/0.54    ( ! [X6,X7] : (r2_hidden(sK7(X6,X7,sK3(k1_xboole_0,k2_zfmisc_1(X6,X7))),X6) | k1_xboole_0 = k2_zfmisc_1(X6,X7)) )),
% 1.30/0.54    inference(resolution,[],[f153,f45])).
% 1.30/0.55  fof(f45,plain,(
% 1.30/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | r2_hidden(sK7(X0,X1,X3),X0)) )),
% 1.30/0.55    inference(equality_resolution,[],[f32])).
% 1.30/0.55  fof(f32,plain,(
% 1.30/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.30/0.55    inference(cnf_transformation,[],[f5])).
% 1.30/0.55  fof(f5,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.30/0.55  fof(f153,plain,(
% 1.30/0.55    ( ! [X7] : (r2_hidden(sK3(k1_xboole_0,X7),X7) | k1_xboole_0 = X7) )),
% 1.30/0.55    inference(forward_demodulation,[],[f123,f16])).
% 1.30/0.55  fof(f16,plain,(
% 1.30/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.30/0.55    inference(cnf_transformation,[],[f7])).
% 1.30/0.55  fof(f7,axiom,(
% 1.30/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.30/0.55  fof(f123,plain,(
% 1.30/0.55    ( ! [X7] : (r2_hidden(sK3(k1_xboole_0,X7),X7) | k3_tarski(k1_xboole_0) = X7) )),
% 1.30/0.55    inference(resolution,[],[f24,f51])).
% 1.30/0.55  fof(f24,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 1.30/0.55    inference(cnf_transformation,[],[f6])).
% 1.30/0.55  fof(f6,axiom,(
% 1.30/0.55    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.30/0.55  fof(f555,plain,(
% 1.30/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.30/0.55    inference(trivial_inequality_removal,[],[f554])).
% 1.30/0.55  fof(f554,plain,(
% 1.30/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.30/0.55    inference(backward_demodulation,[],[f47,f552])).
% 1.30/0.55  fof(f552,plain,(
% 1.30/0.55    k1_xboole_0 = sK0),
% 1.30/0.55    inference(trivial_inequality_removal,[],[f546])).
% 1.30/0.55  fof(f546,plain,(
% 1.30/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.30/0.55    inference(superposition,[],[f505,f535])).
% 1.30/0.55  fof(f535,plain,(
% 1.30/0.55    ( ! [X7] : (k1_xboole_0 = k2_zfmisc_1(X7,k1_xboole_0)) )),
% 1.30/0.55    inference(resolution,[],[f159,f51])).
% 1.30/0.55  fof(f159,plain,(
% 1.30/0.55    ( ! [X8,X9] : (r2_hidden(sK8(X8,X9,sK3(k1_xboole_0,k2_zfmisc_1(X8,X9))),X9) | k1_xboole_0 = k2_zfmisc_1(X8,X9)) )),
% 1.30/0.55    inference(resolution,[],[f153,f44])).
% 1.30/0.55  fof(f44,plain,(
% 1.30/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | r2_hidden(sK8(X0,X1,X3),X1)) )),
% 1.30/0.55    inference(equality_resolution,[],[f33])).
% 1.30/0.55  fof(f33,plain,(
% 1.30/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.30/0.55    inference(cnf_transformation,[],[f5])).
% 1.30/0.55  fof(f505,plain,(
% 1.30/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.30/0.55    inference(trivial_inequality_removal,[],[f504])).
% 1.30/0.55  fof(f504,plain,(
% 1.30/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.30/0.55    inference(superposition,[],[f46,f502])).
% 1.30/0.55  fof(f502,plain,(
% 1.30/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.30/0.55    inference(duplicate_literal_removal,[],[f498])).
% 1.30/0.55  fof(f498,plain,(
% 1.30/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.30/0.55    inference(resolution,[],[f490,f153])).
% 1.30/0.55  fof(f490,plain,(
% 1.30/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.30/0.55    inference(subsumption_resolution,[],[f489,f51])).
% 1.30/0.55  fof(f489,plain,(
% 1.30/0.55    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,sK1)),k1_xboole_0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.30/0.55    inference(duplicate_literal_removal,[],[f488])).
% 1.30/0.55  fof(f488,plain,(
% 1.30/0.55    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,sK1)),k1_xboole_0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.30/0.55    inference(superposition,[],[f154,f15])).
% 1.30/0.55  fof(f15,plain,(
% 1.30/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.30/0.55    inference(cnf_transformation,[],[f11])).
% 1.30/0.55  % (13949)Refutation not found, incomplete strategy% (13949)------------------------------
% 1.30/0.55  % (13949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (13949)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (13949)Memory used [KB]: 1663
% 1.30/0.55  % (13949)Time elapsed: 0.139 s
% 1.30/0.55  % (13949)------------------------------
% 1.30/0.55  % (13949)------------------------------
% 1.30/0.55  fof(f11,plain,(
% 1.30/0.55    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.30/0.55    inference(ennf_transformation,[],[f9])).
% 1.30/0.55  fof(f9,negated_conjecture,(
% 1.30/0.55    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.30/0.55    inference(negated_conjecture,[],[f8])).
% 1.30/0.55  fof(f8,conjecture,(
% 1.30/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.30/0.55  fof(f154,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,sK3(k1_xboole_0,X0)),k2_zfmisc_1(X2,X0)) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0) )),
% 1.30/0.55    inference(resolution,[],[f153,f42])).
% 1.30/0.55  fof(f42,plain,(
% 1.30/0.55    ( ! [X4,X0,X5,X1] : (~r2_hidden(X5,X1) | ~r2_hidden(X4,X0) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 1.30/0.55    inference(equality_resolution,[],[f41])).
% 1.30/0.55  fof(f41,plain,(
% 1.30/0.55    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.30/0.55    inference(equality_resolution,[],[f35])).
% 1.30/0.55  % (13948)Refutation not found, incomplete strategy% (13948)------------------------------
% 1.30/0.55  % (13948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  fof(f35,plain,(
% 1.30/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.30/0.55    inference(cnf_transformation,[],[f5])).
% 1.30/0.55  fof(f46,plain,(
% 1.30/0.55    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.30/0.55    inference(inner_rewriting,[],[f14])).
% 1.30/0.55  fof(f14,plain,(
% 1.30/0.55    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.30/0.55    inference(cnf_transformation,[],[f11])).
% 1.30/0.55  fof(f47,plain,(
% 1.30/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.30/0.55    inference(inner_rewriting,[],[f13])).
% 1.30/0.55  fof(f13,plain,(
% 1.30/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.30/0.55    inference(cnf_transformation,[],[f11])).
% 1.30/0.55  % SZS output end Proof for theBenchmark
% 1.30/0.55  % (13934)------------------------------
% 1.30/0.55  % (13934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (13934)Termination reason: Refutation
% 1.30/0.55  
% 1.30/0.55  % (13934)Memory used [KB]: 6652
% 1.30/0.55  % (13934)Time elapsed: 0.118 s
% 1.30/0.55  % (13934)------------------------------
% 1.30/0.55  % (13934)------------------------------
% 1.30/0.55  % (13927)Success in time 0.176 s
% 1.30/0.55  % (13948)Termination reason: Refutation not found, incomplete strategy
%------------------------------------------------------------------------------
