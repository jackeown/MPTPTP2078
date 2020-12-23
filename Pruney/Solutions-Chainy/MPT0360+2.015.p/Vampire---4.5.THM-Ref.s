%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:50 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 126 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (24066)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f295,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f295,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f41,f291])).

fof(f291,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f137,f288])).

fof(f288,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f33,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

% (24068)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f137,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) ),
    inference(superposition,[],[f100,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),sK1) ),
    inference(resolution,[],[f94,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f94,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),sK1) ),
    inference(resolution,[],[f92,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f21,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | r1_xboole_0(X0,sK1) ) ),
    inference(superposition,[],[f29,f38])).

fof(f38,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f41,plain,(
    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 20:35:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (24054)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.53  % (24064)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.53  % (24064)Refutation not found, incomplete strategy% (24064)------------------------------
% 0.23/0.53  % (24064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (24061)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (24071)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.53  % (24064)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (24064)Memory used [KB]: 6140
% 0.23/0.53  % (24064)Time elapsed: 0.090 s
% 0.23/0.53  % (24064)------------------------------
% 0.23/0.53  % (24064)------------------------------
% 0.23/0.53  % (24062)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (24055)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.53  % (24060)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.54  % (24060)Refutation not found, incomplete strategy% (24060)------------------------------
% 0.23/0.54  % (24060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (24060)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (24060)Memory used [KB]: 10618
% 0.23/0.54  % (24060)Time elapsed: 0.112 s
% 0.23/0.54  % (24060)------------------------------
% 0.23/0.54  % (24060)------------------------------
% 0.23/0.54  % (24055)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % (24063)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.54  % (24080)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.55  % (24069)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.55  % (24048)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.55  % (24049)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.55  % (24048)Refutation not found, incomplete strategy% (24048)------------------------------
% 0.23/0.55  % (24048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (24048)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (24048)Memory used [KB]: 1663
% 0.23/0.55  % (24048)Time elapsed: 0.116 s
% 0.23/0.55  % (24048)------------------------------
% 0.23/0.55  % (24048)------------------------------
% 0.23/0.55  % (24052)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.55  % (24072)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.55  % (24051)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.56  % (24077)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.56  % (24065)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.56  % (24072)Refutation not found, incomplete strategy% (24072)------------------------------
% 0.23/0.56  % (24072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (24072)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (24072)Memory used [KB]: 10618
% 0.23/0.56  % (24072)Time elapsed: 0.147 s
% 0.23/0.56  % (24072)------------------------------
% 0.23/0.56  % (24072)------------------------------
% 0.23/0.56  % SZS output start Proof for theBenchmark
% 0.23/0.56  % (24066)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.56  fof(f296,plain,(
% 0.23/0.56    $false),
% 0.23/0.56    inference(subsumption_resolution,[],[f295,f20])).
% 0.23/0.56  fof(f20,plain,(
% 0.23/0.56    k1_xboole_0 != sK1),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f12,plain,(
% 0.23/0.56    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.56    inference(flattening,[],[f11])).
% 0.23/0.56  fof(f11,plain,(
% 0.23/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f10])).
% 0.23/0.56  fof(f10,negated_conjecture,(
% 0.23/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.23/0.56    inference(negated_conjecture,[],[f9])).
% 0.23/0.56  fof(f9,conjecture,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 0.23/0.56  fof(f295,plain,(
% 0.23/0.56    k1_xboole_0 = sK1),
% 0.23/0.56    inference(backward_demodulation,[],[f41,f291])).
% 0.23/0.56  fof(f291,plain,(
% 0.23/0.56    k1_xboole_0 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.23/0.56    inference(superposition,[],[f137,f288])).
% 0.23/0.56  fof(f288,plain,(
% 0.23/0.56    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.23/0.56    inference(resolution,[],[f33,f17])).
% 0.23/0.56  fof(f17,plain,(
% 0.23/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f33,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f26,f23])).
% 0.23/0.56  fof(f23,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f15])).
% 0.23/0.56  fof(f15,plain,(
% 0.23/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f8])).
% 0.23/0.56  fof(f8,axiom,(
% 0.23/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.23/0.56  % (24068)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.56  fof(f137,plain,(
% 0.23/0.56    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(X1,k3_xboole_0(X1,sK2)))) )),
% 0.23/0.56    inference(superposition,[],[f100,f22])).
% 0.23/0.56  fof(f22,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.56  fof(f100,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),sK1)) )),
% 0.23/0.56    inference(resolution,[],[f94,f28])).
% 0.23/0.56  fof(f28,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.23/0.56  fof(f94,plain,(
% 0.23/0.56    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),sK1)) )),
% 0.23/0.56    inference(resolution,[],[f92,f32])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f21,f23])).
% 0.23/0.56  fof(f21,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f7])).
% 0.23/0.56  fof(f7,axiom,(
% 0.23/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.23/0.56  fof(f92,plain,(
% 0.23/0.56    ( ! [X0] : (~r1_xboole_0(X0,sK2) | r1_xboole_0(X0,sK1)) )),
% 0.23/0.56    inference(superposition,[],[f29,f38])).
% 0.23/0.56  fof(f38,plain,(
% 0.23/0.56    sK2 = k2_xboole_0(sK1,sK2)),
% 0.23/0.56    inference(resolution,[],[f24,f18])).
% 0.23/0.56  fof(f18,plain,(
% 0.23/0.56    r1_tarski(sK1,sK2)),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f24,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f13])).
% 0.23/0.56  fof(f13,plain,(
% 0.23/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.23/0.56  fof(f29,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f16])).
% 0.23/0.56  fof(f16,plain,(
% 0.23/0.56    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.23/0.56    inference(ennf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.23/0.56  fof(f41,plain,(
% 0.23/0.56    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.23/0.56    inference(resolution,[],[f25,f19])).
% 0.23/0.56  fof(f19,plain,(
% 0.23/0.56    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f14])).
% 0.23/0.56  fof(f14,plain,(
% 0.23/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (24055)------------------------------
% 0.23/0.56  % (24055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (24055)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (24055)Memory used [KB]: 6396
% 0.23/0.56  % (24055)Time elapsed: 0.069 s
% 0.23/0.56  % (24055)------------------------------
% 0.23/0.56  % (24055)------------------------------
% 0.23/0.56  % (24066)Refutation not found, incomplete strategy% (24066)------------------------------
% 0.23/0.56  % (24066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (24066)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (24066)Memory used [KB]: 10618
% 0.23/0.56  % (24066)Time elapsed: 0.137 s
% 0.23/0.56  % (24066)------------------------------
% 0.23/0.56  % (24066)------------------------------
% 0.23/0.56  % (24042)Success in time 0.179 s
%------------------------------------------------------------------------------
