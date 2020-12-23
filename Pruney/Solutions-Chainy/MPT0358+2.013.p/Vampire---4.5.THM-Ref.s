%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:30 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 118 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   17
%              Number of atoms          :  120 ( 260 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(subsumption_resolution,[],[f126,f72])).

fof(f72,plain,(
    k1_xboole_0 != sK1 ),
    inference(resolution,[],[f71,f42])).

fof(f42,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f39])).

fof(f39,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f22,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f66,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f66,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(k1_xboole_0,X1),X2)
      | r1_tarski(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f58,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f35,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f126,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f125,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f125,plain,(
    ! [X1] : ~ r2_hidden(X1,sK1) ),
    inference(subsumption_resolution,[],[f124,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f124,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f116,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(X0,k5_xboole_0(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f111,f72])).

fof(f111,plain,(
    ! [X0] :
      ( r2_hidden(X0,k5_xboole_0(sK0,sK1))
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(backward_demodulation,[],[f47,f109])).

fof(f109,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f108,f61])).

fof(f61,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f60,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f60,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f54,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f52,f34])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f50,f33])).

fof(f108,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f41,f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f28])).

% (23921)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f21,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:50:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (23930)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (23943)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (23936)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (23946)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (23923)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (23941)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (23924)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (23929)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (23935)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (23939)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (23922)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (23938)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (23933)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (23941)Refutation not found, incomplete strategy% (23941)------------------------------
% 0.21/0.58  % (23941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (23941)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (23941)Memory used [KB]: 10746
% 0.21/0.58  % (23941)Time elapsed: 0.085 s
% 0.21/0.58  % (23941)------------------------------
% 0.21/0.58  % (23941)------------------------------
% 0.21/0.58  % (23940)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (23925)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.59  % (23928)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.59  % (23945)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.59  % (23932)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.73/0.59  % (23925)Refutation found. Thanks to Tanya!
% 1.73/0.59  % SZS status Theorem for theBenchmark
% 1.73/0.59  % SZS output start Proof for theBenchmark
% 1.73/0.59  fof(f129,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(subsumption_resolution,[],[f126,f72])).
% 1.73/0.59  fof(f72,plain,(
% 1.73/0.59    k1_xboole_0 != sK1),
% 1.73/0.59    inference(resolution,[],[f71,f42])).
% 1.73/0.59  fof(f42,plain,(
% 1.73/0.59    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | k1_xboole_0 != sK1),
% 1.73/0.59    inference(inner_rewriting,[],[f39])).
% 1.73/0.59  fof(f39,plain,(
% 1.73/0.59    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.73/0.59    inference(definition_unfolding,[],[f22,f24])).
% 1.73/0.59  fof(f24,plain,(
% 1.73/0.59    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f9])).
% 1.73/0.59  fof(f9,axiom,(
% 1.73/0.59    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.73/0.59  fof(f22,plain,(
% 1.73/0.59    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.73/0.59    inference(cnf_transformation,[],[f14])).
% 1.73/0.59  fof(f14,plain,(
% 1.73/0.59    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f13])).
% 1.73/0.59  fof(f13,negated_conjecture,(
% 1.73/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.73/0.59    inference(negated_conjecture,[],[f12])).
% 1.73/0.59  fof(f12,conjecture,(
% 1.73/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 1.73/0.59  fof(f71,plain,(
% 1.73/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f67])).
% 1.73/0.59  fof(f67,plain,(
% 1.73/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.73/0.59    inference(resolution,[],[f66,f34])).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f19])).
% 1.73/0.59  fof(f19,plain,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f3])).
% 1.73/0.59  fof(f3,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.73/0.59  fof(f66,plain,(
% 1.73/0.59    ( ! [X2,X1] : (r2_hidden(sK3(k1_xboole_0,X1),X2) | r1_tarski(k1_xboole_0,X1)) )),
% 1.73/0.59    inference(resolution,[],[f58,f33])).
% 1.73/0.59  fof(f33,plain,(
% 1.73/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f19])).
% 1.73/0.59  fof(f58,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f57])).
% 1.73/0.59  fof(f57,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0) | r2_hidden(X1,X0)) )),
% 1.73/0.59    inference(superposition,[],[f35,f25])).
% 1.73/0.59  fof(f25,plain,(
% 1.73/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f8])).
% 1.73/0.59  fof(f8,axiom,(
% 1.73/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.73/0.59  fof(f35,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f20])).
% 1.73/0.59  fof(f20,plain,(
% 1.73/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.73/0.59    inference(ennf_transformation,[],[f4])).
% 1.73/0.59  fof(f4,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.73/0.59  fof(f126,plain,(
% 1.73/0.59    k1_xboole_0 = sK1),
% 1.73/0.59    inference(resolution,[],[f125,f26])).
% 1.73/0.59  fof(f26,plain,(
% 1.73/0.59    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.73/0.59    inference(cnf_transformation,[],[f15])).
% 1.73/0.59  fof(f15,plain,(
% 1.73/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.73/0.59    inference(ennf_transformation,[],[f5])).
% 1.73/0.59  fof(f5,axiom,(
% 1.73/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.73/0.59  fof(f125,plain,(
% 1.73/0.59    ( ! [X1] : (~r2_hidden(X1,sK1)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f124,f50])).
% 1.73/0.59  fof(f50,plain,(
% 1.73/0.59    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 1.73/0.59    inference(resolution,[],[f31,f23])).
% 1.73/0.59  fof(f23,plain,(
% 1.73/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.73/0.59    inference(cnf_transformation,[],[f14])).
% 1.73/0.59  fof(f31,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f18])).
% 1.73/0.59  fof(f18,plain,(
% 1.73/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f11])).
% 1.73/0.59  fof(f11,axiom,(
% 1.73/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.73/0.59  fof(f124,plain,(
% 1.73/0.59    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f122])).
% 1.73/0.59  fof(f122,plain,(
% 1.73/0.59    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0) | ~r2_hidden(X1,sK1)) )),
% 1.73/0.59    inference(resolution,[],[f116,f36])).
% 1.73/0.59  fof(f36,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f20])).
% 1.73/0.59  fof(f116,plain,(
% 1.73/0.59    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f111,f72])).
% 1.73/0.59  fof(f111,plain,(
% 1.73/0.59    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(sK0,sK1)) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK1) )),
% 1.73/0.59    inference(backward_demodulation,[],[f47,f109])).
% 1.73/0.59  fof(f109,plain,(
% 1.73/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.73/0.59    inference(forward_demodulation,[],[f108,f61])).
% 1.73/0.59  fof(f61,plain,(
% 1.73/0.59    sK1 = k3_xboole_0(sK0,sK1)),
% 1.73/0.59    inference(superposition,[],[f60,f27])).
% 1.73/0.59  fof(f27,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f1])).
% 1.73/0.59  fof(f1,axiom,(
% 1.73/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.73/0.59  fof(f60,plain,(
% 1.73/0.59    sK1 = k3_xboole_0(sK1,sK0)),
% 1.73/0.59    inference(resolution,[],[f54,f29])).
% 1.73/0.59  fof(f29,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.73/0.59    inference(cnf_transformation,[],[f16])).
% 1.73/0.59  fof(f16,plain,(
% 1.73/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f7])).
% 1.73/0.59  fof(f7,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.73/0.59  fof(f54,plain,(
% 1.73/0.59    r1_tarski(sK1,sK0)),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f53])).
% 1.73/0.59  fof(f53,plain,(
% 1.73/0.59    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.73/0.59    inference(resolution,[],[f52,f34])).
% 1.73/0.59  fof(f52,plain,(
% 1.73/0.59    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.73/0.59    inference(resolution,[],[f50,f33])).
% 1.73/0.59  fof(f108,plain,(
% 1.73/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.73/0.59    inference(resolution,[],[f41,f23])).
% 1.73/0.59  fof(f41,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f30,f28])).
% 1.73/0.59  % (23921)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.73/0.59  fof(f28,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f6])).
% 1.73/0.59  fof(f6,axiom,(
% 1.73/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.73/0.59  fof(f30,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f17])).
% 1.73/0.59  fof(f17,plain,(
% 1.73/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f10])).
% 1.73/0.59  fof(f10,axiom,(
% 1.73/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.73/0.59  fof(f47,plain,(
% 1.73/0.59    ( ! [X0] : (r2_hidden(X0,k3_subset_1(sK0,sK1)) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK1) )),
% 1.73/0.59    inference(resolution,[],[f32,f40])).
% 1.73/0.60  fof(f40,plain,(
% 1.73/0.60    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.73/0.60    inference(definition_unfolding,[],[f21,f24])).
% 1.73/0.60  fof(f21,plain,(
% 1.73/0.60    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.73/0.60    inference(cnf_transformation,[],[f14])).
% 1.73/0.60  fof(f32,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f19])).
% 1.73/0.60  % SZS output end Proof for theBenchmark
% 1.73/0.60  % (23925)------------------------------
% 1.73/0.60  % (23925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (23925)Termination reason: Refutation
% 1.73/0.60  
% 1.73/0.60  % (23925)Memory used [KB]: 6268
% 1.73/0.60  % (23925)Time elapsed: 0.091 s
% 1.73/0.60  % (23925)------------------------------
% 1.73/0.60  % (23925)------------------------------
% 1.73/0.60  % (23929)Refutation not found, incomplete strategy% (23929)------------------------------
% 1.73/0.60  % (23929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (23929)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.60  
% 1.73/0.60  % (23929)Memory used [KB]: 10618
% 1.73/0.60  % (23929)Time elapsed: 0.185 s
% 1.73/0.60  % (23929)------------------------------
% 1.73/0.60  % (23929)------------------------------
% 1.73/0.60  % (23948)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.73/0.60  % (23918)Success in time 0.229 s
%------------------------------------------------------------------------------
