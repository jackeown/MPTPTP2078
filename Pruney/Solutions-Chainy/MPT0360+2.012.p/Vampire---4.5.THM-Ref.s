%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:49 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 121 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  111 ( 284 expanded)
%              Number of equality atoms :   34 (  83 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f170,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f170,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f169,f111])).

fof(f111,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f108,f62])).

fof(f62,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f108,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f49,f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f41,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f169,plain,(
    sK1 = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f167,f62])).

fof(f167,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f163,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f36,f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f163,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f151,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k5_xboole_0(sK0,sK2))
      | r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f73,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f73,plain,(
    r1_xboole_0(k5_xboole_0(sK0,sK2),sK2) ),
    inference(superposition,[],[f52,f64])).

fof(f64,plain,(
    sK2 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f33,f61])).

fof(f61,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f60,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f25])).

fof(f25,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f57,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f52,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f44,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f151,plain,(
    r1_tarski(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f23,f150])).

fof(f150,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f148,f71])).

fof(f71,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f64,f27])).

fof(f148,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f45,f21])).

% (31222)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f23,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (31211)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31206)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (31210)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (31207)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (31209)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.52  % (31228)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.52  % (31221)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.52  % (31220)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.52  % (31208)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.52  % (31211)Refutation found. Thanks to Tanya!
% 1.27/0.52  % SZS status Theorem for theBenchmark
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f171,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(subsumption_resolution,[],[f170,f24])).
% 1.27/0.52  fof(f24,plain,(
% 1.27/0.52    k1_xboole_0 != sK1),
% 1.27/0.52    inference(cnf_transformation,[],[f15])).
% 1.27/0.52  fof(f15,plain,(
% 1.27/0.52    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.27/0.52    inference(flattening,[],[f14])).
% 1.27/0.52  fof(f14,plain,(
% 1.27/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.27/0.52    inference(ennf_transformation,[],[f13])).
% 1.27/0.52  fof(f13,negated_conjecture,(
% 1.27/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.27/0.52    inference(negated_conjecture,[],[f12])).
% 1.27/0.52  fof(f12,conjecture,(
% 1.27/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.27/0.52  fof(f170,plain,(
% 1.27/0.52    k1_xboole_0 = sK1),
% 1.27/0.52    inference(forward_demodulation,[],[f169,f111])).
% 1.27/0.52  fof(f111,plain,(
% 1.27/0.52    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.27/0.52    inference(forward_demodulation,[],[f108,f62])).
% 1.27/0.52  fof(f62,plain,(
% 1.27/0.52    sK1 = k3_xboole_0(sK1,sK2)),
% 1.27/0.52    inference(resolution,[],[f33,f22])).
% 1.27/0.52  fof(f22,plain,(
% 1.27/0.52    r1_tarski(sK1,sK2)),
% 1.27/0.52    inference(cnf_transformation,[],[f15])).
% 1.27/0.52  fof(f33,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f17])).
% 1.27/0.52  fof(f17,plain,(
% 1.27/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f4])).
% 1.27/0.52  fof(f4,axiom,(
% 1.27/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.27/0.52  fof(f108,plain,(
% 1.27/0.52    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.27/0.52    inference(resolution,[],[f49,f22])).
% 1.27/0.52  fof(f49,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.27/0.52    inference(definition_unfolding,[],[f41,f28])).
% 1.27/0.52  fof(f28,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f3])).
% 1.27/0.53  fof(f3,axiom,(
% 1.27/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.27/0.53  fof(f41,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.27/0.53    inference(cnf_transformation,[],[f2])).
% 1.27/0.53  fof(f2,axiom,(
% 1.27/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.27/0.53  fof(f169,plain,(
% 1.27/0.53    sK1 = k5_xboole_0(sK1,sK1)),
% 1.27/0.53    inference(forward_demodulation,[],[f167,f62])).
% 1.27/0.53  fof(f167,plain,(
% 1.27/0.53    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.27/0.53    inference(resolution,[],[f163,f46])).
% 1.27/0.53  fof(f46,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.27/0.53    inference(definition_unfolding,[],[f36,f28])).
% 1.27/0.53  fof(f36,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f7])).
% 1.27/0.53  fof(f7,axiom,(
% 1.27/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.27/0.53  fof(f163,plain,(
% 1.27/0.53    r1_xboole_0(sK1,sK2)),
% 1.27/0.53    inference(resolution,[],[f151,f79])).
% 1.27/0.53  fof(f79,plain,(
% 1.27/0.53    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK0,sK2)) | r1_xboole_0(X0,sK2)) )),
% 1.27/0.53    inference(resolution,[],[f73,f43])).
% 1.27/0.53  fof(f43,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f20])).
% 1.27/0.53  fof(f20,plain,(
% 1.27/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.27/0.53    inference(flattening,[],[f19])).
% 1.27/0.53  fof(f19,plain,(
% 1.27/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.27/0.53    inference(ennf_transformation,[],[f5])).
% 1.27/0.53  fof(f5,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.27/0.53  fof(f73,plain,(
% 1.27/0.53    r1_xboole_0(k5_xboole_0(sK0,sK2),sK2)),
% 1.27/0.53    inference(superposition,[],[f52,f64])).
% 1.27/0.53  fof(f64,plain,(
% 1.27/0.53    sK2 = k3_xboole_0(sK2,sK0)),
% 1.27/0.53    inference(resolution,[],[f33,f61])).
% 1.27/0.53  fof(f61,plain,(
% 1.27/0.53    r1_tarski(sK2,sK0)),
% 1.27/0.53    inference(resolution,[],[f60,f50])).
% 1.27/0.53  fof(f50,plain,(
% 1.27/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.27/0.53    inference(equality_resolution,[],[f38])).
% 1.27/0.53  fof(f38,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.27/0.53    inference(cnf_transformation,[],[f8])).
% 1.27/0.53  fof(f8,axiom,(
% 1.27/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.27/0.53  fof(f60,plain,(
% 1.27/0.53    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.27/0.53    inference(subsumption_resolution,[],[f57,f25])).
% 1.27/0.53  fof(f25,plain,(
% 1.27/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f11])).
% 1.27/0.53  fof(f11,axiom,(
% 1.27/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.27/0.53  fof(f57,plain,(
% 1.27/0.53    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.27/0.53    inference(resolution,[],[f32,f21])).
% 1.27/0.53  fof(f21,plain,(
% 1.27/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.27/0.53    inference(cnf_transformation,[],[f15])).
% 1.27/0.53  fof(f32,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f16])).
% 1.27/0.53  fof(f16,plain,(
% 1.27/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.27/0.53    inference(ennf_transformation,[],[f9])).
% 1.27/0.53  fof(f9,axiom,(
% 1.27/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.27/0.53  fof(f52,plain,(
% 1.27/0.53    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1)) )),
% 1.27/0.53    inference(superposition,[],[f44,f27])).
% 1.27/0.53  fof(f27,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f1])).
% 1.27/0.53  fof(f1,axiom,(
% 1.27/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.27/0.53  fof(f44,plain,(
% 1.27/0.53    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.27/0.53    inference(definition_unfolding,[],[f26,f28])).
% 1.27/0.53  fof(f26,plain,(
% 1.27/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f6])).
% 1.27/0.53  fof(f6,axiom,(
% 1.27/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.27/0.53  fof(f151,plain,(
% 1.27/0.53    r1_tarski(sK1,k5_xboole_0(sK0,sK2))),
% 1.27/0.53    inference(backward_demodulation,[],[f23,f150])).
% 1.27/0.53  fof(f150,plain,(
% 1.27/0.53    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.27/0.53    inference(forward_demodulation,[],[f148,f71])).
% 1.27/0.53  fof(f71,plain,(
% 1.27/0.53    sK2 = k3_xboole_0(sK0,sK2)),
% 1.27/0.53    inference(superposition,[],[f64,f27])).
% 1.27/0.53  fof(f148,plain,(
% 1.27/0.53    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.27/0.53    inference(resolution,[],[f45,f21])).
% 1.27/0.53  % (31222)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.53  fof(f45,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.27/0.53    inference(definition_unfolding,[],[f34,f28])).
% 1.27/0.53  fof(f34,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f18])).
% 1.27/0.53  fof(f18,plain,(
% 1.27/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.27/0.53    inference(ennf_transformation,[],[f10])).
% 1.27/0.53  fof(f10,axiom,(
% 1.27/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.27/0.53  fof(f23,plain,(
% 1.27/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.27/0.53    inference(cnf_transformation,[],[f15])).
% 1.27/0.53  % SZS output end Proof for theBenchmark
% 1.27/0.53  % (31211)------------------------------
% 1.27/0.53  % (31211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (31211)Termination reason: Refutation
% 1.27/0.53  
% 1.27/0.53  % (31211)Memory used [KB]: 6268
% 1.27/0.53  % (31211)Time elapsed: 0.118 s
% 1.27/0.53  % (31211)------------------------------
% 1.27/0.53  % (31211)------------------------------
% 1.27/0.53  % (31220)Refutation not found, incomplete strategy% (31220)------------------------------
% 1.27/0.53  % (31220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (31216)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.53  % (31204)Success in time 0.172 s
%------------------------------------------------------------------------------
