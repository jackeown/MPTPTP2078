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
% DateTime   : Thu Dec  3 12:44:18 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 142 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 321 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(subsumption_resolution,[],[f98,f87])).

fof(f87,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f86,f77])).

fof(f77,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f76,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f75,f41])).

fof(f41,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f19,f30])).

fof(f30,plain,(
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

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f75,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f17,f44])).

fof(f44,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f20,f30])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f85,f41])).

fof(f85,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f18,f44])).

fof(f18,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f98,plain,(
    r1_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f96,f60])).

fof(f60,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f51,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f29,f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f47,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f43,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f21,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f42,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f19,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f96,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f78,f69])).

fof(f69,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f56,f37])).

fof(f56,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f52,f38])).

fof(f52,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f46,f39])).

fof(f46,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f20,f28])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f77,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:52:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (17553)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (17556)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (17545)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.52  % (17543)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.53  % (17563)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.53  % (17546)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.53  % (17542)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.53  % (17554)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (17547)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.53  % (17550)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.26/0.53  % (17565)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.54  % (17562)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.54  % (17561)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.54  % (17571)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.54  % (17549)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.54  % (17548)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.54  % (17551)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.26/0.54  % (17570)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.54  % (17563)Refutation found. Thanks to Tanya!
% 1.26/0.54  % SZS status Theorem for theBenchmark
% 1.26/0.54  % SZS output start Proof for theBenchmark
% 1.26/0.54  fof(f99,plain,(
% 1.26/0.54    $false),
% 1.26/0.54    inference(subsumption_resolution,[],[f98,f87])).
% 1.26/0.54  fof(f87,plain,(
% 1.26/0.54    ~r1_tarski(sK1,sK2)),
% 1.26/0.54    inference(subsumption_resolution,[],[f86,f77])).
% 1.26/0.54  fof(f77,plain,(
% 1.26/0.54    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 1.26/0.54    inference(subsumption_resolution,[],[f76,f35])).
% 1.26/0.54  fof(f35,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f16])).
% 1.26/0.54  fof(f16,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.26/0.54    inference(ennf_transformation,[],[f4])).
% 1.26/0.54  fof(f4,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.26/0.54  fof(f76,plain,(
% 1.26/0.54    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 1.26/0.54    inference(forward_demodulation,[],[f75,f41])).
% 1.26/0.54  fof(f41,plain,(
% 1.26/0.54    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.26/0.54    inference(resolution,[],[f19,f30])).
% 1.26/0.54  fof(f30,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f15])).
% 1.26/0.54  fof(f15,plain,(
% 1.26/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f8])).
% 1.26/0.54  fof(f8,axiom,(
% 1.26/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.26/0.54  fof(f19,plain,(
% 1.26/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(cnf_transformation,[],[f12])).
% 1.26/0.54  fof(f12,plain,(
% 1.26/0.54    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f11])).
% 1.26/0.54  fof(f11,negated_conjecture,(
% 1.26/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.26/0.54    inference(negated_conjecture,[],[f10])).
% 1.26/0.54  fof(f10,conjecture,(
% 1.26/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 1.26/0.54  fof(f75,plain,(
% 1.26/0.54    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 1.26/0.54    inference(forward_demodulation,[],[f17,f44])).
% 1.26/0.54  fof(f44,plain,(
% 1.26/0.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.26/0.54    inference(resolution,[],[f20,f30])).
% 1.26/0.54  fof(f20,plain,(
% 1.26/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(cnf_transformation,[],[f12])).
% 1.26/0.54  fof(f17,plain,(
% 1.26/0.54    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 1.26/0.54    inference(cnf_transformation,[],[f12])).
% 1.26/0.54  fof(f86,plain,(
% 1.26/0.54    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 1.26/0.54    inference(forward_demodulation,[],[f85,f41])).
% 1.26/0.54  fof(f85,plain,(
% 1.26/0.54    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 1.26/0.54    inference(forward_demodulation,[],[f18,f44])).
% 1.26/0.54  fof(f18,plain,(
% 1.26/0.54    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 1.26/0.54    inference(cnf_transformation,[],[f12])).
% 1.26/0.54  fof(f98,plain,(
% 1.26/0.54    r1_tarski(sK1,sK2)),
% 1.26/0.54    inference(forward_demodulation,[],[f96,f60])).
% 1.26/0.54  fof(f60,plain,(
% 1.26/0.54    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.26/0.54    inference(superposition,[],[f51,f37])).
% 1.26/0.54  fof(f37,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.26/0.54    inference(definition_unfolding,[],[f22,f23,f23])).
% 1.26/0.54  fof(f23,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f5])).
% 1.26/0.54  fof(f5,axiom,(
% 1.26/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.26/0.54  fof(f22,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f1])).
% 1.26/0.54  fof(f1,axiom,(
% 1.26/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.26/0.54  fof(f51,plain,(
% 1.26/0.54    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.26/0.54    inference(resolution,[],[f47,f38])).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.26/0.54    inference(definition_unfolding,[],[f29,f23])).
% 1.26/0.54  fof(f29,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.26/0.54    inference(cnf_transformation,[],[f14])).
% 1.26/0.54  fof(f14,plain,(
% 1.26/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.26/0.54    inference(ennf_transformation,[],[f3])).
% 1.26/0.54  fof(f3,axiom,(
% 1.26/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.26/0.54  fof(f47,plain,(
% 1.26/0.54    r1_tarski(sK2,sK0)),
% 1.26/0.54    inference(resolution,[],[f43,f39])).
% 1.26/0.54  fof(f39,plain,(
% 1.26/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.26/0.54    inference(equality_resolution,[],[f32])).
% 1.26/0.54  fof(f32,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.26/0.54    inference(cnf_transformation,[],[f6])).
% 1.26/0.54  fof(f6,axiom,(
% 1.26/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.26/0.54  fof(f43,plain,(
% 1.26/0.54    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(subsumption_resolution,[],[f42,f21])).
% 1.26/0.54  fof(f21,plain,(
% 1.26/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f9])).
% 1.26/0.54  fof(f9,axiom,(
% 1.26/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.26/0.54  fof(f42,plain,(
% 1.26/0.54    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(resolution,[],[f19,f28])).
% 1.26/0.54  fof(f28,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f13])).
% 1.26/0.54  fof(f13,plain,(
% 1.26/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f7])).
% 1.26/0.54  fof(f7,axiom,(
% 1.26/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.26/0.54  fof(f96,plain,(
% 1.26/0.54    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 1.26/0.54    inference(superposition,[],[f78,f69])).
% 1.26/0.54  fof(f69,plain,(
% 1.26/0.54    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.26/0.54    inference(superposition,[],[f56,f37])).
% 1.26/0.54  fof(f56,plain,(
% 1.26/0.54    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.26/0.54    inference(resolution,[],[f52,f38])).
% 1.26/0.54  fof(f52,plain,(
% 1.26/0.54    r1_tarski(sK1,sK0)),
% 1.26/0.54    inference(resolution,[],[f46,f39])).
% 1.26/0.54  fof(f46,plain,(
% 1.26/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(subsumption_resolution,[],[f45,f21])).
% 1.26/0.54  fof(f45,plain,(
% 1.26/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(resolution,[],[f20,f28])).
% 1.26/0.54  fof(f78,plain,(
% 1.26/0.54    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))) )),
% 1.26/0.54    inference(resolution,[],[f77,f35])).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (17563)------------------------------
% 1.26/0.54  % (17563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (17563)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (17563)Memory used [KB]: 1791
% 1.26/0.54  % (17563)Time elapsed: 0.118 s
% 1.26/0.54  % (17563)------------------------------
% 1.26/0.54  % (17563)------------------------------
% 1.26/0.55  % (17541)Success in time 0.184 s
%------------------------------------------------------------------------------
