%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 186 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 327 expanded)
%              Number of equality atoms :   53 ( 144 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(subsumption_resolution,[],[f371,f100])).

fof(f100,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f53,f98])).

fof(f98,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f38,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f53,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f23,f25])).

fof(f25,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f23,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f371,plain,(
    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f360,f295])).

fof(f295,plain,(
    sK0 = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f294,f170])).

fof(f170,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f165,f47])).

fof(f47,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f26,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f165,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0)) ),
    inference(superposition,[],[f49,f64])).

fof(f64,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f43,f61])).

fof(f61,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f60,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f60,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f24,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f58,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f37,f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f46,f46])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f294,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f289,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f32,f32])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f289,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f279,f49])).

fof(f279,plain,(
    ! [X0] : k4_subset_1(sK0,k4_xboole_0(sK0,X0),sK1) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,X0))) ),
    inference(forward_demodulation,[],[f272,f48])).

fof(f272,plain,(
    ! [X0] : k4_subset_1(sK0,k4_xboole_0(sK0,X0),sK1) = k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1)) ),
    inference(resolution,[],[f262,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f262,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1)) ) ),
    inference(resolution,[],[f260,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f260,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1)) ) ),
    inference(resolution,[],[f204,f54])).

% (18781)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f204,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1)) ) ),
    inference(resolution,[],[f50,f22])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f360,plain,(
    ! [X0] : k4_subset_1(sK0,k4_xboole_0(sK0,X0),sK1) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f279,f350])).

fof(f350,plain,(
    ! [X0] : k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,X0))) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f339,f29])).

fof(f339,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f337,f52])).

fof(f337,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f205,f22])).

fof(f205,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k4_subset_1(X2,X1,X3) = k3_tarski(k2_enumset1(X1,X1,X1,X3))
      | ~ r2_hidden(X3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f50,f54])).

% (18779)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (18766)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (18758)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (18758)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (18757)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18765)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.53  % (18753)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.53  % (18777)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.53  % (18754)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.53  % (18775)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.53  % (18755)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.53  % (18752)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (18756)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.54  % (18752)Refutation not found, incomplete strategy% (18752)------------------------------
% 1.34/0.54  % (18752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (18752)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (18752)Memory used [KB]: 1663
% 1.34/0.54  % (18752)Time elapsed: 0.124 s
% 1.34/0.54  % (18752)------------------------------
% 1.34/0.54  % (18752)------------------------------
% 1.34/0.54  % (18775)Refutation not found, incomplete strategy% (18775)------------------------------
% 1.34/0.54  % (18775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f375,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(subsumption_resolution,[],[f371,f100])).
% 1.34/0.54  fof(f100,plain,(
% 1.34/0.54    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.34/0.54    inference(backward_demodulation,[],[f53,f98])).
% 1.34/0.54  fof(f98,plain,(
% 1.34/0.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.34/0.54    inference(resolution,[],[f38,f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.34/0.54    inference(negated_conjecture,[],[f15])).
% 1.34/0.54  fof(f15,conjecture,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,axiom,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.34/0.54  fof(f53,plain,(
% 1.34/0.54    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.34/0.54    inference(backward_demodulation,[],[f23,f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f371,plain,(
% 1.34/0.54    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.34/0.54    inference(superposition,[],[f360,f295])).
% 1.34/0.54  fof(f295,plain,(
% 1.34/0.54    sK0 = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1)),
% 1.34/0.54    inference(forward_demodulation,[],[f294,f170])).
% 1.34/0.54  fof(f170,plain,(
% 1.34/0.54    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.34/0.54    inference(forward_demodulation,[],[f165,f47])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.34/0.54    inference(definition_unfolding,[],[f26,f46])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f31,f32])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.34/0.54  fof(f165,plain,(
% 1.34/0.54    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0))),
% 1.34/0.54    inference(superposition,[],[f49,f64])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.34/0.54    inference(resolution,[],[f43,f61])).
% 1.34/0.54  fof(f61,plain,(
% 1.34/0.54    r1_tarski(sK1,sK0)),
% 1.34/0.54    inference(resolution,[],[f60,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.34/0.54    inference(equality_resolution,[],[f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.54    inference(subsumption_resolution,[],[f58,f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.34/0.54    inference(resolution,[],[f37,f22])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.34/0.54  fof(f43,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f33,f46,f46])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.34/0.54  fof(f294,plain,(
% 1.34/0.54    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1)),
% 1.34/0.54    inference(forward_demodulation,[],[f289,f48])).
% 1.34/0.54  fof(f48,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f30,f32,f32])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.34/0.54  fof(f289,plain,(
% 1.34/0.54    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1)),
% 1.34/0.54    inference(superposition,[],[f279,f49])).
% 1.34/0.54  fof(f279,plain,(
% 1.34/0.54    ( ! [X0] : (k4_subset_1(sK0,k4_xboole_0(sK0,X0),sK1) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,X0)))) )),
% 1.34/0.54    inference(forward_demodulation,[],[f272,f48])).
% 1.34/0.54  fof(f272,plain,(
% 1.34/0.54    ( ! [X0] : (k4_subset_1(sK0,k4_xboole_0(sK0,X0),sK1) = k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1))) )),
% 1.34/0.54    inference(resolution,[],[f262,f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.34/0.54  fof(f262,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1))) )),
% 1.34/0.54    inference(resolution,[],[f260,f52])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.34/0.54    inference(equality_resolution,[],[f39])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f8])).
% 1.34/0.54  fof(f260,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1))) )),
% 1.34/0.54    inference(resolution,[],[f204,f54])).
% 1.34/0.54  % (18781)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f36,f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f18])).
% 1.34/0.54  fof(f204,plain,(
% 1.34/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1))) )),
% 1.34/0.54    inference(resolution,[],[f50,f22])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f45,f46])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f21])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.54    inference(flattening,[],[f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.34/0.54    inference(ennf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.34/0.54  fof(f360,plain,(
% 1.34/0.54    ( ! [X0] : (k4_subset_1(sK0,k4_xboole_0(sK0,X0),sK1) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,X0))) )),
% 1.34/0.54    inference(backward_demodulation,[],[f279,f350])).
% 1.34/0.54  fof(f350,plain,(
% 1.34/0.54    ( ! [X0] : (k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,X0))) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,X0))) )),
% 1.34/0.54    inference(resolution,[],[f339,f29])).
% 1.34/0.54  fof(f339,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) = k4_subset_1(sK0,sK1,X0)) )),
% 1.34/0.54    inference(resolution,[],[f337,f52])).
% 1.34/0.54  fof(f337,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) = k4_subset_1(sK0,sK1,X0)) )),
% 1.34/0.54    inference(resolution,[],[f205,f22])).
% 1.34/0.54  fof(f205,plain,(
% 1.34/0.54    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X1,X3) = k3_tarski(k2_enumset1(X1,X1,X1,X3)) | ~r2_hidden(X3,k1_zfmisc_1(X2))) )),
% 1.34/0.54    inference(resolution,[],[f50,f54])).
% 1.34/0.54  % (18779)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (18758)------------------------------
% 1.34/0.54  % (18758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (18758)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (18758)Memory used [KB]: 6396
% 1.34/0.54  % (18758)Time elapsed: 0.105 s
% 1.34/0.54  % (18758)------------------------------
% 1.34/0.54  % (18758)------------------------------
% 1.34/0.54  % (18751)Success in time 0.177 s
%------------------------------------------------------------------------------
