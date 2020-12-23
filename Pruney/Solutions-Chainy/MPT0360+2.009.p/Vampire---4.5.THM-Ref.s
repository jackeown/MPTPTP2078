%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:49 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 176 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  107 ( 293 expanded)
%              Number of equality atoms :   49 ( 150 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f729,plain,(
    $false ),
    inference(subsumption_resolution,[],[f728,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f728,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f106,f727])).

fof(f727,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f725,f505])).

fof(f505,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f427,f440])).

fof(f440,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f397,f431])).

fof(f431,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f416,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f416,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f56,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

% (6704)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

% (6703)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f397,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f56,f57])).

fof(f427,plain,(
    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f56,f80])).

fof(f80,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f60,f28])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f725,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f723,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f48,f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f723,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f717,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f717,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f692,f68])).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f692,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(sK0,sK2))
      | r1_xboole_0(X0,sK1) ) ),
    inference(forward_demodulation,[],[f688,f33])).

fof(f688,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k5_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0))
      | r1_xboole_0(X0,sK1) ) ),
    inference(superposition,[],[f64,f518])).

fof(f518,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f428,f440])).

fof(f428,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f56,f315])).

fof(f315,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(backward_demodulation,[],[f81,f312])).

fof(f312,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f81,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f60,f29])).

fof(f29,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f54,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f106,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f58,f103])).

fof(f103,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f100,f80])).

fof(f100,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f61,f84])).

fof(f84,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f35,f80])).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:27:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.58  % (6714)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (6708)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.58  % (6706)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.59  % (6698)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.46/0.59  % (6700)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.59  % (6716)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.60  % (6714)Refutation not found, incomplete strategy% (6714)------------------------------
% 1.46/0.60  % (6714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.60  % (6714)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.60  
% 1.46/0.60  % (6714)Memory used [KB]: 10746
% 1.46/0.60  % (6714)Time elapsed: 0.155 s
% 1.46/0.60  % (6714)------------------------------
% 1.46/0.60  % (6714)------------------------------
% 1.84/0.61  % (6692)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.84/0.61  % (6695)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.84/0.61  % (6697)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.84/0.61  % (6692)Refutation not found, incomplete strategy% (6692)------------------------------
% 1.84/0.61  % (6692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (6692)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (6692)Memory used [KB]: 1791
% 1.84/0.61  % (6692)Time elapsed: 0.122 s
% 1.84/0.61  % (6692)------------------------------
% 1.84/0.61  % (6692)------------------------------
% 1.84/0.61  % (6698)Refutation found. Thanks to Tanya!
% 1.84/0.61  % SZS status Theorem for theBenchmark
% 1.84/0.61  % SZS output start Proof for theBenchmark
% 1.84/0.61  fof(f729,plain,(
% 1.84/0.61    $false),
% 1.84/0.61    inference(subsumption_resolution,[],[f728,f30])).
% 1.84/0.61  fof(f30,plain,(
% 1.84/0.61    k1_xboole_0 != sK1),
% 1.84/0.61    inference(cnf_transformation,[],[f21])).
% 1.84/0.61  fof(f21,plain,(
% 1.84/0.61    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.84/0.61    inference(flattening,[],[f20])).
% 1.84/0.61  fof(f20,plain,(
% 1.84/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.84/0.61    inference(ennf_transformation,[],[f18])).
% 1.84/0.61  fof(f18,negated_conjecture,(
% 1.84/0.61    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.84/0.61    inference(negated_conjecture,[],[f17])).
% 1.84/0.61  fof(f17,conjecture,(
% 1.84/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 1.84/0.61  fof(f728,plain,(
% 1.84/0.61    k1_xboole_0 = sK1),
% 1.84/0.61    inference(backward_demodulation,[],[f106,f727])).
% 1.84/0.61  fof(f727,plain,(
% 1.84/0.61    k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.84/0.61    inference(forward_demodulation,[],[f725,f505])).
% 1.84/0.61  fof(f505,plain,(
% 1.84/0.61    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.84/0.61    inference(forward_demodulation,[],[f427,f440])).
% 1.84/0.61  fof(f440,plain,(
% 1.84/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.84/0.61    inference(backward_demodulation,[],[f397,f431])).
% 1.84/0.61  fof(f431,plain,(
% 1.84/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.84/0.61    inference(forward_demodulation,[],[f416,f33])).
% 1.84/0.61  fof(f33,plain,(
% 1.84/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f9])).
% 1.84/0.61  fof(f9,axiom,(
% 1.84/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.84/0.61  fof(f416,plain,(
% 1.84/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.84/0.61    inference(superposition,[],[f56,f57])).
% 1.84/0.61  fof(f57,plain,(
% 1.84/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f32,f39])).
% 1.84/0.61  fof(f39,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f8])).
% 1.84/0.61  fof(f8,axiom,(
% 1.84/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.84/0.61  fof(f32,plain,(
% 1.84/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f7])).
% 1.84/0.61  fof(f7,axiom,(
% 1.84/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.84/0.61  % (6704)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.84/0.61  fof(f56,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f38,f39])).
% 1.84/0.61  fof(f38,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f5])).
% 1.84/0.61  % (6703)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.84/0.61  fof(f5,axiom,(
% 1.84/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.84/0.61  fof(f397,plain,(
% 1.84/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.84/0.61    inference(superposition,[],[f56,f57])).
% 1.84/0.61  fof(f427,plain,(
% 1.84/0.61    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK1)),
% 1.84/0.61    inference(superposition,[],[f56,f80])).
% 1.84/0.61  fof(f80,plain,(
% 1.84/0.61    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.84/0.61    inference(resolution,[],[f60,f28])).
% 1.84/0.61  fof(f28,plain,(
% 1.84/0.61    r1_tarski(sK1,sK2)),
% 1.84/0.61    inference(cnf_transformation,[],[f21])).
% 1.84/0.61  fof(f60,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.84/0.61    inference(definition_unfolding,[],[f44,f39])).
% 1.84/0.61  fof(f44,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f23])).
% 1.84/0.61  fof(f23,plain,(
% 1.84/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f6])).
% 1.84/0.61  fof(f6,axiom,(
% 1.84/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.84/0.61  fof(f725,plain,(
% 1.84/0.61    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.84/0.61    inference(resolution,[],[f723,f61])).
% 1.84/0.61  fof(f61,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f48,f39])).
% 1.84/0.61  fof(f48,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f2])).
% 1.84/0.61  fof(f2,axiom,(
% 1.84/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.84/0.61  fof(f723,plain,(
% 1.84/0.61    r1_xboole_0(sK1,sK2)),
% 1.84/0.61    inference(resolution,[],[f717,f45])).
% 1.84/0.61  fof(f45,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f24])).
% 1.84/0.61  fof(f24,plain,(
% 1.84/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f4])).
% 1.84/0.61  fof(f4,axiom,(
% 1.84/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.84/0.61  fof(f717,plain,(
% 1.84/0.61    r1_xboole_0(sK2,sK1)),
% 1.84/0.61    inference(resolution,[],[f692,f68])).
% 1.84/0.61  fof(f68,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.84/0.61    inference(resolution,[],[f45,f35])).
% 1.84/0.61  fof(f35,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f11])).
% 1.84/0.61  fof(f11,axiom,(
% 1.84/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.84/0.61  fof(f692,plain,(
% 1.84/0.61    ( ! [X0] : (~r1_xboole_0(X0,k4_xboole_0(sK0,sK2)) | r1_xboole_0(X0,sK1)) )),
% 1.84/0.61    inference(forward_demodulation,[],[f688,f33])).
% 1.84/0.61  fof(f688,plain,(
% 1.84/0.61    ( ! [X0] : (~r1_xboole_0(X0,k5_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)) | r1_xboole_0(X0,sK1)) )),
% 1.84/0.61    inference(superposition,[],[f64,f518])).
% 1.84/0.61  fof(f518,plain,(
% 1.84/0.61    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.84/0.61    inference(forward_demodulation,[],[f428,f440])).
% 1.84/0.61  fof(f428,plain,(
% 1.84/0.61    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,sK1)),
% 1.84/0.61    inference(superposition,[],[f56,f315])).
% 1.84/0.61  fof(f315,plain,(
% 1.84/0.61    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 1.84/0.61    inference(backward_demodulation,[],[f81,f312])).
% 1.84/0.61  fof(f312,plain,(
% 1.84/0.61    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.84/0.61    inference(resolution,[],[f46,f27])).
% 1.84/0.61  fof(f27,plain,(
% 1.84/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.84/0.61    inference(cnf_transformation,[],[f21])).
% 1.84/0.61  fof(f46,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f25])).
% 1.84/0.61  fof(f25,plain,(
% 1.84/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.84/0.61    inference(ennf_transformation,[],[f15])).
% 1.84/0.61  fof(f15,axiom,(
% 1.84/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.84/0.61  fof(f81,plain,(
% 1.84/0.61    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK2)))),
% 1.84/0.61    inference(resolution,[],[f60,f29])).
% 1.84/0.61  fof(f29,plain,(
% 1.84/0.61    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.84/0.61    inference(cnf_transformation,[],[f21])).
% 1.84/0.61  fof(f64,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) | r1_xboole_0(X0,X2)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f54,f37])).
% 1.84/0.61  fof(f37,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f12])).
% 1.84/0.61  fof(f12,axiom,(
% 1.84/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.84/0.61  fof(f54,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f26])).
% 1.84/0.61  fof(f26,plain,(
% 1.84/0.61    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.84/0.61    inference(ennf_transformation,[],[f10])).
% 1.84/0.61  fof(f10,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.84/0.61  fof(f106,plain,(
% 1.84/0.61    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.84/0.61    inference(superposition,[],[f58,f103])).
% 1.84/0.61  fof(f103,plain,(
% 1.84/0.61    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.84/0.61    inference(forward_demodulation,[],[f100,f80])).
% 1.84/0.61  fof(f100,plain,(
% 1.84/0.61    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.84/0.61    inference(resolution,[],[f61,f84])).
% 1.84/0.61  fof(f84,plain,(
% 1.84/0.61    r1_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.84/0.61    inference(superposition,[],[f35,f80])).
% 1.84/0.61  fof(f58,plain,(
% 1.84/0.61    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.84/0.61    inference(definition_unfolding,[],[f34,f39])).
% 1.84/0.61  fof(f34,plain,(
% 1.84/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f19])).
% 1.84/0.61  fof(f19,plain,(
% 1.84/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.84/0.61    inference(rectify,[],[f3])).
% 1.84/0.61  fof(f3,axiom,(
% 1.84/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.84/0.61  % SZS output end Proof for theBenchmark
% 1.84/0.61  % (6698)------------------------------
% 1.84/0.61  % (6698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (6698)Termination reason: Refutation
% 1.84/0.61  
% 1.84/0.61  % (6698)Memory used [KB]: 6524
% 1.84/0.61  % (6698)Time elapsed: 0.155 s
% 1.84/0.61  % (6698)------------------------------
% 1.84/0.61  % (6698)------------------------------
% 1.84/0.62  % (6691)Success in time 0.242 s
%------------------------------------------------------------------------------
