%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:11 EST 2020

% Result     : Theorem 7.01s
% Output     : Refutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 304 expanded)
%              Number of leaves         :   15 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  134 ( 619 expanded)
%              Number of equality atoms :   44 ( 163 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13022,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13013,f533])).

fof(f533,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f525])).

fof(f525,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f334,f79])).

fof(f79,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f30,f74])).

fof(f74,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f32,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f30,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f334,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | r1_xboole_0(X3,k4_xboole_0(sK0,sK2)) ) ),
    inference(superposition,[],[f61,f115])).

fof(f115,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f95,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f42,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f95,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f88,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f81,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f81,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f76,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f13013,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f13006,f80])).

fof(f80,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f31,f74])).

fof(f31,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f13006,plain,(
    r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f12975,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f12975,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK1)
      | r1_tarski(X5,sK2) ) ),
    inference(superposition,[],[f60,f12938])).

fof(f12938,plain,(
    sK1 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f12907,f1964])).

fof(f1964,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1950,f240])).

fof(f240,plain,(
    sK1 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f225,f239])).

fof(f239,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f238,f213])).

fof(f213,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f103,f65])).

fof(f103,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f96,f66])).

fof(f96,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f87,f72])).

fof(f87,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f84,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f33,f46])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f238,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f237,f65])).

fof(f237,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f221,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f221,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f38,f103])).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f225,plain,(
    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f63,f103])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1950,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f63,f541])).

fof(f541,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f533,f67])).

fof(f12907,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f5472,f364])).

fof(f364,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) ),
    inference(superposition,[],[f58,f213])).

fof(f58,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f5472,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f332,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f332,plain,(
    ! [X1] : k4_xboole_0(sK2,X1) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) ),
    inference(superposition,[],[f58,f115])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:57:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.57  % (14779)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (14771)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (14778)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (14762)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (14770)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (14763)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.51/0.59  % (14758)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.51/0.60  % (14757)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.51/0.60  % (14757)Refutation not found, incomplete strategy% (14757)------------------------------
% 1.51/0.60  % (14757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.60  % (14757)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.60  
% 1.51/0.60  % (14757)Memory used [KB]: 1663
% 1.51/0.60  % (14757)Time elapsed: 0.166 s
% 1.51/0.60  % (14757)------------------------------
% 1.51/0.60  % (14757)------------------------------
% 1.89/0.60  % (14761)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.89/0.60  % (14768)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.89/0.61  % (14767)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.89/0.62  % (14756)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.89/0.62  % (14781)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.89/0.62  % (14760)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.89/0.63  % (14759)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.89/0.63  % (14773)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.89/0.63  % (14785)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.89/0.63  % (14785)Refutation not found, incomplete strategy% (14785)------------------------------
% 1.89/0.63  % (14785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.63  % (14785)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.63  
% 1.89/0.63  % (14785)Memory used [KB]: 1663
% 1.89/0.63  % (14785)Time elapsed: 0.194 s
% 1.89/0.63  % (14785)------------------------------
% 1.89/0.63  % (14785)------------------------------
% 1.89/0.63  % (14766)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.89/0.64  % (14765)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.89/0.64  % (14777)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.89/0.64  % (14766)Refutation not found, incomplete strategy% (14766)------------------------------
% 1.89/0.64  % (14766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.64  % (14766)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.64  
% 1.89/0.64  % (14766)Memory used [KB]: 10746
% 1.89/0.64  % (14766)Time elapsed: 0.194 s
% 1.89/0.64  % (14766)------------------------------
% 1.89/0.64  % (14766)------------------------------
% 1.89/0.64  % (14783)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.89/0.64  % (14774)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.89/0.64  % (14784)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.89/0.64  % (14769)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.89/0.64  % (14784)Refutation not found, incomplete strategy% (14784)------------------------------
% 1.89/0.64  % (14784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.64  % (14784)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.64  
% 1.89/0.64  % (14784)Memory used [KB]: 10746
% 1.89/0.64  % (14784)Time elapsed: 0.206 s
% 1.89/0.64  % (14784)------------------------------
% 1.89/0.64  % (14784)------------------------------
% 1.89/0.64  % (14772)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.89/0.64  % (14775)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.89/0.64  % (14776)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.89/0.65  % (14782)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.27/0.66  % (14764)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.27/0.66  % (14780)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.27/0.68  % (14772)Refutation not found, incomplete strategy% (14772)------------------------------
% 2.27/0.68  % (14772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.68  % (14772)Termination reason: Refutation not found, incomplete strategy
% 2.27/0.68  
% 2.27/0.68  % (14772)Memory used [KB]: 10618
% 2.27/0.68  % (14772)Time elapsed: 0.245 s
% 2.27/0.68  % (14772)------------------------------
% 2.27/0.68  % (14772)------------------------------
% 2.91/0.78  % (14823)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.19/0.79  % (14759)Refutation not found, incomplete strategy% (14759)------------------------------
% 3.19/0.79  % (14759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.80  % (14824)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.19/0.81  % (14759)Termination reason: Refutation not found, incomplete strategy
% 3.19/0.81  
% 3.19/0.81  % (14759)Memory used [KB]: 6140
% 3.19/0.81  % (14759)Time elapsed: 0.356 s
% 3.19/0.81  % (14759)------------------------------
% 3.19/0.81  % (14759)------------------------------
% 3.19/0.84  % (14758)Time limit reached!
% 3.19/0.84  % (14758)------------------------------
% 3.19/0.84  % (14758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.52/0.84  % (14828)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.52/0.84  % (14758)Termination reason: Time limit
% 3.52/0.84  % (14758)Termination phase: Saturation
% 3.52/0.84  
% 3.52/0.84  % (14758)Memory used [KB]: 6396
% 3.52/0.84  % (14758)Time elapsed: 0.400 s
% 3.52/0.84  % (14758)------------------------------
% 3.52/0.84  % (14758)------------------------------
% 3.55/0.84  % (14827)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.55/0.85  % (14780)Time limit reached!
% 3.55/0.85  % (14780)------------------------------
% 3.55/0.85  % (14780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.85  % (14780)Termination reason: Time limit
% 3.55/0.85  % (14780)Termination phase: Saturation
% 3.55/0.85  
% 3.55/0.85  % (14780)Memory used [KB]: 12537
% 3.55/0.85  % (14780)Time elapsed: 0.400 s
% 3.55/0.85  % (14780)------------------------------
% 3.55/0.85  % (14780)------------------------------
% 3.55/0.88  % (14829)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.55/0.90  % (14883)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.91/0.94  % (14899)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.91/0.95  % (14770)Time limit reached!
% 3.91/0.95  % (14770)------------------------------
% 3.91/0.95  % (14770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.95  % (14770)Termination reason: Time limit
% 3.91/0.95  
% 3.91/0.95  % (14770)Memory used [KB]: 4989
% 3.91/0.95  % (14770)Time elapsed: 0.513 s
% 3.91/0.95  % (14770)------------------------------
% 3.91/0.95  % (14770)------------------------------
% 3.91/0.95  % (14762)Time limit reached!
% 3.91/0.95  % (14762)------------------------------
% 3.91/0.95  % (14762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.96  % (14762)Termination reason: Time limit
% 4.19/0.96  % (14762)Termination phase: Saturation
% 4.19/0.96  
% 4.19/0.96  % (14762)Memory used [KB]: 16630
% 4.19/0.96  % (14762)Time elapsed: 0.500 s
% 4.19/0.96  % (14762)------------------------------
% 4.19/0.96  % (14762)------------------------------
% 4.19/0.99  % (14908)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.74/1.09  % (14967)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.96/1.10  % (14971)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.96/1.13  % (14763)Time limit reached!
% 4.96/1.13  % (14763)------------------------------
% 4.96/1.13  % (14763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.13  % (14763)Termination reason: Time limit
% 4.96/1.13  % (14763)Termination phase: Saturation
% 4.96/1.13  
% 4.96/1.13  % (14763)Memory used [KB]: 7164
% 4.96/1.13  % (14763)Time elapsed: 0.600 s
% 4.96/1.13  % (14763)------------------------------
% 4.96/1.13  % (14763)------------------------------
% 7.01/1.28  % (15014)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 7.01/1.33  % (14773)Refutation found. Thanks to Tanya!
% 7.01/1.33  % SZS status Theorem for theBenchmark
% 7.01/1.34  % SZS output start Proof for theBenchmark
% 7.01/1.34  fof(f13022,plain,(
% 7.01/1.34    $false),
% 7.01/1.34    inference(subsumption_resolution,[],[f13013,f533])).
% 7.01/1.34  fof(f533,plain,(
% 7.01/1.34    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.01/1.34    inference(duplicate_literal_removal,[],[f525])).
% 7.01/1.34  fof(f525,plain,(
% 7.01/1.34    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.01/1.34    inference(resolution,[],[f334,f79])).
% 7.01/1.34  fof(f79,plain,(
% 7.01/1.34    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.01/1.34    inference(backward_demodulation,[],[f30,f74])).
% 7.01/1.34  fof(f74,plain,(
% 7.01/1.34    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 7.01/1.34    inference(resolution,[],[f32,f48])).
% 7.01/1.34  fof(f48,plain,(
% 7.01/1.34    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 7.01/1.34    inference(cnf_transformation,[],[f26])).
% 7.01/1.34  fof(f26,plain,(
% 7.01/1.34    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.01/1.34    inference(ennf_transformation,[],[f18])).
% 7.01/1.34  fof(f18,axiom,(
% 7.01/1.34    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 7.01/1.34  fof(f32,plain,(
% 7.01/1.34    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.01/1.34    inference(cnf_transformation,[],[f23])).
% 7.01/1.34  fof(f23,plain,(
% 7.01/1.34    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.01/1.34    inference(ennf_transformation,[],[f21])).
% 7.01/1.34  fof(f21,negated_conjecture,(
% 7.01/1.34    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 7.01/1.34    inference(negated_conjecture,[],[f20])).
% 7.01/1.34  fof(f20,conjecture,(
% 7.01/1.34    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 7.01/1.34  fof(f30,plain,(
% 7.01/1.34    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 7.01/1.34    inference(cnf_transformation,[],[f23])).
% 7.01/1.34  fof(f334,plain,(
% 7.01/1.34    ( ! [X3] : (~r1_tarski(X3,sK2) | r1_xboole_0(X3,k4_xboole_0(sK0,sK2))) )),
% 7.01/1.34    inference(superposition,[],[f61,f115])).
% 7.01/1.34  fof(f115,plain,(
% 7.01/1.34    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 7.01/1.34    inference(superposition,[],[f95,f65])).
% 7.01/1.34  fof(f65,plain,(
% 7.01/1.34    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.01/1.34    inference(definition_unfolding,[],[f40,f42,f42])).
% 7.01/1.34  fof(f42,plain,(
% 7.01/1.34    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.01/1.34    inference(cnf_transformation,[],[f12])).
% 7.01/1.34  fof(f12,axiom,(
% 7.01/1.34    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 7.01/1.34  fof(f40,plain,(
% 7.01/1.34    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.01/1.34    inference(cnf_transformation,[],[f2])).
% 7.01/1.34  fof(f2,axiom,(
% 7.01/1.34    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.01/1.34  fof(f95,plain,(
% 7.01/1.34    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 7.01/1.34    inference(resolution,[],[f88,f66])).
% 7.01/1.34  fof(f66,plain,(
% 7.01/1.34    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 7.01/1.34    inference(definition_unfolding,[],[f47,f42])).
% 7.01/1.34  fof(f47,plain,(
% 7.01/1.34    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 7.01/1.34    inference(cnf_transformation,[],[f25])).
% 7.01/1.34  fof(f25,plain,(
% 7.01/1.34    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.01/1.34    inference(ennf_transformation,[],[f9])).
% 7.01/1.34  fof(f9,axiom,(
% 7.01/1.34    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 7.01/1.34  fof(f88,plain,(
% 7.01/1.34    r1_tarski(sK2,sK0)),
% 7.01/1.34    inference(resolution,[],[f81,f72])).
% 7.01/1.34  fof(f72,plain,(
% 7.01/1.34    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 7.01/1.34    inference(equality_resolution,[],[f55])).
% 7.01/1.34  fof(f55,plain,(
% 7.01/1.34    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.01/1.34    inference(cnf_transformation,[],[f16])).
% 7.01/1.34  fof(f16,axiom,(
% 7.01/1.34    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 7.01/1.34  fof(f81,plain,(
% 7.01/1.34    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 7.01/1.34    inference(subsumption_resolution,[],[f76,f34])).
% 7.01/1.34  fof(f34,plain,(
% 7.01/1.34    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.01/1.34    inference(cnf_transformation,[],[f19])).
% 7.01/1.34  fof(f19,axiom,(
% 7.01/1.34    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 7.01/1.34  fof(f76,plain,(
% 7.01/1.34    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 7.01/1.34    inference(resolution,[],[f32,f46])).
% 7.01/1.34  fof(f46,plain,(
% 7.01/1.34    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 7.01/1.34    inference(cnf_transformation,[],[f24])).
% 7.01/1.34  fof(f24,plain,(
% 7.01/1.34    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.01/1.34    inference(ennf_transformation,[],[f17])).
% 7.01/1.34  fof(f17,axiom,(
% 7.01/1.34    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 7.01/1.34  fof(f61,plain,(
% 7.01/1.34    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 7.01/1.34    inference(cnf_transformation,[],[f27])).
% 7.01/1.34  fof(f27,plain,(
% 7.01/1.34    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.01/1.34    inference(ennf_transformation,[],[f7])).
% 7.01/1.34  fof(f7,axiom,(
% 7.01/1.34    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 7.01/1.34  fof(f13013,plain,(
% 7.01/1.34    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.01/1.34    inference(resolution,[],[f13006,f80])).
% 7.01/1.34  fof(f80,plain,(
% 7.01/1.34    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.01/1.34    inference(backward_demodulation,[],[f31,f74])).
% 7.01/1.34  fof(f31,plain,(
% 7.01/1.34    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 7.01/1.34    inference(cnf_transformation,[],[f23])).
% 7.01/1.34  fof(f13006,plain,(
% 7.01/1.34    r1_tarski(sK1,sK2)),
% 7.01/1.34    inference(resolution,[],[f12975,f71])).
% 7.01/1.34  fof(f71,plain,(
% 7.01/1.34    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.01/1.34    inference(equality_resolution,[],[f49])).
% 7.01/1.34  fof(f49,plain,(
% 7.01/1.34    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.01/1.34    inference(cnf_transformation,[],[f5])).
% 7.01/1.34  fof(f5,axiom,(
% 7.01/1.34    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.01/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.01/1.34  fof(f12975,plain,(
% 7.01/1.34    ( ! [X5] : (~r1_tarski(X5,sK1) | r1_tarski(X5,sK2)) )),
% 7.01/1.34    inference(superposition,[],[f60,f12938])).
% 7.01/1.34  fof(f12938,plain,(
% 7.01/1.34    sK1 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 7.01/1.34    inference(forward_demodulation,[],[f12907,f1964])).
% 7.01/1.34  fof(f1964,plain,(
% 7.01/1.34    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.01/1.34    inference(forward_demodulation,[],[f1950,f240])).
% 7.01/1.34  fof(f240,plain,(
% 7.01/1.34    sK1 = k5_xboole_0(sK1,k1_xboole_0)),
% 7.01/1.34    inference(backward_demodulation,[],[f225,f239])).
% 7.01/1.34  fof(f239,plain,(
% 7.01/1.34    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 7.01/1.34    inference(forward_demodulation,[],[f238,f213])).
% 7.01/1.34  fof(f213,plain,(
% 7.01/1.34    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 7.01/1.34    inference(superposition,[],[f103,f65])).
% 7.68/1.34  fof(f103,plain,(
% 7.68/1.34    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 7.68/1.34    inference(resolution,[],[f96,f66])).
% 7.68/1.34  fof(f96,plain,(
% 7.68/1.34    r1_tarski(sK1,sK0)),
% 7.68/1.34    inference(resolution,[],[f87,f72])).
% 7.68/1.34  fof(f87,plain,(
% 7.68/1.34    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 7.68/1.34    inference(subsumption_resolution,[],[f84,f34])).
% 7.68/1.34  fof(f84,plain,(
% 7.68/1.34    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 7.68/1.34    inference(resolution,[],[f33,f46])).
% 7.68/1.34  fof(f33,plain,(
% 7.68/1.34    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.68/1.34    inference(cnf_transformation,[],[f23])).
% 7.68/1.34  fof(f238,plain,(
% 7.68/1.34    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 7.68/1.34    inference(forward_demodulation,[],[f237,f65])).
% 7.68/1.34  fof(f237,plain,(
% 7.68/1.34    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 7.68/1.34    inference(resolution,[],[f221,f67])).
% 7.68/1.34  fof(f67,plain,(
% 7.68/1.34    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.68/1.34    inference(definition_unfolding,[],[f53,f42])).
% 7.68/1.34  fof(f53,plain,(
% 7.68/1.34    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.68/1.34    inference(cnf_transformation,[],[f3])).
% 7.68/1.34  fof(f3,axiom,(
% 7.68/1.34    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.68/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 7.68/1.34  fof(f221,plain,(
% 7.68/1.34    r1_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 7.68/1.34    inference(superposition,[],[f38,f103])).
% 7.68/1.34  fof(f38,plain,(
% 7.68/1.34    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.68/1.34    inference(cnf_transformation,[],[f15])).
% 7.68/1.34  fof(f15,axiom,(
% 7.68/1.34    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.68/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 7.68/1.34  fof(f225,plain,(
% 7.68/1.34    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 7.68/1.34    inference(superposition,[],[f63,f103])).
% 7.68/1.34  fof(f63,plain,(
% 7.68/1.34    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.68/1.34    inference(definition_unfolding,[],[f41,f42])).
% 7.68/1.34  fof(f41,plain,(
% 7.68/1.34    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.68/1.34    inference(cnf_transformation,[],[f6])).
% 7.68/1.34  fof(f6,axiom,(
% 7.68/1.34    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.68/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 7.68/1.34  fof(f1950,plain,(
% 7.68/1.34    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,k1_xboole_0)),
% 7.68/1.34    inference(superposition,[],[f63,f541])).
% 7.68/1.34  fof(f541,plain,(
% 7.68/1.34    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 7.68/1.34    inference(resolution,[],[f533,f67])).
% 7.68/1.34  fof(f12907,plain,(
% 7.68/1.34    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 7.68/1.34    inference(superposition,[],[f5472,f364])).
% 7.68/1.34  fof(f364,plain,(
% 7.68/1.34    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X1))) )),
% 7.68/1.34    inference(superposition,[],[f58,f213])).
% 7.68/1.34  fof(f58,plain,(
% 7.68/1.34    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.68/1.34    inference(cnf_transformation,[],[f11])).
% 7.68/1.34  fof(f11,axiom,(
% 7.68/1.34    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.68/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 7.68/1.34  fof(f5472,plain,(
% 7.68/1.34    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK2)))) )),
% 7.68/1.34    inference(superposition,[],[f332,f39])).
% 7.68/1.34  fof(f39,plain,(
% 7.68/1.34    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.68/1.34    inference(cnf_transformation,[],[f1])).
% 7.68/1.34  fof(f1,axiom,(
% 7.68/1.34    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.68/1.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 7.68/1.34  fof(f332,plain,(
% 7.68/1.34    ( ! [X1] : (k4_xboole_0(sK2,X1) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X1))) )),
% 7.68/1.34    inference(superposition,[],[f58,f115])).
% 7.68/1.34  fof(f60,plain,(
% 7.68/1.34    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 7.68/1.34    inference(cnf_transformation,[],[f27])).
% 7.68/1.34  % SZS output end Proof for theBenchmark
% 7.68/1.34  % (14773)------------------------------
% 7.68/1.34  % (14773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.68/1.34  % (14773)Termination reason: Refutation
% 7.68/1.34  
% 7.68/1.34  % (14773)Memory used [KB]: 8955
% 7.68/1.34  % (14773)Time elapsed: 0.900 s
% 7.68/1.34  % (14773)------------------------------
% 7.68/1.34  % (14773)------------------------------
% 7.68/1.34  % (14755)Success in time 0.972 s
%------------------------------------------------------------------------------
