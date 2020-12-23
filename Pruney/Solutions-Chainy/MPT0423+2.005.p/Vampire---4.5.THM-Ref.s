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
% DateTime   : Thu Dec  3 12:46:29 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 676 expanded)
%              Number of leaves         :   28 ( 212 expanded)
%              Depth                    :   22
%              Number of atoms          :  220 ( 906 expanded)
%              Number of equality atoms :   97 ( 582 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(subsumption_resolution,[],[f443,f168])).

% (15422)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (15432)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (15422)Refutation not found, incomplete strategy% (15422)------------------------------
% (15422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15422)Termination reason: Refutation not found, incomplete strategy

% (15422)Memory used [KB]: 10618
% (15422)Time elapsed: 0.150 s
% (15422)------------------------------
% (15422)------------------------------
% (15414)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (15415)Refutation not found, incomplete strategy% (15415)------------------------------
% (15415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15415)Termination reason: Refutation not found, incomplete strategy

% (15415)Memory used [KB]: 10618
% (15415)Time elapsed: 0.152 s
% (15415)------------------------------
% (15415)------------------------------
% (15414)Refutation not found, incomplete strategy% (15414)------------------------------
% (15414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15414)Termination reason: Refutation not found, incomplete strategy

% (15414)Memory used [KB]: 10618
% (15414)Time elapsed: 0.149 s
% (15414)------------------------------
% (15414)------------------------------
% (15424)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (15430)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f168,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f144,f109])).

fof(f109,plain,(
    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f106])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f103])).

fof(f103,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_setfam_1)).

fof(f144,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f143,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f143,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f124,f112])).

fof(f112,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f50,f106])).

fof(f50,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f124,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f75,f106,f105,f106,f106])).

fof(f105,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f57,f104])).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f103])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f443,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f428,f212])).

fof(f212,plain,(
    ! [X0] : k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f211,f174])).

fof(f174,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(resolution,[],[f64,f113])).

fof(f113,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f52,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f211,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0)
      | ~ m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(trivial_inequality_removal,[],[f210])).

fof(f210,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0)
      | ~ m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f65,f170])).

fof(f170,plain,(
    ! [X0] : k1_xboole_0 = k7_setfam_1(X0,k7_setfam_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f63,f113])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f428,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f169,f426])).

fof(f426,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f424,f142])).

fof(f142,plain,(
    k1_zfmisc_1(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f108,f110])).

fof(f110,plain,(
    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f46,f106])).

fof(f46,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f108,plain,(
    k7_setfam_1(sK0,sK1) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f45,f106])).

fof(f45,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f424,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f409,f389])).

fof(f389,plain,(
    r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f385,f256])).

fof(f256,plain,(
    ! [X0] : m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(forward_demodulation,[],[f253,f251])).

fof(f251,plain,(
    ! [X1] : k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f248,f158])).

fof(f158,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f154,f47])).

fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f154,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f61,f113])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f248,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
      | k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0))) ) ),
    inference(resolution,[],[f239,f63])).

fof(f239,plain,(
    ! [X1] :
      ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))
      | ~ r2_hidden(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f114,f110])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f106])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f253,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(resolution,[],[f250,f64])).

fof(f250,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(subsumption_resolution,[],[f247,f158])).

fof(f247,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
      | m1_subset_1(k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f239,f64])).

fof(f385,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f379,f306])).

fof(f306,plain,(
    r1_tarski(sK1,k7_setfam_1(sK0,k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f302,f220])).

fof(f220,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f119,f109])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f106])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f302,plain,(
    ! [X0] : r2_hidden(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f301,f256])).

fof(f301,plain,(
    ! [X64,X65] :
      ( ~ m1_subset_1(k1_zfmisc_1(X65),k1_zfmisc_1(k1_zfmisc_1(X64)))
      | r2_hidden(X64,k7_setfam_1(X64,k1_zfmisc_1(X65))) ) ),
    inference(resolution,[],[f286,f158])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_xboole_0,X1)
      | r2_hidden(X0,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(subsumption_resolution,[],[f283,f113])).

fof(f283,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ r2_hidden(k1_xboole_0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f66,f111])).

fof(f111,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f49,f107])).

fof(f107,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f379,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r1_tarski(k7_setfam_1(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f373,f173])).

fof(f173,plain,(
    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f373,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r1_tarski(k7_setfam_1(sK0,sK1),X0) ) ),
    inference(superposition,[],[f68,f169])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f409,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(k1_xboole_0) = X1
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f117,f110])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f69,f106,f106])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f169,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f63,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (15428)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.46  % (15412)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (15407)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (15433)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (15409)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (15410)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (15416)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (15409)Refutation not found, incomplete strategy% (15409)------------------------------
% 0.21/0.51  % (15409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15409)Memory used [KB]: 6396
% 0.21/0.51  % (15409)Time elapsed: 0.112 s
% 0.21/0.51  % (15409)------------------------------
% 0.21/0.51  % (15409)------------------------------
% 0.21/0.52  % (15419)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (15427)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (15425)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.53  % (15405)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.53  % (15417)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.53  % (15405)Refutation not found, incomplete strategy% (15405)------------------------------
% 1.34/0.53  % (15405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (15405)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (15405)Memory used [KB]: 1663
% 1.34/0.53  % (15405)Time elapsed: 0.126 s
% 1.34/0.53  % (15405)------------------------------
% 1.34/0.53  % (15405)------------------------------
% 1.34/0.53  % (15415)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.53  % (15406)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.53  % (15418)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.53  % (15408)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.53  % (15434)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.53  % (15411)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.53  % (15421)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.53  % (15413)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.54  % (15420)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.54  % (15431)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  % (15429)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (15426)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.54  % (15423)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.55  % (15411)Refutation found. Thanks to Tanya!
% 1.50/0.55  % SZS status Theorem for theBenchmark
% 1.50/0.55  % SZS output start Proof for theBenchmark
% 1.50/0.55  fof(f444,plain,(
% 1.50/0.55    $false),
% 1.50/0.55    inference(subsumption_resolution,[],[f443,f168])).
% 1.50/0.55  % (15422)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (15432)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.55  % (15422)Refutation not found, incomplete strategy% (15422)------------------------------
% 1.50/0.55  % (15422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (15422)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (15422)Memory used [KB]: 10618
% 1.50/0.55  % (15422)Time elapsed: 0.150 s
% 1.50/0.55  % (15422)------------------------------
% 1.50/0.55  % (15422)------------------------------
% 1.50/0.55  % (15414)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.55  % (15415)Refutation not found, incomplete strategy% (15415)------------------------------
% 1.50/0.55  % (15415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (15415)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (15415)Memory used [KB]: 10618
% 1.50/0.55  % (15415)Time elapsed: 0.152 s
% 1.50/0.55  % (15415)------------------------------
% 1.50/0.55  % (15415)------------------------------
% 1.50/0.55  % (15414)Refutation not found, incomplete strategy% (15414)------------------------------
% 1.50/0.55  % (15414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (15414)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (15414)Memory used [KB]: 10618
% 1.50/0.55  % (15414)Time elapsed: 0.149 s
% 1.50/0.55  % (15414)------------------------------
% 1.50/0.55  % (15414)------------------------------
% 1.50/0.55  % (15424)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.55  % (15430)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.57  fof(f168,plain,(
% 1.50/0.57    k1_xboole_0 != sK1),
% 1.50/0.57    inference(superposition,[],[f144,f109])).
% 1.50/0.57  fof(f109,plain,(
% 1.50/0.57    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.50/0.57    inference(definition_unfolding,[],[f44,f106])).
% 1.50/0.57  fof(f106,plain,(
% 1.50/0.57    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f53,f103])).
% 1.50/0.57  fof(f103,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f56,f102])).
% 1.50/0.57  fof(f102,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f76,f101])).
% 1.50/0.57  fof(f101,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f77,f100])).
% 1.50/0.57  fof(f100,plain,(
% 1.50/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f78,f99])).
% 1.50/0.57  fof(f99,plain,(
% 1.50/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f79,f80])).
% 1.50/0.57  fof(f80,plain,(
% 1.50/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.50/0.57  fof(f79,plain,(
% 1.50/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.50/0.57  fof(f78,plain,(
% 1.50/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.57  fof(f77,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f6])).
% 1.50/0.57  fof(f6,axiom,(
% 1.50/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.57  fof(f76,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f5])).
% 1.50/0.57  fof(f5,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f4])).
% 1.50/0.57  fof(f4,axiom,(
% 1.50/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.57  fof(f53,plain,(
% 1.50/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.57  fof(f44,plain,(
% 1.50/0.57    sK1 = k1_tarski(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f32])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(flattening,[],[f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ? [X0,X1] : ((k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(ennf_transformation,[],[f30])).
% 1.50/0.57  fof(f30,negated_conjecture,(
% 1.50/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 1.50/0.57    inference(negated_conjecture,[],[f29])).
% 1.50/0.57  fof(f29,conjecture,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_setfam_1)).
% 1.50/0.57  fof(f144,plain,(
% 1.50/0.57    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 1.50/0.57    inference(forward_demodulation,[],[f143,f51])).
% 1.50/0.57  fof(f51,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.50/0.57  fof(f143,plain,(
% 1.50/0.57    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.50/0.57    inference(forward_demodulation,[],[f124,f112])).
% 1.50/0.57  fof(f112,plain,(
% 1.50/0.57    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.50/0.57    inference(definition_unfolding,[],[f50,f106])).
% 1.50/0.57  fof(f50,plain,(
% 1.50/0.57    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f24,axiom,(
% 1.50/0.57    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.50/0.57  fof(f124,plain,(
% 1.50/0.57    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.50/0.57    inference(equality_resolution,[],[f120])).
% 1.50/0.57  fof(f120,plain,(
% 1.50/0.57    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f75,f106,f105,f106,f106])).
% 1.50/0.57  fof(f105,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f57,f104])).
% 1.50/0.57  fof(f104,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f55,f103])).
% 1.50/0.57  fof(f55,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f25])).
% 1.50/0.57  fof(f25,axiom,(
% 1.50/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.50/0.57  fof(f57,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.50/0.57  fof(f75,plain,(
% 1.50/0.57    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f12])).
% 1.50/0.57  fof(f12,axiom,(
% 1.50/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.50/0.57  fof(f443,plain,(
% 1.50/0.57    k1_xboole_0 = sK1),
% 1.50/0.57    inference(forward_demodulation,[],[f428,f212])).
% 1.50/0.57  fof(f212,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0)) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f211,f174])).
% 1.50/0.57  fof(f174,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(resolution,[],[f64,f113])).
% 1.50/0.57  fof(f113,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f52,f48])).
% 1.50/0.57  fof(f48,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f15])).
% 1.50/0.57  fof(f15,axiom,(
% 1.50/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.50/0.57  fof(f52,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f18,axiom,(
% 1.50/0.57    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.50/0.57  fof(f64,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f36])).
% 1.50/0.57  fof(f36,plain,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(ennf_transformation,[],[f22])).
% 1.50/0.57  fof(f22,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 1.50/0.57  fof(f211,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0) | ~m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(trivial_inequality_removal,[],[f210])).
% 1.50/0.57  fof(f210,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0) | ~m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(superposition,[],[f65,f170])).
% 1.50/0.57  fof(f170,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 = k7_setfam_1(X0,k7_setfam_1(X0,k1_xboole_0))) )),
% 1.50/0.57    inference(resolution,[],[f63,f113])).
% 1.50/0.57  fof(f63,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f35])).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(ennf_transformation,[],[f23])).
% 1.50/0.57  fof(f23,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 1.50/0.57  fof(f65,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f38])).
% 1.50/0.57  fof(f38,plain,(
% 1.50/0.57    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(flattening,[],[f37])).
% 1.50/0.57  fof(f37,plain,(
% 1.50/0.57    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(ennf_transformation,[],[f26])).
% 1.50/0.57  fof(f26,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 1.50/0.57  fof(f428,plain,(
% 1.50/0.57    sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 1.50/0.57    inference(backward_demodulation,[],[f169,f426])).
% 1.50/0.57  fof(f426,plain,(
% 1.50/0.57    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 1.50/0.57    inference(subsumption_resolution,[],[f424,f142])).
% 1.50/0.57  fof(f142,plain,(
% 1.50/0.57    k1_zfmisc_1(k1_xboole_0) != k7_setfam_1(sK0,sK1)),
% 1.50/0.57    inference(backward_demodulation,[],[f108,f110])).
% 1.50/0.57  fof(f110,plain,(
% 1.50/0.57    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(definition_unfolding,[],[f46,f106])).
% 1.50/0.57  fof(f46,plain,(
% 1.50/0.57    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.50/0.57    inference(cnf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,axiom,(
% 1.50/0.57    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.50/0.57  fof(f108,plain,(
% 1.50/0.57    k7_setfam_1(sK0,sK1) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(definition_unfolding,[],[f45,f106])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)),
% 1.50/0.57    inference(cnf_transformation,[],[f32])).
% 1.50/0.57  fof(f424,plain,(
% 1.50/0.57    k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1) | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 1.50/0.57    inference(resolution,[],[f409,f389])).
% 1.50/0.57  fof(f389,plain,(
% 1.50/0.57    r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 1.50/0.57    inference(subsumption_resolution,[],[f385,f256])).
% 1.50/0.57  fof(f256,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(forward_demodulation,[],[f253,f251])).
% 1.50/0.57  fof(f251,plain,(
% 1.50/0.57    ( ! [X1] : (k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)))) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f248,f158])).
% 1.50/0.57  fof(f158,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f154,f47])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f19])).
% 1.50/0.57  fof(f19,axiom,(
% 1.50/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.50/0.57  fof(f154,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(resolution,[],[f61,f113])).
% 1.50/0.57  fof(f61,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f33])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f14])).
% 1.50/0.57  fof(f14,axiom,(
% 1.50/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.50/0.57  fof(f248,plain,(
% 1.50/0.57    ( ! [X1] : (~r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) | k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)))) )),
% 1.50/0.57    inference(resolution,[],[f239,f63])).
% 1.50/0.57  fof(f239,plain,(
% 1.50/0.57    ( ! [X1] : (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1)) | ~r2_hidden(k1_xboole_0,X1)) )),
% 1.50/0.57    inference(superposition,[],[f114,f110])).
% 1.50/0.57  fof(f114,plain,(
% 1.50/0.57    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f62,f106])).
% 1.50/0.57  fof(f62,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f34])).
% 1.50/0.57  fof(f34,plain,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.50/0.57    inference(ennf_transformation,[],[f21])).
% 1.50/0.57  fof(f21,axiom,(
% 1.50/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.50/0.57  fof(f253,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k7_setfam_1(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(resolution,[],[f250,f64])).
% 1.50/0.57  fof(f250,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f247,f158])).
% 1.50/0.57  fof(f247,plain,(
% 1.50/0.57    ( ! [X0] : (~r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) | m1_subset_1(k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(resolution,[],[f239,f64])).
% 1.50/0.57  fof(f385,plain,(
% 1.50/0.57    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 1.50/0.57    inference(resolution,[],[f379,f306])).
% 1.50/0.57  fof(f306,plain,(
% 1.50/0.57    r1_tarski(sK1,k7_setfam_1(sK0,k1_zfmisc_1(k1_xboole_0)))),
% 1.50/0.57    inference(resolution,[],[f302,f220])).
% 1.50/0.57  fof(f220,plain,(
% 1.50/0.57    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0)) )),
% 1.50/0.57    inference(superposition,[],[f119,f109])).
% 1.50/0.57  fof(f119,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f72,f106])).
% 1.50/0.57  fof(f72,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,axiom,(
% 1.50/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.50/0.57  fof(f302,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)))) )),
% 1.50/0.57    inference(resolution,[],[f301,f256])).
% 1.50/0.57  fof(f301,plain,(
% 1.50/0.57    ( ! [X64,X65] : (~m1_subset_1(k1_zfmisc_1(X65),k1_zfmisc_1(k1_zfmisc_1(X64))) | r2_hidden(X64,k7_setfam_1(X64,k1_zfmisc_1(X65)))) )),
% 1.50/0.57    inference(resolution,[],[f286,f158])).
% 1.50/0.57  fof(f286,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r2_hidden(k1_xboole_0,X1) | r2_hidden(X0,k7_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f283,f113])).
% 1.50/0.57  fof(f283,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r2_hidden(X0,k7_setfam_1(X0,X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~r2_hidden(k1_xboole_0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(superposition,[],[f66,f111])).
% 1.50/0.57  fof(f111,plain,(
% 1.50/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.50/0.57    inference(definition_unfolding,[],[f49,f107])).
% 1.50/0.57  fof(f107,plain,(
% 1.50/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f54,f48])).
% 1.50/0.57  fof(f54,plain,(
% 1.50/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f20])).
% 1.50/0.57  fof(f20,axiom,(
% 1.50/0.57    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.50/0.57  fof(f49,plain,(
% 1.50/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f16])).
% 1.50/0.57  fof(f16,axiom,(
% 1.50/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.50/0.57  fof(f66,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f39])).
% 1.50/0.57  fof(f39,plain,(
% 1.50/0.57    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(ennf_transformation,[],[f27])).
% 1.50/0.57  fof(f27,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).
% 1.50/0.57  fof(f379,plain,(
% 1.50/0.57    ( ! [X0] : (~r1_tarski(sK1,k7_setfam_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(k7_setfam_1(sK0,sK1),X0)) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f373,f173])).
% 1.50/0.57  fof(f173,plain,(
% 1.50/0.57    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.50/0.57    inference(resolution,[],[f64,f43])).
% 1.50/0.57  fof(f43,plain,(
% 1.50/0.57    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.50/0.57    inference(cnf_transformation,[],[f32])).
% 1.50/0.57  fof(f373,plain,(
% 1.50/0.57    ( ! [X0] : (~r1_tarski(sK1,k7_setfam_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(k7_setfam_1(sK0,sK1),X0)) )),
% 1.50/0.57    inference(superposition,[],[f68,f169])).
% 1.50/0.57  fof(f68,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r1_tarski(X1,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f41])).
% 1.50/0.57  fof(f41,plain,(
% 1.50/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(flattening,[],[f40])).
% 1.50/0.57  fof(f40,plain,(
% 1.50/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.50/0.57    inference(ennf_transformation,[],[f28])).
% 1.50/0.57  fof(f28,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).
% 1.50/0.57  fof(f409,plain,(
% 1.50/0.57    ( ! [X1] : (~r1_tarski(X1,k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0) = X1 | k1_xboole_0 = X1) )),
% 1.50/0.57    inference(superposition,[],[f117,f110])).
% 1.50/0.57  fof(f117,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.50/0.57    inference(definition_unfolding,[],[f69,f106,f106])).
% 1.50/0.57  fof(f69,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f13])).
% 1.50/0.57  fof(f13,axiom,(
% 1.50/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 1.50/0.57  fof(f169,plain,(
% 1.50/0.57    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 1.50/0.57    inference(resolution,[],[f63,f43])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (15411)------------------------------
% 1.50/0.57  % (15411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (15411)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (15411)Memory used [KB]: 6524
% 1.50/0.57  % (15411)Time elapsed: 0.119 s
% 1.50/0.57  % (15411)------------------------------
% 1.50/0.57  % (15411)------------------------------
% 1.50/0.57  % (15404)Success in time 0.212 s
%------------------------------------------------------------------------------
