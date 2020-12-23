%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 682 expanded)
%              Number of leaves         :   28 ( 212 expanded)
%              Depth                    :   23
%              Number of atoms          :  218 ( 892 expanded)
%              Number of equality atoms :   98 ( 583 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(subsumption_resolution,[],[f409,f165])).

fof(f165,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f143,f108])).

fof(f108,plain,(
    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f46,f105])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f102])).

fof(f102,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

% (30702)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

fof(f143,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f142,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f142,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f123,f112])).

fof(f112,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f103])).

fof(f103,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f102])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f123,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f74,f105,f104,f105,f105])).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f103])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f409,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f393,f195])).

fof(f195,plain,(
    ! [X0] : k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f194,f169])).

fof(f169,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(resolution,[],[f63,f111])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f194,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0)
      | ~ m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0)
      | ~ m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f64,f167])).

fof(f167,plain,(
    ! [X0] : k1_xboole_0 = k7_setfam_1(X0,k7_setfam_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f62,f111])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f393,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f166,f391])).

fof(f391,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f389,f141])).

fof(f141,plain,(
    k1_zfmisc_1(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f107,f109])).

fof(f109,plain,(
    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f48,f105])).

fof(f48,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f107,plain,(
    k7_setfam_1(sK0,sK1) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f47,f105])).

fof(f47,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f389,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f372,f346])).

fof(f346,plain,(
    r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f342,f241])).

fof(f241,plain,(
    ! [X0] : m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(forward_demodulation,[],[f238,f236])).

% (30718)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (30724)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f236,plain,(
    ! [X1] : k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f233,f155])).

fof(f155,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f153,f49])).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f153,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f61,f111])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f233,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
      | k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0))) ) ),
    inference(resolution,[],[f226,f62])).

fof(f226,plain,(
    ! [X1] :
      ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))
      | ~ r2_hidden(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f113,f109])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f105])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f238,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(resolution,[],[f235,f63])).

fof(f235,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(subsumption_resolution,[],[f232,f155])).

fof(f232,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
      | m1_subset_1(k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f226,f63])).

fof(f342,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f336,f277])).

fof(f277,plain,(
    r1_tarski(sK1,k7_setfam_1(sK0,k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f274,f203])).

fof(f203,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f118,f108])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f105])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f274,plain,(
    ! [X3] : r2_hidden(X3,k7_setfam_1(X3,k1_zfmisc_1(k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f267,f155])).

fof(f267,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | r2_hidden(X3,k7_setfam_1(X3,k1_zfmisc_1(k1_xboole_0))) ) ),
    inference(resolution,[],[f258,f241])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(k1_xboole_0,X1)
      | r2_hidden(X0,k7_setfam_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f254,f111])).

fof(f254,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ r2_hidden(k1_xboole_0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f65,f110])).

fof(f110,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f51,f106])).

fof(f106,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f336,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r1_tarski(k7_setfam_1(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f330,f168])).

fof(f168,plain,(
    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f330,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r1_tarski(k7_setfam_1(sK0,sK1),X0) ) ),
    inference(superposition,[],[f67,f166])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f372,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(k1_xboole_0) = X1
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f116,f109])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f68,f105,f105])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f166,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f62,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:55:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (30719)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.50  % (30712)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (30723)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (30715)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (30704)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (30707)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (30731)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (30711)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (30711)Refutation not found, incomplete strategy% (30711)------------------------------
% 0.22/0.52  % (30711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30711)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30711)Memory used [KB]: 10618
% 0.22/0.52  % (30711)Time elapsed: 0.117 s
% 0.22/0.52  % (30711)------------------------------
% 0.22/0.52  % (30711)------------------------------
% 0.22/0.52  % (30710)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (30722)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (30727)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (30714)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (30707)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f410,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f409,f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(superposition,[],[f143,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.53    inference(definition_unfolding,[],[f46,f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f54,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f58,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f75,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f76,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f77,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f78,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  % (30702)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    sK1 = k1_tarski(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X0,X1] : ((k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f29])).
% 0.22/0.53  fof(f29,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f142,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f123,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f56,f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f57,f102])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.53    inference(rectify,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 0.22/0.53    inference(equality_resolution,[],[f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f74,f105,f104,f105,f105])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f59,f103])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.53  fof(f409,plain,(
% 0.22/0.53    k1_xboole_0 = sK1),
% 0.22/0.53    inference(forward_demodulation,[],[f393,f195])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f194,f169])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(resolution,[],[f63,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f53,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0) | ~m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f193])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0) | ~m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(superposition,[],[f64,f167])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k7_setfam_1(X0,k7_setfam_1(X0,k1_xboole_0))) )),
% 0.22/0.53    inference(resolution,[],[f62,f111])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.22/0.53  fof(f393,plain,(
% 0.22/0.53    sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.53    inference(backward_demodulation,[],[f166,f391])).
% 0.22/0.53  fof(f391,plain,(
% 0.22/0.53    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f389,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    k1_zfmisc_1(k1_xboole_0) != k7_setfam_1(sK0,sK1)),
% 0.22/0.53    inference(backward_demodulation,[],[f107,f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    inference(definition_unfolding,[],[f48,f105])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    k7_setfam_1(sK0,sK1) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    inference(definition_unfolding,[],[f47,f105])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1) | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.53    inference(resolution,[],[f372,f346])).
% 0.22/0.53  fof(f346,plain,(
% 0.22/0.53    r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f342,f241])).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f238,f236])).
% 0.22/0.53  % (30718)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (30724)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ( ! [X1] : (k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f233,f155])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f153,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,axiom,(
% 0.22/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(resolution,[],[f61,f111])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) | k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)))) )),
% 0.22/0.53    inference(resolution,[],[f226,f62])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    ( ! [X1] : (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1)) | ~r2_hidden(k1_xboole_0,X1)) )),
% 0.22/0.53    inference(superposition,[],[f113,f109])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f60,f105])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k7_setfam_1(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(resolution,[],[f235,f63])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f232,f155])).
% 0.22/0.53  fof(f232,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) | m1_subset_1(k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(resolution,[],[f226,f63])).
% 0.22/0.53  fof(f342,plain,(
% 0.22/0.53    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    inference(resolution,[],[f336,f277])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    r1_tarski(sK1,k7_setfam_1(sK0,k1_zfmisc_1(k1_xboole_0)))),
% 0.22/0.53    inference(resolution,[],[f274,f203])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0)) )),
% 0.22/0.53    inference(superposition,[],[f118,f108])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f71,f105])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(X3,k7_setfam_1(X3,k1_zfmisc_1(k1_xboole_0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f267,f155])).
% 0.22/0.53  fof(f267,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(X3,k7_setfam_1(X3,k1_zfmisc_1(k1_xboole_0)))) )),
% 0.22/0.53    inference(resolution,[],[f258,f241])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(k1_xboole_0,X1) | r2_hidden(X0,k7_setfam_1(X0,X1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f254,f111])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,k7_setfam_1(X0,X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~r2_hidden(k1_xboole_0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(superposition,[],[f65,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f51,f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f55,f50])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.22/0.53  fof(f336,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK1,k7_setfam_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(k7_setfam_1(sK0,sK1),X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f330,f168])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(resolution,[],[f63,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK1,k7_setfam_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(k7_setfam_1(sK0,sK1),X0)) )),
% 0.22/0.53    inference(superposition,[],[f67,f166])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r1_tarski(X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_tarski(X1,k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0) = X1 | k1_xboole_0 = X1) )),
% 0.22/0.53    inference(superposition,[],[f116,f109])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f68,f105,f105])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f62,f45])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (30707)------------------------------
% 0.22/0.53  % (30707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30707)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (30707)Memory used [KB]: 6524
% 0.22/0.53  % (30707)Time elapsed: 0.079 s
% 0.22/0.53  % (30707)------------------------------
% 0.22/0.53  % (30707)------------------------------
% 0.22/0.54  % (30706)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (30701)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (30701)Refutation not found, incomplete strategy% (30701)------------------------------
% 0.22/0.54  % (30701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30701)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30701)Memory used [KB]: 1663
% 0.22/0.54  % (30701)Time elapsed: 0.126 s
% 0.22/0.54  % (30701)------------------------------
% 0.22/0.54  % (30701)------------------------------
% 0.22/0.54  % (30705)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (30696)Success in time 0.177 s
%------------------------------------------------------------------------------
