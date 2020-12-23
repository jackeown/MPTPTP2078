%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 908 expanded)
%              Number of leaves         :   16 ( 267 expanded)
%              Depth                    :   27
%              Number of atoms          :  158 (1607 expanded)
%              Number of equality atoms :   47 ( 713 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(subsumption_resolution,[],[f241,f228])).

% (2828)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f228,plain,(
    k1_xboole_0 != sK1 ),
    inference(resolution,[],[f226,f23])).

fof(f23,plain,
    ( ~ v3_relat_1(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

fof(f226,plain,(
    v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f224,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f224,plain,
    ( ~ v1_relat_1(sK0)
    | v3_relat_1(sK0) ),
    inference(resolution,[],[f223,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))
      | ~ v1_relat_1(X0)
      | v3_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f56,f53])).

fof(f53,plain,(
    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f26,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | v3_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f31,f52])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | v3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

fof(f223,plain,(
    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f221,f112])).

fof(f112,plain,(
    ! [X2] : r2_hidden(X2,k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f58,f94])).

fof(f94,plain,(
    ! [X0] : r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f29,f54])).

fof(f54,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f52])).

fof(f28,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f29,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f221,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f40,f220])).

fof(f220,plain,(
    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f218,f82])).

fof(f82,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f80,f23])).

fof(f80,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f79,f25])).

fof(f79,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | v3_relat_1(sK0) ),
    inference(resolution,[],[f66,f63])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK0),X0)
      | k1_xboole_0 = sK2(k2_relat_1(sK0),X0)
      | v3_relat_1(sK0) ) ),
    inference(resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | k1_xboole_0 = X1
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f218,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f216,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f216,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f205,f65])).

fof(f65,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X3))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f42,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f205,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f86,f84])).

fof(f84,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f83,f25])).

fof(f83,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f80,f62])).

% (2826)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f62,plain,(
    ! [X0] :
      ( ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f55,f53])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v3_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r2_hidden(sK1,X0)
      | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f81,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f80,f22])).

fof(f22,plain,
    ( ~ v3_relat_1(sK0)
    | r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f241,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f239,f70])).

fof(f239,plain,(
    r1_tarski(sK1,k1_xboole_0) ),
    inference(resolution,[],[f237,f65])).

fof(f237,plain,(
    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f231,f223])).

fof(f231,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f227,f38])).

fof(f227,plain,(
    r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(resolution,[],[f226,f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:56:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (2824)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (2821)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (2820)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (2840)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (2832)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (2841)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (2833)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (2834)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (2825)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (2823)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (2840)Refutation not found, incomplete strategy% (2840)------------------------------
% 0.20/0.53  % (2840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2841)Refutation not found, incomplete strategy% (2841)------------------------------
% 0.20/0.53  % (2841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2841)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2841)Memory used [KB]: 10618
% 0.20/0.53  % (2841)Time elapsed: 0.082 s
% 0.20/0.53  % (2841)------------------------------
% 0.20/0.53  % (2841)------------------------------
% 0.20/0.54  % (2842)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (2840)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2840)Memory used [KB]: 1663
% 0.20/0.54  % (2840)Time elapsed: 0.121 s
% 0.20/0.54  % (2840)------------------------------
% 0.20/0.54  % (2840)------------------------------
% 0.20/0.54  % (2839)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (2819)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (2822)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (2831)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (2848)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (2825)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (2845)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (2843)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (2846)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (2829)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (2836)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (2836)Refutation not found, incomplete strategy% (2836)------------------------------
% 0.20/0.55  % (2836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (2835)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.55  % (2844)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f243,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(subsumption_resolution,[],[f241,f228])).
% 1.47/0.55  % (2828)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.55  fof(f228,plain,(
% 1.47/0.55    k1_xboole_0 != sK1),
% 1.47/0.55    inference(resolution,[],[f226,f23])).
% 1.47/0.55  fof(f23,plain,(
% 1.47/0.55    ~v3_relat_1(sK0) | k1_xboole_0 != sK1),
% 1.47/0.55    inference(cnf_transformation,[],[f18])).
% 1.47/0.55  fof(f18,plain,(
% 1.47/0.55    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f17])).
% 1.47/0.55  fof(f17,negated_conjecture,(
% 1.47/0.55    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 1.47/0.55    inference(negated_conjecture,[],[f16])).
% 1.47/0.55  fof(f16,conjecture,(
% 1.47/0.55    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).
% 1.47/0.55  fof(f226,plain,(
% 1.47/0.55    v3_relat_1(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f224,f25])).
% 1.47/0.55  fof(f25,plain,(
% 1.47/0.55    v1_relat_1(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f18])).
% 1.47/0.55  fof(f224,plain,(
% 1.47/0.55    ~v1_relat_1(sK0) | v3_relat_1(sK0)),
% 1.47/0.55    inference(resolution,[],[f223,f63])).
% 1.47/0.55  fof(f63,plain,(
% 1.47/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(X0) | v3_relat_1(X0)) )),
% 1.47/0.55    inference(forward_demodulation,[],[f56,f53])).
% 1.47/0.55  fof(f53,plain,(
% 1.47/0.55    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.47/0.55    inference(definition_unfolding,[],[f26,f52])).
% 1.47/0.55  fof(f52,plain,(
% 1.47/0.55    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f30,f51])).
% 1.47/0.55  fof(f51,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f33,f50])).
% 1.47/0.55  fof(f50,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f43,f49])).
% 1.47/0.55  fof(f49,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f47,f48])).
% 1.47/0.55  fof(f48,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f8])).
% 1.47/0.55  fof(f8,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.47/0.55  fof(f47,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f7])).
% 1.47/0.55  fof(f7,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.47/0.55  fof(f43,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f6])).
% 1.47/0.55  fof(f6,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.55  fof(f33,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f5])).
% 1.47/0.55  fof(f5,axiom,(
% 1.47/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.55  fof(f30,plain,(
% 1.47/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f4])).
% 1.47/0.55  fof(f4,axiom,(
% 1.47/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.55  fof(f26,plain,(
% 1.47/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.47/0.55    inference(cnf_transformation,[],[f10])).
% 1.47/0.55  fof(f10,axiom,(
% 1.47/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.47/0.55  fof(f56,plain,(
% 1.47/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | v3_relat_1(X0)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f31,f52])).
% 1.47/0.55  fof(f31,plain,(
% 1.47/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | v3_relat_1(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f19])).
% 1.47/0.55  fof(f19,plain,(
% 1.47/0.55    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f15])).
% 1.47/0.55  fof(f15,axiom,(
% 1.47/0.55    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).
% 1.47/0.55  fof(f223,plain,(
% 1.47/0.55    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(subsumption_resolution,[],[f221,f112])).
% 1.47/0.55  fof(f112,plain,(
% 1.47/0.55    ( ! [X2] : (r2_hidden(X2,k1_zfmisc_1(X2))) )),
% 1.47/0.55    inference(resolution,[],[f58,f94])).
% 1.47/0.55  fof(f94,plain,(
% 1.47/0.55    ( ! [X0] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0))) )),
% 1.47/0.55    inference(superposition,[],[f29,f54])).
% 1.47/0.55  fof(f54,plain,(
% 1.47/0.55    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.47/0.55    inference(definition_unfolding,[],[f28,f52])).
% 1.47/0.55  fof(f28,plain,(
% 1.47/0.55    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.47/0.55    inference(cnf_transformation,[],[f11])).
% 1.47/0.55  fof(f11,axiom,(
% 1.47/0.55    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.47/0.55  fof(f29,plain,(
% 1.47/0.55    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 1.47/0.55    inference(cnf_transformation,[],[f9])).
% 1.47/0.55  fof(f9,axiom,(
% 1.47/0.55    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 1.47/0.55  fof(f58,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f45,f51])).
% 1.47/0.55  fof(f45,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f12])).
% 1.47/0.55  fof(f12,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.47/0.55  fof(f221,plain,(
% 1.47/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(superposition,[],[f40,f220])).
% 1.47/0.55  fof(f220,plain,(
% 1.47/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(subsumption_resolution,[],[f218,f82])).
% 1.47/0.55  fof(f82,plain,(
% 1.47/0.55    k1_xboole_0 != sK1 | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(resolution,[],[f80,f23])).
% 1.47/0.55  fof(f80,plain,(
% 1.47/0.55    v3_relat_1(sK0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(subsumption_resolution,[],[f79,f25])).
% 1.47/0.55  fof(f79,plain,(
% 1.47/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 1.47/0.55    inference(duplicate_literal_removal,[],[f76])).
% 1.47/0.55  fof(f76,plain,(
% 1.47/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(sK0) | ~v1_relat_1(sK0) | v3_relat_1(sK0)),
% 1.47/0.55    inference(resolution,[],[f66,f63])).
% 1.47/0.55  fof(f66,plain,(
% 1.47/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),X0) | k1_xboole_0 = sK2(k2_relat_1(sK0),X0) | v3_relat_1(sK0)) )),
% 1.47/0.55    inference(resolution,[],[f39,f24])).
% 1.47/0.55  fof(f24,plain,(
% 1.47/0.55    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1 | v3_relat_1(sK0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f18])).
% 1.47/0.55  fof(f39,plain,(
% 1.47/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f21])).
% 1.47/0.55  fof(f21,plain,(
% 1.47/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f1])).
% 1.47/0.55  fof(f1,axiom,(
% 1.47/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.55  fof(f218,plain,(
% 1.47/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 1.47/0.55    inference(resolution,[],[f216,f70])).
% 1.47/0.55  fof(f70,plain,(
% 1.47/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.47/0.55    inference(resolution,[],[f37,f27])).
% 1.47/0.55  fof(f27,plain,(
% 1.47/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f3])).
% 1.47/0.55  fof(f3,axiom,(
% 1.47/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.47/0.55  fof(f37,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.47/0.55    inference(cnf_transformation,[],[f2])).
% 1.47/0.55  fof(f2,axiom,(
% 1.47/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.55  fof(f216,plain,(
% 1.47/0.55    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(resolution,[],[f205,f65])).
% 1.47/0.55  fof(f65,plain,(
% 1.47/0.55    ( ! [X2,X3] : (~r2_hidden(X2,k1_zfmisc_1(X3)) | r1_tarski(X2,X3)) )),
% 1.47/0.55    inference(resolution,[],[f42,f34])).
% 1.47/0.55  fof(f34,plain,(
% 1.47/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f20])).
% 1.47/0.55  fof(f20,plain,(
% 1.47/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.47/0.55    inference(ennf_transformation,[],[f13])).
% 1.47/0.55  fof(f13,axiom,(
% 1.47/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.47/0.55  fof(f42,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f14])).
% 1.47/0.55  fof(f14,axiom,(
% 1.47/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.55  fof(f205,plain,(
% 1.47/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(duplicate_literal_removal,[],[f200])).
% 1.47/0.55  fof(f200,plain,(
% 1.47/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(resolution,[],[f86,f84])).
% 1.47/0.55  fof(f84,plain,(
% 1.47/0.55    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(subsumption_resolution,[],[f83,f25])).
% 1.47/0.55  fof(f83,plain,(
% 1.47/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(sK0) | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(resolution,[],[f80,f62])).
% 1.47/0.55  % (2826)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.55  fof(f62,plain,(
% 1.47/0.55    ( ! [X0] : (~v3_relat_1(X0) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))) )),
% 1.47/0.55    inference(forward_demodulation,[],[f55,f53])).
% 1.47/0.55  fof(f55,plain,(
% 1.47/0.55    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v3_relat_1(X0)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f32,f52])).
% 1.47/0.55  fof(f32,plain,(
% 1.47/0.55    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f19])).
% 1.47/0.55  fof(f86,plain,(
% 1.47/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))) )),
% 1.47/0.55    inference(resolution,[],[f81,f38])).
% 1.47/0.55  fof(f38,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f21])).
% 1.47/0.55  fof(f81,plain,(
% 1.47/0.55    r2_hidden(sK1,k2_relat_1(sK0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(resolution,[],[f80,f22])).
% 1.47/0.55  fof(f22,plain,(
% 1.47/0.55    ~v3_relat_1(sK0) | r2_hidden(sK1,k2_relat_1(sK0))),
% 1.47/0.55    inference(cnf_transformation,[],[f18])).
% 1.47/0.55  fof(f40,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f21])).
% 1.47/0.55  fof(f241,plain,(
% 1.47/0.55    k1_xboole_0 = sK1),
% 1.47/0.55    inference(resolution,[],[f239,f70])).
% 1.47/0.55  fof(f239,plain,(
% 1.47/0.55    r1_tarski(sK1,k1_xboole_0)),
% 1.47/0.55    inference(resolution,[],[f237,f65])).
% 1.47/0.55  fof(f237,plain,(
% 1.47/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.55    inference(resolution,[],[f231,f223])).
% 1.47/0.55  fof(f231,plain,(
% 1.47/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r2_hidden(sK1,X0)) )),
% 1.47/0.55    inference(resolution,[],[f227,f38])).
% 1.47/0.55  fof(f227,plain,(
% 1.47/0.55    r2_hidden(sK1,k2_relat_1(sK0))),
% 1.47/0.55    inference(resolution,[],[f226,f22])).
% 1.47/0.55  % SZS output end Proof for theBenchmark
% 1.47/0.55  % (2825)------------------------------
% 1.47/0.55  % (2825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (2825)Termination reason: Refutation
% 1.47/0.55  
% 1.47/0.55  % (2825)Memory used [KB]: 6396
% 1.47/0.55  % (2825)Time elapsed: 0.094 s
% 1.47/0.55  % (2825)------------------------------
% 1.47/0.55  % (2825)------------------------------
% 1.47/0.55  % (2818)Success in time 0.189 s
%------------------------------------------------------------------------------
