%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:00 EST 2020

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 159 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 286 expanded)
%              Number of equality atoms :   43 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f892,plain,(
    $false ),
    inference(subsumption_resolution,[],[f886,f38])).

fof(f38,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f886,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    inference(superposition,[],[f363,f874])).

fof(f874,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f814,f868,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f868,plain,(
    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f414,f288])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(X0,k9_relat_1(X1,X0))
      | ~ r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f284,f40])).

fof(f284,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f56,f140])).

fof(f140,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f139,f42])).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f139,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f134,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f134,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f40,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f414,plain,(
    r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2)) ),
    inference(superposition,[],[f163,f397])).

fof(f397,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2) ),
    inference(superposition,[],[f211,f112])).

fof(f112,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f37,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f211,plain,(
    ! [X0,X1] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f199,f41])).

fof(f199,plain,(
    ! [X0,X1] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k2_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(unit_resulting_resolution,[],[f40,f113,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f113,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f65,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f163,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f93,f151])).

fof(f151,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f814,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(forward_demodulation,[],[f809,f542])).

fof(f542,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[],[f362,f140])).

fof(f362,plain,(
    ! [X2,X0,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f316,f151])).

fof(f316,plain,(
    ! [X2,X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) ),
    inference(unit_resulting_resolution,[],[f40,f40,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f809,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0),X0) ),
    inference(superposition,[],[f277,f140])).

fof(f277,plain,(
    ! [X2,X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(unit_resulting_resolution,[],[f68,f163,f40,f56])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(unit_resulting_resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f363,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f315,f150])).

fof(f150,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0) ),
    inference(unit_resulting_resolution,[],[f39,f50])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f315,plain,(
    ! [X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(unit_resulting_resolution,[],[f39,f40,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:53:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (10604)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (10607)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (10602)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (10606)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (10622)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (10603)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (10627)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (10614)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (10623)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (10612)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (10615)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (10616)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (10610)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (10608)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.30/0.54  % (10620)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.30/0.54  % (10605)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.30/0.54  % (10621)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.30/0.54  % (10619)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.30/0.55  % (10611)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.30/0.55  % (10626)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.51/0.56  % (10613)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.51/0.56  % (10618)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.51/0.57  % (10624)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.51/0.58  % (10625)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.51/0.58  % (10617)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.51/0.59  % (10609)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 2.15/0.65  % (10611)Refutation not found, incomplete strategy% (10611)------------------------------
% 2.15/0.65  % (10611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.65  % (10611)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.65  
% 2.15/0.65  % (10611)Memory used [KB]: 6140
% 2.15/0.65  % (10611)Time elapsed: 0.237 s
% 2.15/0.65  % (10611)------------------------------
% 2.15/0.65  % (10611)------------------------------
% 2.44/0.70  % (10609)Refutation found. Thanks to Tanya!
% 2.44/0.70  % SZS status Theorem for theBenchmark
% 2.44/0.70  % SZS output start Proof for theBenchmark
% 2.44/0.70  fof(f892,plain,(
% 2.44/0.70    $false),
% 2.44/0.70    inference(subsumption_resolution,[],[f886,f38])).
% 2.44/0.70  fof(f38,plain,(
% 2.44/0.70    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 2.44/0.70    inference(cnf_transformation,[],[f20])).
% 2.44/0.70  fof(f20,plain,(
% 2.44/0.70    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 2.44/0.70    inference(ennf_transformation,[],[f19])).
% 2.44/0.70  fof(f19,negated_conjecture,(
% 2.44/0.70    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.44/0.70    inference(negated_conjecture,[],[f18])).
% 2.44/0.70  fof(f18,conjecture,(
% 2.44/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.44/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 2.44/0.70  fof(f886,plain,(
% 2.44/0.70    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 2.44/0.70    inference(superposition,[],[f363,f874])).
% 2.44/0.70  fof(f874,plain,(
% 2.44/0.70    sK1 = k9_relat_1(k6_relat_1(sK2),sK1)),
% 2.44/0.70    inference(unit_resulting_resolution,[],[f814,f868,f60])).
% 2.44/0.70  fof(f60,plain,(
% 2.44/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.44/0.70    inference(cnf_transformation,[],[f1])).
% 2.44/0.70  fof(f1,axiom,(
% 2.44/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.44/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.44/0.70  fof(f868,plain,(
% 2.44/0.70    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1))),
% 2.44/0.70    inference(unit_resulting_resolution,[],[f40,f414,f288])).
% 2.44/0.70  fof(f288,plain,(
% 2.44/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(X0,k9_relat_1(X1,X0)) | ~r1_tarski(k6_relat_1(X0),X1)) )),
% 2.44/0.70    inference(subsumption_resolution,[],[f284,f40])).
% 2.44/0.70  fof(f284,plain,(
% 2.44/0.70    ( ! [X0,X1] : (r1_tarski(X0,k9_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.44/0.70    inference(superposition,[],[f56,f140])).
% 2.44/0.70  fof(f140,plain,(
% 2.44/0.70    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.44/0.70    inference(forward_demodulation,[],[f139,f42])).
% 2.44/0.70  fof(f42,plain,(
% 2.44/0.70    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.44/0.70    inference(cnf_transformation,[],[f11])).
% 2.44/0.70  fof(f11,axiom,(
% 2.44/0.70    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.44/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.44/0.70  fof(f139,plain,(
% 2.44/0.70    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 2.44/0.70    inference(forward_demodulation,[],[f134,f41])).
% 2.44/0.70  fof(f41,plain,(
% 2.44/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.44/0.70    inference(cnf_transformation,[],[f11])).
% 2.44/0.70  fof(f134,plain,(
% 2.44/0.70    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 2.44/0.70    inference(unit_resulting_resolution,[],[f40,f44])).
% 2.44/0.70  fof(f44,plain,(
% 2.44/0.70    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.44/0.70    inference(cnf_transformation,[],[f22])).
% 2.44/0.70  fof(f22,plain,(
% 2.44/0.70    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.44/0.70    inference(ennf_transformation,[],[f7])).
% 2.44/0.70  fof(f7,axiom,(
% 2.44/0.70    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.44/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 2.44/0.70  fof(f56,plain,(
% 2.44/0.70    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | ~v1_relat_1(X1)) )),
% 2.44/0.70    inference(cnf_transformation,[],[f33])).
% 2.44/0.70  fof(f33,plain,(
% 2.44/0.70    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.44/0.70    inference(flattening,[],[f32])).
% 2.44/0.70  fof(f32,plain,(
% 2.44/0.70    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.44/0.70    inference(ennf_transformation,[],[f9])).
% 2.44/0.70  fof(f9,axiom,(
% 2.44/0.70    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 2.44/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).
% 2.44/0.70  fof(f414,plain,(
% 2.44/0.70    r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2))),
% 2.44/0.70    inference(superposition,[],[f163,f397])).
% 2.44/0.70  fof(f397,plain,(
% 2.44/0.70    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2)),
% 2.44/0.70    inference(superposition,[],[f211,f112])).
% 2.44/0.70  fof(f112,plain,(
% 2.44/0.70    sK2 = k2_xboole_0(sK1,sK2)),
% 2.44/0.70    inference(unit_resulting_resolution,[],[f37,f57])).
% 2.44/0.70  fof(f57,plain,(
% 2.44/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.44/0.70    inference(cnf_transformation,[],[f34])).
% 2.44/0.70  fof(f34,plain,(
% 2.44/0.70    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.44/0.70    inference(ennf_transformation,[],[f3])).
% 2.44/0.70  fof(f3,axiom,(
% 2.44/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.44/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.44/0.70  fof(f37,plain,(
% 2.44/0.70    r1_tarski(sK1,sK2)),
% 2.44/0.70    inference(cnf_transformation,[],[f20])).
% 2.44/0.70  fof(f211,plain,(
% 2.44/0.70    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1))) )),
% 2.44/0.70    inference(forward_demodulation,[],[f199,f41])).
% 2.44/0.70  fof(f199,plain,(
% 2.44/0.70    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k2_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 2.44/0.70    inference(unit_resulting_resolution,[],[f40,f113,f54])).
% 2.44/0.70  fof(f54,plain,(
% 2.44/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 2.44/0.70    inference(cnf_transformation,[],[f30])).
% 2.44/0.70  fof(f30,plain,(
% 2.44/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.44/0.70    inference(flattening,[],[f29])).
% 2.44/0.70  fof(f29,plain,(
% 2.44/0.70    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.44/0.70    inference(ennf_transformation,[],[f16])).
% 2.44/0.70  fof(f16,axiom,(
% 2.44/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.44/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 2.44/0.70  fof(f113,plain,(
% 2.44/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.44/0.70    inference(unit_resulting_resolution,[],[f65,f64])).
% 2.44/0.70  fof(f64,plain,(
% 2.44/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.44/0.70    inference(cnf_transformation,[],[f36])).
% 2.44/0.70  fof(f36,plain,(
% 2.44/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.44/0.70    inference(ennf_transformation,[],[f2])).
% 2.44/0.70  fof(f2,axiom,(
% 2.44/0.70    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.44/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.44/0.70  fof(f65,plain,(
% 2.44/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.44/0.70    inference(equality_resolution,[],[f59])).
% 2.44/0.70  fof(f59,plain,(
% 2.44/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.44/0.70    inference(cnf_transformation,[],[f1])).
% 2.44/0.72  fof(f163,plain,(
% 2.44/0.72    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 2.44/0.72    inference(backward_demodulation,[],[f93,f151])).
% 2.44/0.72  fof(f151,plain,(
% 2.44/0.72    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 2.44/0.72    inference(unit_resulting_resolution,[],[f40,f50])).
% 2.44/0.72  fof(f50,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f26])).
% 2.44/0.72  fof(f26,plain,(
% 2.44/0.72    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.44/0.72    inference(ennf_transformation,[],[f15])).
% 2.44/0.72  fof(f15,axiom,(
% 2.44/0.72    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.44/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.44/0.72  fof(f93,plain,(
% 2.44/0.72    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 2.44/0.72    inference(unit_resulting_resolution,[],[f40,f52])).
% 2.44/0.72  fof(f52,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f28])).
% 2.44/0.72  fof(f28,plain,(
% 2.44/0.72    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 2.44/0.72    inference(ennf_transformation,[],[f12])).
% 2.44/0.72  fof(f12,axiom,(
% 2.44/0.72    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.44/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 2.44/0.72  fof(f40,plain,(
% 2.44/0.72    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f5])).
% 2.44/0.72  fof(f5,axiom,(
% 2.44/0.72    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.44/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.44/0.72  fof(f814,plain,(
% 2.44/0.72    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X0)) )),
% 2.44/0.72    inference(forward_demodulation,[],[f809,f542])).
% 2.44/0.72  fof(f542,plain,(
% 2.44/0.72    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 2.44/0.72    inference(superposition,[],[f362,f140])).
% 2.44/0.72  fof(f362,plain,(
% 2.44/0.72    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 2.44/0.72    inference(forward_demodulation,[],[f316,f151])).
% 2.44/0.72  fof(f316,plain,(
% 2.44/0.72    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) )),
% 2.44/0.72    inference(unit_resulting_resolution,[],[f40,f40,f55])).
% 2.44/0.72  fof(f55,plain,(
% 2.44/0.72    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f31])).
% 2.44/0.72  fof(f31,plain,(
% 2.44/0.72    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.44/0.72    inference(ennf_transformation,[],[f10])).
% 2.44/0.72  fof(f10,axiom,(
% 2.44/0.72    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 2.44/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 2.44/0.72  fof(f809,plain,(
% 2.44/0.72    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0),X0)) )),
% 2.44/0.72    inference(superposition,[],[f277,f140])).
% 2.44/0.72  fof(f277,plain,(
% 2.44/0.72    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k9_relat_1(k6_relat_1(X1),X2))) )),
% 2.44/0.72    inference(unit_resulting_resolution,[],[f68,f163,f40,f56])).
% 2.44/0.72  fof(f68,plain,(
% 2.44/0.72    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.44/0.72    inference(unit_resulting_resolution,[],[f40,f48])).
% 2.44/0.72  fof(f48,plain,(
% 2.44/0.72    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f24])).
% 2.44/0.72  fof(f24,plain,(
% 2.44/0.72    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.44/0.72    inference(ennf_transformation,[],[f6])).
% 2.44/0.72  fof(f6,axiom,(
% 2.44/0.72    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.44/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.44/0.72  fof(f363,plain,(
% 2.44/0.72    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1))) )),
% 2.44/0.72    inference(forward_demodulation,[],[f315,f150])).
% 2.44/0.72  fof(f150,plain,(
% 2.44/0.72    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) )),
% 2.44/0.72    inference(unit_resulting_resolution,[],[f39,f50])).
% 2.44/0.72  fof(f39,plain,(
% 2.44/0.72    v1_relat_1(sK0)),
% 2.44/0.72    inference(cnf_transformation,[],[f20])).
% 2.44/0.72  fof(f315,plain,(
% 2.44/0.72    ( ! [X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1))) )),
% 2.44/0.72    inference(unit_resulting_resolution,[],[f39,f40,f55])).
% 2.44/0.72  % SZS output end Proof for theBenchmark
% 2.44/0.72  % (10609)------------------------------
% 2.44/0.72  % (10609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.72  % (10609)Termination reason: Refutation
% 2.44/0.72  
% 2.44/0.72  % (10609)Memory used [KB]: 2814
% 2.44/0.72  % (10609)Time elapsed: 0.206 s
% 2.44/0.72  % (10609)------------------------------
% 2.44/0.72  % (10609)------------------------------
% 2.44/0.72  % (10601)Success in time 0.358 s
%------------------------------------------------------------------------------
