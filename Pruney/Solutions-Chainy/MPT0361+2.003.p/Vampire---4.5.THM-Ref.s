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
% DateTime   : Thu Dec  3 12:44:58 EST 2020

% Result     : Theorem 4.53s
% Output     : Refutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  116 ( 242 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7653,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7526,f410])).

fof(f410,plain,(
    ! [X6,X7,X5] : r2_hidden(k4_xboole_0(X5,k2_xboole_0(X6,X7)),k1_zfmisc_1(k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f79,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f7526,plain,(
    ~ r2_hidden(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f640,f7523])).

fof(f7523,plain,(
    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f7403,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f7403,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f7397,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f7397,plain,(
    r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f7363,f65])).

fof(f7363,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f7354,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f7354,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),sK0) ),
    inference(superposition,[],[f6716,f101])).

fof(f101,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f91,plain,(
    r1_tarski(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f87,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f33,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f6716,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0)) ),
    inference(unit_resulting_resolution,[],[f6589,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f6589,plain,(
    ! [X34] : r1_tarski(k4_xboole_0(k2_xboole_0(X34,sK1),X34),sK0) ),
    inference(superposition,[],[f2394,f102])).

fof(f102,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f94,f47])).

fof(f94,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f88,f64])).

fof(f88,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f35,f46])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f2394,plain,(
    ! [X14,X15,X16] : r1_tarski(k4_xboole_0(k2_xboole_0(X14,X15),X14),k2_xboole_0(X15,X16)) ),
    inference(subsumption_resolution,[],[f2378,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2378,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k1_xboole_0,X16)
      | r1_tarski(k4_xboole_0(k2_xboole_0(X14,X15),X14),k2_xboole_0(X15,X16)) ) ),
    inference(superposition,[],[f411,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f41,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f411,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tarski(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X11)
      | r1_tarski(k4_xboole_0(X8,X9),k2_xboole_0(X10,X11)) ) ),
    inference(superposition,[],[f59,f58])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f640,plain,(
    ~ r2_hidden(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f303,f517])).

fof(f517,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f33,f35,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f303,plain,(
    ~ r2_hidden(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f218,f289])).

fof(f289,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f35,f49])).

fof(f218,plain,(
    ~ r2_hidden(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(k3_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f34,f64])).

fof(f34,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:43:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (5328)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (5320)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (5321)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (5342)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (5327)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (5322)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (5335)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (5318)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (5317)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (5329)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (5333)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (5339)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (5331)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (5325)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (5338)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (5336)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (5340)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (5323)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  % (5341)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (5324)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.55  % (5319)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.55  % (5330)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (5337)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.56  % (5334)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.56  % (5326)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.56  % (5332)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 4.30/0.93  % (5317)Time limit reached!
% 4.30/0.93  % (5317)------------------------------
% 4.30/0.93  % (5317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.93  % (5317)Termination reason: Time limit
% 4.30/0.93  
% 4.30/0.93  % (5317)Memory used [KB]: 15479
% 4.30/0.93  % (5317)Time elapsed: 0.502 s
% 4.30/0.93  % (5317)------------------------------
% 4.30/0.93  % (5317)------------------------------
% 4.30/0.93  % (5330)Time limit reached!
% 4.30/0.93  % (5330)------------------------------
% 4.30/0.93  % (5330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.93  % (5330)Termination reason: Time limit
% 4.30/0.93  
% 4.30/0.93  % (5330)Memory used [KB]: 8699
% 4.30/0.93  % (5330)Time elapsed: 0.515 s
% 4.30/0.93  % (5330)------------------------------
% 4.30/0.93  % (5330)------------------------------
% 4.53/0.95  % (5324)Refutation found. Thanks to Tanya!
% 4.53/0.95  % SZS status Theorem for theBenchmark
% 4.53/0.95  % SZS output start Proof for theBenchmark
% 4.53/0.95  fof(f7653,plain,(
% 4.53/0.95    $false),
% 4.53/0.95    inference(subsumption_resolution,[],[f7526,f410])).
% 4.53/0.95  fof(f410,plain,(
% 4.53/0.95    ( ! [X6,X7,X5] : (r2_hidden(k4_xboole_0(X5,k2_xboole_0(X6,X7)),k1_zfmisc_1(k4_xboole_0(X5,X6)))) )),
% 4.53/0.95    inference(superposition,[],[f79,f58])).
% 4.53/0.95  fof(f58,plain,(
% 4.53/0.95    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.53/0.95    inference(cnf_transformation,[],[f8])).
% 4.53/0.95  fof(f8,axiom,(
% 4.53/0.95    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.53/0.95  fof(f79,plain,(
% 4.53/0.95    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f40,f65])).
% 4.53/0.95  fof(f65,plain,(
% 4.53/0.95    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 4.53/0.95    inference(equality_resolution,[],[f54])).
% 4.53/0.95  fof(f54,plain,(
% 4.53/0.95    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.53/0.95    inference(cnf_transformation,[],[f12])).
% 4.53/0.95  fof(f12,axiom,(
% 4.53/0.95    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 4.53/0.95  fof(f40,plain,(
% 4.53/0.95    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.53/0.95    inference(cnf_transformation,[],[f7])).
% 4.53/0.95  fof(f7,axiom,(
% 4.53/0.95    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.53/0.95  fof(f7526,plain,(
% 4.53/0.95    ~r2_hidden(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 4.53/0.95    inference(backward_demodulation,[],[f640,f7523])).
% 4.53/0.95  fof(f7523,plain,(
% 4.53/0.95    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f7403,f49])).
% 4.53/0.95  fof(f49,plain,(
% 4.53/0.95    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 4.53/0.95    inference(cnf_transformation,[],[f26])).
% 4.53/0.95  fof(f26,plain,(
% 4.53/0.95    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.95    inference(ennf_transformation,[],[f14])).
% 4.53/0.95  fof(f14,axiom,(
% 4.53/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 4.53/0.95  fof(f7403,plain,(
% 4.53/0.95    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f36,f7397,f45])).
% 4.53/0.95  fof(f45,plain,(
% 4.53/0.95    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 4.53/0.95    inference(cnf_transformation,[],[f23])).
% 4.53/0.95  fof(f23,plain,(
% 4.53/0.95    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 4.53/0.95    inference(ennf_transformation,[],[f13])).
% 4.53/0.95  fof(f13,axiom,(
% 4.53/0.95    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 4.53/0.95  fof(f7397,plain,(
% 4.53/0.95    r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f7363,f65])).
% 4.53/0.95  fof(f7363,plain,(
% 4.53/0.95    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 4.53/0.95    inference(forward_demodulation,[],[f7354,f42])).
% 4.53/0.95  fof(f42,plain,(
% 4.53/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.53/0.95    inference(cnf_transformation,[],[f1])).
% 4.53/0.95  fof(f1,axiom,(
% 4.53/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.53/0.95  fof(f7354,plain,(
% 4.53/0.95    r1_tarski(k2_xboole_0(sK2,sK1),sK0)),
% 4.53/0.95    inference(superposition,[],[f6716,f101])).
% 4.53/0.95  fof(f101,plain,(
% 4.53/0.95    sK0 = k2_xboole_0(sK2,sK0)),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f91,f47])).
% 4.53/0.95  fof(f47,plain,(
% 4.53/0.95    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.53/0.95    inference(cnf_transformation,[],[f24])).
% 4.53/0.95  fof(f24,plain,(
% 4.53/0.95    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.53/0.95    inference(ennf_transformation,[],[f4])).
% 4.53/0.95  fof(f4,axiom,(
% 4.53/0.95    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.53/0.95  fof(f91,plain,(
% 4.53/0.95    r1_tarski(sK2,sK0)),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f87,f64])).
% 4.53/0.95  fof(f64,plain,(
% 4.53/0.95    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 4.53/0.95    inference(equality_resolution,[],[f55])).
% 4.53/0.95  fof(f55,plain,(
% 4.53/0.95    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.53/0.95    inference(cnf_transformation,[],[f12])).
% 4.53/0.95  fof(f87,plain,(
% 4.53/0.95    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f36,f33,f46])).
% 4.53/0.95  fof(f46,plain,(
% 4.53/0.95    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 4.53/0.95    inference(cnf_transformation,[],[f23])).
% 4.53/0.95  fof(f33,plain,(
% 4.53/0.95    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.53/0.95    inference(cnf_transformation,[],[f22])).
% 4.53/0.95  fof(f22,plain,(
% 4.53/0.95    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.95    inference(ennf_transformation,[],[f20])).
% 4.53/0.95  fof(f20,negated_conjecture,(
% 4.53/0.95    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 4.53/0.95    inference(negated_conjecture,[],[f19])).
% 4.53/0.95  fof(f19,conjecture,(
% 4.53/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 4.53/0.95  fof(f6716,plain,(
% 4.53/0.95    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0))) )),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f6589,f59])).
% 4.53/0.95  fof(f59,plain,(
% 4.53/0.95    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.53/0.95    inference(cnf_transformation,[],[f28])).
% 4.53/0.95  fof(f28,plain,(
% 4.53/0.95    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.53/0.95    inference(ennf_transformation,[],[f9])).
% 4.53/0.95  fof(f9,axiom,(
% 4.53/0.95    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 4.53/0.95  fof(f6589,plain,(
% 4.53/0.95    ( ! [X34] : (r1_tarski(k4_xboole_0(k2_xboole_0(X34,sK1),X34),sK0)) )),
% 4.53/0.95    inference(superposition,[],[f2394,f102])).
% 4.53/0.95  fof(f102,plain,(
% 4.53/0.95    sK0 = k2_xboole_0(sK1,sK0)),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f94,f47])).
% 4.53/0.95  fof(f94,plain,(
% 4.53/0.95    r1_tarski(sK1,sK0)),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f88,f64])).
% 4.53/0.95  fof(f88,plain,(
% 4.53/0.95    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f36,f35,f46])).
% 4.53/0.95  fof(f35,plain,(
% 4.53/0.95    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.53/0.95    inference(cnf_transformation,[],[f22])).
% 4.53/0.95  fof(f2394,plain,(
% 4.53/0.95    ( ! [X14,X15,X16] : (r1_tarski(k4_xboole_0(k2_xboole_0(X14,X15),X14),k2_xboole_0(X15,X16))) )),
% 4.53/0.95    inference(subsumption_resolution,[],[f2378,f37])).
% 4.53/0.95  fof(f37,plain,(
% 4.53/0.95    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.53/0.95    inference(cnf_transformation,[],[f6])).
% 4.53/0.95  fof(f6,axiom,(
% 4.53/0.95    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.53/0.95  fof(f2378,plain,(
% 4.53/0.95    ( ! [X14,X15,X16] : (~r1_tarski(k1_xboole_0,X16) | r1_tarski(k4_xboole_0(k2_xboole_0(X14,X15),X14),k2_xboole_0(X15,X16))) )),
% 4.53/0.95    inference(superposition,[],[f411,f67])).
% 4.53/0.95  fof(f67,plain,(
% 4.53/0.95    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 4.53/0.95    inference(superposition,[],[f41,f38])).
% 4.53/0.95  fof(f38,plain,(
% 4.53/0.95    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.53/0.95    inference(cnf_transformation,[],[f21])).
% 4.53/0.95  fof(f21,plain,(
% 4.53/0.95    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.53/0.95    inference(rectify,[],[f2])).
% 4.53/0.95  fof(f2,axiom,(
% 4.53/0.95    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 4.53/0.95  fof(f41,plain,(
% 4.53/0.95    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.53/0.95    inference(cnf_transformation,[],[f10])).
% 4.53/0.95  fof(f10,axiom,(
% 4.53/0.95    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 4.53/0.95  fof(f411,plain,(
% 4.53/0.95    ( ! [X10,X8,X11,X9] : (~r1_tarski(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X11) | r1_tarski(k4_xboole_0(X8,X9),k2_xboole_0(X10,X11))) )),
% 4.53/0.95    inference(superposition,[],[f59,f58])).
% 4.53/0.95  fof(f36,plain,(
% 4.53/0.95    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 4.53/0.95    inference(cnf_transformation,[],[f16])).
% 4.53/0.95  fof(f16,axiom,(
% 4.53/0.95    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 4.53/0.95  fof(f640,plain,(
% 4.53/0.95    ~r2_hidden(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 4.53/0.95    inference(backward_demodulation,[],[f303,f517])).
% 4.53/0.95  fof(f517,plain,(
% 4.53/0.95    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f33,f35,f61])).
% 4.53/0.95  fof(f61,plain,(
% 4.53/0.95    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 4.53/0.95    inference(cnf_transformation,[],[f32])).
% 4.53/0.95  fof(f32,plain,(
% 4.53/0.95    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.95    inference(flattening,[],[f31])).
% 4.53/0.95  fof(f31,plain,(
% 4.53/0.95    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.53/0.95    inference(ennf_transformation,[],[f18])).
% 4.53/0.95  fof(f18,axiom,(
% 4.53/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.53/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.53/0.95  fof(f303,plain,(
% 4.53/0.95    ~r2_hidden(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 4.53/0.95    inference(backward_demodulation,[],[f218,f289])).
% 4.53/0.95  fof(f289,plain,(
% 4.53/0.95    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f35,f49])).
% 4.53/0.95  fof(f218,plain,(
% 4.53/0.95    ~r2_hidden(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(k3_subset_1(sK0,sK1)))),
% 4.53/0.95    inference(unit_resulting_resolution,[],[f34,f64])).
% 4.53/0.95  fof(f34,plain,(
% 4.53/0.95    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 4.53/0.95    inference(cnf_transformation,[],[f22])).
% 4.53/0.95  % SZS output end Proof for theBenchmark
% 4.53/0.95  % (5324)------------------------------
% 4.53/0.95  % (5324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/0.95  % (5324)Termination reason: Refutation
% 4.53/0.95  
% 4.53/0.95  % (5324)Memory used [KB]: 6396
% 4.53/0.95  % (5324)Time elapsed: 0.535 s
% 4.53/0.95  % (5324)------------------------------
% 4.53/0.95  % (5324)------------------------------
% 4.53/0.95  % (5316)Success in time 0.593 s
%------------------------------------------------------------------------------
