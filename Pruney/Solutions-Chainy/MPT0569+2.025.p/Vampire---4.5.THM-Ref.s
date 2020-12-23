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
% DateTime   : Thu Dec  3 12:50:29 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 312 expanded)
%              Number of leaves         :   10 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  143 ( 713 expanded)
%              Number of equality atoms :   32 ( 171 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f750,plain,(
    $false ),
    inference(subsumption_resolution,[],[f742,f723])).

% (18961)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f723,plain,(
    k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f715,f69])).

fof(f69,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f20,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f20,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

% (18963)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f715,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) ),
    inference(subsumption_resolution,[],[f714,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f714,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f711,f75])).

fof(f75,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f74,f66])).

fof(f66,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f21,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f71,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(sK1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) ),
    inference(resolution,[],[f70,f22])).

fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r2_hidden(X0,k10_relat_1(sK1,k1_setfam_1(k2_tarski(X1,X2)))) ) ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,X3,sK1),X3)
      | ~ r2_hidden(X2,k10_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f21,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

% (18968)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f711,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f415,f19])).

fof(f19,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f415,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(sK1,X3),k10_relat_1(sK1,X2))
      | ~ r2_hidden(X3,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X2))) ) ),
    inference(subsumption_resolution,[],[f413,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f25])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f413,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(sK1,X3),k10_relat_1(sK1,X2))
      | ~ r2_hidden(X3,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X2)))
      | ~ r2_hidden(X3,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f309,f65])).

fof(f65,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X7))) ),
    inference(resolution,[],[f21,f48])).

% (18981)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f309,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(sK1,X5),k10_relat_1(sK1,X6))
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X5,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f67,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f67,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),sK1)
      | ~ r2_hidden(X4,X6)
      | r2_hidden(X5,k10_relat_1(sK1,X6)) ) ),
    inference(subsumption_resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X3,X2),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k2_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X5,X4),sK1)
      | ~ r2_hidden(X4,X6)
      | r2_hidden(X5,k10_relat_1(sK1,X6)) ) ),
    inference(resolution,[],[f21,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f742,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f728,f312])).

fof(f312,plain,(
    ! [X4] :
      ( r2_hidden(sK3(k1_xboole_0,X4),X4)
      | k1_xboole_0 = X4 ) ),
    inference(backward_demodulation,[],[f78,f282])).

fof(f282,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f78,f75])).

fof(f78,plain,(
    ! [X4] :
      ( r2_hidden(sK3(k1_xboole_0,X4),X4)
      | k2_relat_1(k1_xboole_0) = X4 ) ),
    inference(resolution,[],[f75,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f728,plain,(
    ! [X7] : ~ r2_hidden(X7,k10_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f725,f65])).

fof(f725,plain,(
    ! [X7] : ~ r2_hidden(X7,k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))) ),
    inference(resolution,[],[f715,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:18:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (18962)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (18964)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (18978)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.53  % (18978)Refutation found. Thanks to Tanya!
% 1.24/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % (18958)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.54  % (18960)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f750,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(subsumption_resolution,[],[f742,f723])).
% 1.24/0.54  % (18961)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.54  fof(f723,plain,(
% 1.24/0.54    k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.24/0.54    inference(resolution,[],[f715,f69])).
% 1.24/0.54  fof(f69,plain,(
% 1.24/0.54    r2_hidden(sK2(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.24/0.54    inference(resolution,[],[f20,f46])).
% 1.24/0.54  fof(f46,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.24/0.54    inference(definition_unfolding,[],[f27,f25])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f6])).
% 1.24/0.54  fof(f6,axiom,(
% 1.24/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.24/0.54  fof(f27,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f16])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.24/0.54    inference(ennf_transformation,[],[f13])).
% 1.24/0.54  fof(f13,plain,(
% 1.24/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.54    inference(rectify,[],[f3])).
% 1.24/0.54  fof(f3,axiom,(
% 1.24/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.24/0.54  fof(f20,plain,(
% 1.24/0.54    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f14])).
% 1.24/0.54  fof(f14,plain,(
% 1.24/0.54    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.24/0.54    inference(ennf_transformation,[],[f12])).
% 1.40/0.54  % (18963)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.54  fof(f12,negated_conjecture,(
% 1.40/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.40/0.54    inference(negated_conjecture,[],[f11])).
% 1.40/0.54  fof(f11,conjecture,(
% 1.40/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.40/0.54  fof(f715,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f714,f47])).
% 1.40/0.54  fof(f47,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f26,f25])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  fof(f714,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f711,f75])).
% 1.40/0.54  fof(f75,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.40/0.54    inference(forward_demodulation,[],[f74,f66])).
% 1.40/0.54  fof(f66,plain,(
% 1.40/0.54    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.40/0.54    inference(resolution,[],[f21,f24])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f10])).
% 1.40/0.54  fof(f10,axiom,(
% 1.40/0.54    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    v1_relat_1(sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f14])).
% 1.40/0.54  fof(f74,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.40/0.54    inference(forward_demodulation,[],[f71,f45])).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f23,f25])).
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.40/0.54  fof(f71,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))))) )),
% 1.40/0.54    inference(resolution,[],[f70,f22])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.40/0.54  fof(f70,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r2_hidden(X0,k10_relat_1(sK1,k1_setfam_1(k2_tarski(X1,X2))))) )),
% 1.40/0.54    inference(resolution,[],[f63,f47])).
% 1.40/0.54  fof(f63,plain,(
% 1.40/0.54    ( ! [X2,X3] : (r2_hidden(sK6(X2,X3,sK1),X3) | ~r2_hidden(X2,k10_relat_1(sK1,X3))) )),
% 1.40/0.54    inference(resolution,[],[f21,f37])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f18])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.40/0.54    inference(ennf_transformation,[],[f8])).
% 1.40/0.54  fof(f8,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.40/0.54  % (18968)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.54  fof(f711,plain,(
% 1.40/0.54    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_xboole_0) | ~r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 1.40/0.54    inference(superposition,[],[f415,f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    k1_xboole_0 = k10_relat_1(sK1,sK0) | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f14])).
% 1.40/0.54  fof(f415,plain,(
% 1.40/0.54    ( ! [X2,X3] : (r2_hidden(sK4(sK1,X3),k10_relat_1(sK1,X2)) | ~r2_hidden(X3,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X2)))) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f413,f61])).
% 1.40/0.54  fof(f61,plain,(
% 1.40/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.40/0.54    inference(equality_resolution,[],[f53])).
% 1.40/0.54  fof(f53,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.40/0.54    inference(definition_unfolding,[],[f42,f25])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.40/0.54    inference(cnf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.40/0.54  fof(f413,plain,(
% 1.40/0.54    ( ! [X2,X3] : (r2_hidden(sK4(sK1,X3),k10_relat_1(sK1,X2)) | ~r2_hidden(X3,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X2))) | ~r2_hidden(X3,k2_relat_1(sK1))) )),
% 1.40/0.54    inference(superposition,[],[f309,f65])).
% 1.40/0.54  fof(f65,plain,(
% 1.40/0.54    ( ! [X7] : (k10_relat_1(sK1,X7) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X7)))) )),
% 1.40/0.54    inference(resolution,[],[f21,f48])).
% 1.40/0.54  % (18981)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.54  fof(f48,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f28,f25])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f17])).
% 1.40/0.54  fof(f17,plain,(
% 1.40/0.54    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.40/0.54    inference(ennf_transformation,[],[f9])).
% 1.40/0.54  fof(f9,axiom,(
% 1.40/0.54    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 1.40/0.54  fof(f309,plain,(
% 1.40/0.54    ( ! [X6,X5] : (r2_hidden(sK4(sK1,X5),k10_relat_1(sK1,X6)) | ~r2_hidden(X5,X6) | ~r2_hidden(X5,k2_relat_1(sK1))) )),
% 1.40/0.54    inference(resolution,[],[f67,f57])).
% 1.40/0.54  fof(f57,plain,(
% 1.40/0.54    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.40/0.54    inference(equality_resolution,[],[f32])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    ( ! [X6,X4,X5] : (~r2_hidden(k4_tarski(X5,X4),sK1) | ~r2_hidden(X4,X6) | r2_hidden(X5,k10_relat_1(sK1,X6))) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f64,f58])).
% 1.40/0.54  fof(f58,plain,(
% 1.40/0.54    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) )),
% 1.40/0.54    inference(equality_resolution,[],[f31])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f64,plain,(
% 1.40/0.54    ( ! [X6,X4,X5] : (~r2_hidden(X4,k2_relat_1(sK1)) | ~r2_hidden(k4_tarski(X5,X4),sK1) | ~r2_hidden(X4,X6) | r2_hidden(X5,k10_relat_1(sK1,X6))) )),
% 1.40/0.54    inference(resolution,[],[f21,f38])).
% 1.40/0.54  fof(f38,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f18])).
% 1.40/0.54  fof(f742,plain,(
% 1.40/0.54    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.40/0.54    inference(resolution,[],[f728,f312])).
% 1.40/0.54  fof(f312,plain,(
% 1.40/0.54    ( ! [X4] : (r2_hidden(sK3(k1_xboole_0,X4),X4) | k1_xboole_0 = X4) )),
% 1.40/0.54    inference(backward_demodulation,[],[f78,f282])).
% 1.40/0.54  fof(f282,plain,(
% 1.40/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.40/0.54    inference(resolution,[],[f78,f75])).
% 1.40/0.54  fof(f78,plain,(
% 1.40/0.54    ( ! [X4] : (r2_hidden(sK3(k1_xboole_0,X4),X4) | k2_relat_1(k1_xboole_0) = X4) )),
% 1.40/0.54    inference(resolution,[],[f75,f33])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f728,plain,(
% 1.40/0.54    ( ! [X7] : (~r2_hidden(X7,k10_relat_1(sK1,sK0))) )),
% 1.40/0.54    inference(forward_demodulation,[],[f725,f65])).
% 1.40/0.54  fof(f725,plain,(
% 1.40/0.54    ( ! [X7] : (~r2_hidden(X7,k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))))) )),
% 1.40/0.54    inference(resolution,[],[f715,f63])).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (18978)------------------------------
% 1.40/0.54  % (18978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (18978)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (18978)Memory used [KB]: 1918
% 1.40/0.54  % (18978)Time elapsed: 0.117 s
% 1.40/0.54  % (18978)------------------------------
% 1.40/0.54  % (18978)------------------------------
% 1.40/0.54  % (18956)Success in time 0.177 s
%------------------------------------------------------------------------------
