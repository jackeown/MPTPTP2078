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
% DateTime   : Thu Dec  3 12:50:30 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   71 (1170 expanded)
%              Number of leaves         :    9 ( 271 expanded)
%              Depth                    :   22
%              Number of atoms          :  161 (3531 expanded)
%              Number of equality atoms :   34 ( 354 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1340,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1339,f933])).

fof(f933,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f932])).

fof(f932,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f18,f931])).

fof(f931,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f906])).

fof(f906,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f115,f898])).

fof(f898,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f887,f20])).

fof(f20,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f887,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(k1_tarski(sK3(k10_relat_1(sK1,k1_xboole_0),X4)),X4)
      | k10_relat_1(sK1,k1_xboole_0) = X4 ) ),
    inference(backward_demodulation,[],[f878,f882])).

% (21369)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f882,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(resolution,[],[f791,f191])).

fof(f191,plain,(
    ! [X3] : ~ r2_hidden(X3,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f189,f134])).

fof(f134,plain,(
    ! [X0] : r1_xboole_0(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(resolution,[],[f129,f62])).

fof(f62,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X2)
      | ~ r1_xboole_0(X2,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f129,plain,(
    ! [X0] : r1_xboole_0(k10_relat_1(sK1,k1_xboole_0),X0) ),
    inference(resolution,[],[f95,f20])).

fof(f95,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(k1_tarski(sK6(sK2(k10_relat_1(sK1,X3),X4),X3,sK1)),X3)
      | r1_xboole_0(k10_relat_1(sK1,X3),X4) ) ),
    inference(resolution,[],[f58,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK2(k10_relat_1(sK1,X0),X1),X0,sK1),X0)
      | r1_xboole_0(k10_relat_1(sK1,X0),X1) ) ),
    inference(resolution,[],[f57,f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(sK6(X0,X1,sK1),X1) ) ),
    inference(resolution,[],[f35,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f189,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k10_relat_1(sK1,k1_xboole_0))
      | ~ r1_xboole_0(k1_tarski(sK6(X3,k10_relat_1(sK1,k1_xboole_0),sK1)),k10_relat_1(sK1,k1_xboole_0)) ) ),
    inference(resolution,[],[f186,f32])).

fof(f186,plain,(
    ! [X3] :
      ( r2_hidden(sK6(X3,k10_relat_1(sK1,k1_xboole_0),sK1),k10_relat_1(sK1,k1_xboole_0))
      | ~ r2_hidden(X3,k10_relat_1(sK1,k1_xboole_0)) ) ),
    inference(superposition,[],[f57,f171])).

fof(f171,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f114,f139])).

fof(f139,plain,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(X1,k10_relat_1(sK1,k1_xboole_0))) ),
    inference(resolution,[],[f134,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f114,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0))) ),
    inference(resolution,[],[f37,f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f791,plain,(
    ! [X15] :
      ( r2_hidden(sK3(k10_relat_1(sK1,k1_xboole_0),X15),X15)
      | k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = X15 ) ),
    inference(resolution,[],[f30,f191])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f878,plain,(
    ! [X4] :
      ( k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = X4
      | ~ r1_xboole_0(k1_tarski(sK3(k10_relat_1(sK1,k1_xboole_0),X4)),X4) ) ),
    inference(resolution,[],[f791,f32])).

fof(f115,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(superposition,[],[f114,f48])).

fof(f48,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f38,f17])).

fof(f17,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f1339,plain,(
    r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f1337,f919])).

fof(f919,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f191,f898])).

fof(f1337,plain,
    ( r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(superposition,[],[f1330,f931])).

fof(f1330,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),X1)),k10_relat_1(sK1,X1))
      | r1_xboole_0(k2_relat_1(sK1),X1) ) ),
    inference(duplicate_literal_removal,[],[f1327])).

fof(f1327,plain,(
    ! [X1] :
      ( r1_xboole_0(k2_relat_1(sK1),X1)
      | r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),X1)),k10_relat_1(sK1,X1))
      | r1_xboole_0(k2_relat_1(sK1),X1) ) ),
    inference(resolution,[],[f1093,f24])).

fof(f1093,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(k2_relat_1(sK1),X2),X3)
      | r1_xboole_0(k2_relat_1(sK1),X2)
      | r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),X2)),k10_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f55,f441])).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,k10_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f42,f19])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,sK2(k2_relat_1(X0),X1)),sK2(k2_relat_1(X0),X1)),X0)
      | r1_xboole_0(k2_relat_1(X0),X1) ) ),
    inference(resolution,[],[f40,f23])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n009.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 12:11:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.55  % (21346)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (21363)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (21362)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (21355)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.58  % (21354)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (21347)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.66/0.60  % (21362)Refutation not found, incomplete strategy% (21362)------------------------------
% 1.66/0.60  % (21362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (21362)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (21362)Memory used [KB]: 10618
% 1.66/0.60  % (21362)Time elapsed: 0.156 s
% 1.66/0.60  % (21362)------------------------------
% 1.66/0.60  % (21362)------------------------------
% 1.66/0.61  % (21349)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.66/0.61  % (21341)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.66/0.61  % (21351)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.66/0.61  % (21350)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.66/0.61  % (21351)Refutation not found, incomplete strategy% (21351)------------------------------
% 1.66/0.61  % (21351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21351)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21351)Memory used [KB]: 10618
% 1.66/0.61  % (21351)Time elapsed: 0.177 s
% 1.66/0.61  % (21351)------------------------------
% 1.66/0.61  % (21351)------------------------------
% 1.66/0.61  % (21350)Refutation not found, incomplete strategy% (21350)------------------------------
% 1.66/0.61  % (21350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21350)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21350)Memory used [KB]: 10618
% 1.66/0.61  % (21350)Time elapsed: 0.176 s
% 1.66/0.61  % (21350)------------------------------
% 1.66/0.61  % (21350)------------------------------
% 1.92/0.62  % (21343)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.92/0.62  % (21349)Refutation not found, incomplete strategy% (21349)------------------------------
% 1.92/0.62  % (21349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.62  % (21349)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.62  
% 1.92/0.62  % (21349)Memory used [KB]: 10618
% 1.92/0.62  % (21349)Time elapsed: 0.166 s
% 1.92/0.62  % (21349)------------------------------
% 1.92/0.62  % (21349)------------------------------
% 1.92/0.62  % (21342)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.92/0.63  % (21364)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.92/0.63  % (21340)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.92/0.63  % (21345)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.92/0.63  % (21340)Refutation not found, incomplete strategy% (21340)------------------------------
% 1.92/0.63  % (21340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.63  % (21340)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.63  
% 1.92/0.63  % (21340)Memory used [KB]: 1663
% 1.92/0.63  % (21340)Time elapsed: 0.187 s
% 1.92/0.63  % (21340)------------------------------
% 1.92/0.63  % (21340)------------------------------
% 1.92/0.63  % (21344)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.92/0.63  % (21346)Refutation found. Thanks to Tanya!
% 1.92/0.63  % SZS status Theorem for theBenchmark
% 1.92/0.63  % SZS output start Proof for theBenchmark
% 1.92/0.63  fof(f1340,plain,(
% 1.92/0.63    $false),
% 1.92/0.63    inference(subsumption_resolution,[],[f1339,f933])).
% 1.92/0.63  fof(f933,plain,(
% 1.92/0.63    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.92/0.63    inference(trivial_inequality_removal,[],[f932])).
% 1.92/0.63  fof(f932,plain,(
% 1.92/0.63    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.92/0.63    inference(backward_demodulation,[],[f18,f931])).
% 1.92/0.63  fof(f931,plain,(
% 1.92/0.63    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.92/0.63    inference(duplicate_literal_removal,[],[f906])).
% 1.92/0.64  fof(f906,plain,(
% 1.92/0.64    k1_xboole_0 = k10_relat_1(sK1,sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.92/0.64    inference(backward_demodulation,[],[f115,f898])).
% 1.92/0.64  fof(f898,plain,(
% 1.92/0.64    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.92/0.64    inference(resolution,[],[f887,f20])).
% 1.92/0.64  fof(f20,plain,(
% 1.92/0.64    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f3])).
% 1.92/0.64  fof(f3,axiom,(
% 1.92/0.64    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.92/0.64  fof(f887,plain,(
% 1.92/0.64    ( ! [X4] : (~r1_xboole_0(k1_tarski(sK3(k10_relat_1(sK1,k1_xboole_0),X4)),X4) | k10_relat_1(sK1,k1_xboole_0) = X4) )),
% 1.92/0.64    inference(backward_demodulation,[],[f878,f882])).
% 1.92/0.64  % (21369)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.92/0.64  fof(f882,plain,(
% 1.92/0.64    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 1.92/0.64    inference(resolution,[],[f791,f191])).
% 1.92/0.64  fof(f191,plain,(
% 1.92/0.64    ( ! [X3] : (~r2_hidden(X3,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f189,f134])).
% 1.92/0.64  fof(f134,plain,(
% 1.92/0.64    ( ! [X0] : (r1_xboole_0(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.92/0.64    inference(resolution,[],[f129,f62])).
% 1.92/0.64  fof(f62,plain,(
% 1.92/0.64    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 1.92/0.64    inference(duplicate_literal_removal,[],[f61])).
% 1.92/0.64  fof(f61,plain,(
% 1.92/0.64    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 1.92/0.64    inference(resolution,[],[f45,f24])).
% 1.92/0.64  fof(f24,plain,(
% 1.92/0.64    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f13])).
% 1.92/0.64  fof(f13,plain,(
% 1.92/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.92/0.64    inference(ennf_transformation,[],[f11])).
% 1.92/0.64  fof(f11,plain,(
% 1.92/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.92/0.64    inference(rectify,[],[f2])).
% 1.92/0.64  fof(f2,axiom,(
% 1.92/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.92/0.64  fof(f45,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),X2) | ~r1_xboole_0(X2,X0) | r1_xboole_0(X0,X1)) )),
% 1.92/0.64    inference(resolution,[],[f22,f23])).
% 1.92/0.64  fof(f23,plain,(
% 1.92/0.64    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f13])).
% 1.92/0.64  fof(f22,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f13])).
% 1.92/0.64  fof(f129,plain,(
% 1.92/0.64    ( ! [X0] : (r1_xboole_0(k10_relat_1(sK1,k1_xboole_0),X0)) )),
% 1.92/0.64    inference(resolution,[],[f95,f20])).
% 1.92/0.64  fof(f95,plain,(
% 1.92/0.64    ( ! [X4,X3] : (~r1_xboole_0(k1_tarski(sK6(sK2(k10_relat_1(sK1,X3),X4),X3,sK1)),X3) | r1_xboole_0(k10_relat_1(sK1,X3),X4)) )),
% 1.92/0.64    inference(resolution,[],[f58,f32])).
% 1.92/0.64  fof(f32,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f15])).
% 1.92/0.64  fof(f15,plain,(
% 1.92/0.64    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.92/0.64    inference(ennf_transformation,[],[f4])).
% 1.92/0.64  fof(f4,axiom,(
% 1.92/0.64    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.92/0.64  fof(f58,plain,(
% 1.92/0.64    ( ! [X0,X1] : (r2_hidden(sK6(sK2(k10_relat_1(sK1,X0),X1),X0,sK1),X0) | r1_xboole_0(k10_relat_1(sK1,X0),X1)) )),
% 1.92/0.64    inference(resolution,[],[f57,f23])).
% 1.92/0.64  fof(f57,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(sK6(X0,X1,sK1),X1)) )),
% 1.92/0.64    inference(resolution,[],[f35,f19])).
% 1.92/0.64  fof(f19,plain,(
% 1.92/0.64    v1_relat_1(sK1)),
% 1.92/0.64    inference(cnf_transformation,[],[f12])).
% 1.92/0.64  fof(f12,plain,(
% 1.92/0.64    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.92/0.64    inference(ennf_transformation,[],[f10])).
% 1.92/0.64  fof(f10,negated_conjecture,(
% 1.92/0.64    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.92/0.64    inference(negated_conjecture,[],[f9])).
% 1.92/0.64  fof(f9,conjecture,(
% 1.92/0.64    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.92/0.64  fof(f35,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.92/0.64    inference(cnf_transformation,[],[f16])).
% 1.92/0.64  fof(f16,plain,(
% 1.92/0.64    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.92/0.64    inference(ennf_transformation,[],[f7])).
% 1.92/0.64  fof(f7,axiom,(
% 1.92/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.92/0.64  fof(f189,plain,(
% 1.92/0.64    ( ! [X3] : (~r2_hidden(X3,k10_relat_1(sK1,k1_xboole_0)) | ~r1_xboole_0(k1_tarski(sK6(X3,k10_relat_1(sK1,k1_xboole_0),sK1)),k10_relat_1(sK1,k1_xboole_0))) )),
% 1.92/0.64    inference(resolution,[],[f186,f32])).
% 1.92/0.64  fof(f186,plain,(
% 1.92/0.64    ( ! [X3] : (r2_hidden(sK6(X3,k10_relat_1(sK1,k1_xboole_0),sK1),k10_relat_1(sK1,k1_xboole_0)) | ~r2_hidden(X3,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.92/0.64    inference(superposition,[],[f57,f171])).
% 1.92/0.64  fof(f171,plain,(
% 1.92/0.64    k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0))),
% 1.92/0.64    inference(superposition,[],[f114,f139])).
% 1.92/0.64  fof(f139,plain,(
% 1.92/0.64    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X1,k10_relat_1(sK1,k1_xboole_0)))) )),
% 1.92/0.64    inference(resolution,[],[f134,f38])).
% 1.92/0.64  fof(f38,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.92/0.64    inference(definition_unfolding,[],[f27,f21])).
% 1.92/0.64  fof(f21,plain,(
% 1.92/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.92/0.64    inference(cnf_transformation,[],[f5])).
% 1.92/0.64  fof(f5,axiom,(
% 1.92/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.92/0.64  fof(f27,plain,(
% 1.92/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f1])).
% 1.92/0.64  fof(f1,axiom,(
% 1.92/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.92/0.64  fof(f114,plain,(
% 1.92/0.64    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))) )),
% 1.92/0.64    inference(resolution,[],[f37,f19])).
% 1.92/0.64  fof(f37,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))) )),
% 1.92/0.64    inference(definition_unfolding,[],[f25,f21])).
% 1.92/0.64  fof(f25,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.92/0.64    inference(cnf_transformation,[],[f14])).
% 1.92/0.64  fof(f14,plain,(
% 1.92/0.64    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.92/0.64    inference(ennf_transformation,[],[f8])).
% 1.92/0.64  fof(f8,axiom,(
% 1.92/0.64    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 1.92/0.64  fof(f791,plain,(
% 1.92/0.64    ( ! [X15] : (r2_hidden(sK3(k10_relat_1(sK1,k1_xboole_0),X15),X15) | k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = X15) )),
% 1.92/0.64    inference(resolution,[],[f30,f191])).
% 1.92/0.64  fof(f30,plain,(
% 1.92/0.64    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.92/0.64    inference(cnf_transformation,[],[f6])).
% 1.92/0.64  fof(f6,axiom,(
% 1.92/0.64    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.92/0.64  fof(f878,plain,(
% 1.92/0.64    ( ! [X4] : (k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = X4 | ~r1_xboole_0(k1_tarski(sK3(k10_relat_1(sK1,k1_xboole_0),X4)),X4)) )),
% 1.92/0.64    inference(resolution,[],[f791,f32])).
% 1.92/0.64  fof(f115,plain,(
% 1.92/0.64    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.92/0.64    inference(superposition,[],[f114,f48])).
% 1.92/0.64  fof(f48,plain,(
% 1.92/0.64    k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.92/0.64    inference(resolution,[],[f38,f17])).
% 1.92/0.64  fof(f17,plain,(
% 1.92/0.64    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.92/0.64    inference(cnf_transformation,[],[f12])).
% 1.92/0.64  fof(f18,plain,(
% 1.92/0.64    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.92/0.64    inference(cnf_transformation,[],[f12])).
% 1.92/0.64  fof(f1339,plain,(
% 1.92/0.64    r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.92/0.64    inference(subsumption_resolution,[],[f1337,f919])).
% 1.92/0.64  fof(f919,plain,(
% 1.92/0.64    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 1.92/0.64    inference(backward_demodulation,[],[f191,f898])).
% 1.92/0.64  fof(f1337,plain,(
% 1.92/0.64    r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.92/0.64    inference(superposition,[],[f1330,f931])).
% 1.92/0.64  fof(f1330,plain,(
% 1.92/0.64    ( ! [X1] : (r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),X1)),k10_relat_1(sK1,X1)) | r1_xboole_0(k2_relat_1(sK1),X1)) )),
% 1.92/0.64    inference(duplicate_literal_removal,[],[f1327])).
% 1.92/0.64  fof(f1327,plain,(
% 1.92/0.64    ( ! [X1] : (r1_xboole_0(k2_relat_1(sK1),X1) | r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),X1)),k10_relat_1(sK1,X1)) | r1_xboole_0(k2_relat_1(sK1),X1)) )),
% 1.92/0.64    inference(resolution,[],[f1093,f24])).
% 1.92/0.64  fof(f1093,plain,(
% 1.92/0.64    ( ! [X2,X3] : (~r2_hidden(sK2(k2_relat_1(sK1),X2),X3) | r1_xboole_0(k2_relat_1(sK1),X2) | r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),X2)),k10_relat_1(sK1,X3))) )),
% 1.92/0.64    inference(resolution,[],[f55,f441])).
% 1.92/0.64  fof(f441,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,X2) | r2_hidden(X0,k10_relat_1(sK1,X2))) )),
% 1.92/0.64    inference(resolution,[],[f42,f19])).
% 1.92/0.64  fof(f42,plain,(
% 1.92/0.64    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f36,f41])).
% 1.92/0.64  fof(f41,plain,(
% 1.92/0.64    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.92/0.64    inference(equality_resolution,[],[f28])).
% 1.92/0.64  fof(f28,plain,(
% 1.92/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.92/0.64    inference(cnf_transformation,[],[f6])).
% 1.92/0.64  fof(f36,plain,(
% 1.92/0.64    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.92/0.64    inference(cnf_transformation,[],[f16])).
% 1.92/0.64  fof(f55,plain,(
% 1.92/0.64    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,sK2(k2_relat_1(X0),X1)),sK2(k2_relat_1(X0),X1)),X0) | r1_xboole_0(k2_relat_1(X0),X1)) )),
% 1.92/0.64    inference(resolution,[],[f40,f23])).
% 1.92/0.64  fof(f40,plain,(
% 1.92/0.64    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)) )),
% 1.92/0.64    inference(equality_resolution,[],[f29])).
% 1.92/0.64  fof(f29,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.92/0.64    inference(cnf_transformation,[],[f6])).
% 1.92/0.64  % SZS output end Proof for theBenchmark
% 1.92/0.64  % (21346)------------------------------
% 1.92/0.64  % (21346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.64  % (21346)Termination reason: Refutation
% 1.92/0.64  
% 1.92/0.64  % (21346)Memory used [KB]: 7036
% 1.92/0.64  % (21346)Time elapsed: 0.204 s
% 1.92/0.64  % (21346)------------------------------
% 1.92/0.64  % (21346)------------------------------
% 1.92/0.64  % (21339)Success in time 0.266 s
%------------------------------------------------------------------------------
