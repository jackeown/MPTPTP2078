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
% DateTime   : Thu Dec  3 12:42:30 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   86 (2804 expanded)
%              Number of leaves         :    8 ( 723 expanded)
%              Depth                    :   34
%              Number of atoms          :  142 (5419 expanded)
%              Number of equality atoms :   75 (4551 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1066,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1064,f815])).

fof(f815,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(subsumption_resolution,[],[f434,f752])).

fof(f752,plain,(
    sK0 != sK2 ),
    inference(subsumption_resolution,[],[f15,f750])).

fof(f750,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f501,f749])).

fof(f749,plain,(
    r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f731,f29])).

fof(f29,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f731,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK1,sK3) ),
    inference(superposition,[],[f442,f710])).

fof(f710,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f709,f16])).

fof(f16,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f709,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f708,f503])).

fof(f503,plain,(
    sK3 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f502,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f502,plain,(
    sK3 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f500,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f500,plain,(
    r1_tarski(sK3,sK1) ),
    inference(subsumption_resolution,[],[f497,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f497,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f456,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f456,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f255,f435])).

fof(f435,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f433,f22])).

fof(f433,plain,(
    r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f430,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f430,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f406,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f406,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f189,f347])).

fof(f347,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f304,f346])).

fof(f346,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f344,f205])).

fof(f205,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f171,f21])).

fof(f171,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f145,f16])).

fof(f145,plain,(
    ! [X4,X2,X3] : r1_tarski(k2_zfmisc_1(X2,k3_xboole_0(X3,X4)),k2_zfmisc_1(X2,X3)) ),
    inference(superposition,[],[f20,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f28,f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f344,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f342,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f342,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f337,f16])).

fof(f337,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f330,f19])).

fof(f330,plain,(
    ! [X8] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X8)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f329,f137])).

fof(f137,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) ),
    inference(superposition,[],[f111,f16])).

fof(f329,plain,(
    ! [X8] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X8)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f316,f28])).

fof(f316,plain,(
    ! [X8] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X8)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f145,f304])).

fof(f304,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f286,f21])).

fof(f286,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f137,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f28,f19])).

fof(f189,plain,(
    ! [X24,X23,X25] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X23,X25),X24),k2_zfmisc_1(X25,X24)) ),
    inference(superposition,[],[f32,f118])).

fof(f32,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f20,f21])).

fof(f255,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f248,f21])).

fof(f248,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f184,f16])).

fof(f184,plain,(
    ! [X6,X4,X5] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X4,X6),X5),k2_zfmisc_1(X4,X5)) ),
    inference(superposition,[],[f20,f118])).

fof(f708,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f684,f21])).

fof(f684,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f491,f19])).

fof(f491,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,sK1)) ),
    inference(backward_demodulation,[],[f139,f478])).

fof(f478,plain,(
    ! [X0,X1] : k2_zfmisc_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,X1)) ),
    inference(superposition,[],[f28,f466])).

fof(f466,plain,(
    sK0 = k3_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f58,f435])).

fof(f58,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f39,f21])).

fof(f39,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X4) ),
    inference(resolution,[],[f22,f32])).

fof(f139,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f111,f16])).

fof(f442,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X2))
      | r1_tarski(sK1,X2) ) ),
    inference(forward_demodulation,[],[f441,f435])).

fof(f441,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2))
      | r1_tarski(sK1,X2) ) ),
    inference(subsumption_resolution,[],[f436,f17])).

fof(f436,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK0
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2))
      | r1_tarski(sK1,X2) ) ),
    inference(backward_demodulation,[],[f348,f435])).

fof(f348,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2))
      | k1_xboole_0 = k3_xboole_0(sK0,sK2)
      | r1_tarski(sK1,X2) ) ),
    inference(backward_demodulation,[],[f310,f346])).

fof(f310,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2))
      | k1_xboole_0 = k3_xboole_0(sK0,sK2)
      | r1_tarski(sK1,X2) ) ),
    inference(superposition,[],[f27,f304])).

fof(f501,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK1 = sK3 ),
    inference(resolution,[],[f500,f25])).

fof(f15,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f434,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f433,f25])).

fof(f1064,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f819,f29])).

fof(f819,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1))
      | r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f818,f18])).

fof(f818,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1))
      | r1_tarski(sK2,X0) ) ),
    inference(forward_demodulation,[],[f754,f750])).

fof(f754,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1))
      | k1_xboole_0 = sK3
      | r1_tarski(sK2,X0) ) ),
    inference(backward_demodulation,[],[f102,f750])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
      | k1_xboole_0 = sK3
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f26,f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (30343)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.44  % (30343)Refutation not found, incomplete strategy% (30343)------------------------------
% 0.21/0.44  % (30343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (30350)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.45  % (30366)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.45  % (30343)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (30343)Memory used [KB]: 10618
% 0.21/0.45  % (30343)Time elapsed: 0.057 s
% 0.21/0.45  % (30343)------------------------------
% 0.21/0.45  % (30343)------------------------------
% 0.21/0.50  % (30353)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (30348)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (30347)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (30358)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (30364)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (30360)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (30344)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (30349)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (30345)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (30342)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (30355)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (30348)Refutation not found, incomplete strategy% (30348)------------------------------
% 0.21/0.52  % (30348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30352)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (30347)Refutation not found, incomplete strategy% (30347)------------------------------
% 0.21/0.52  % (30347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30347)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30347)Memory used [KB]: 6140
% 0.21/0.52  % (30347)Time elapsed: 0.110 s
% 0.21/0.52  % (30347)------------------------------
% 0.21/0.52  % (30347)------------------------------
% 0.21/0.52  % (30359)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (30365)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (30363)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (30355)Refutation not found, incomplete strategy% (30355)------------------------------
% 0.21/0.52  % (30355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30355)Memory used [KB]: 6140
% 0.21/0.52  % (30355)Time elapsed: 0.117 s
% 0.21/0.52  % (30355)------------------------------
% 0.21/0.52  % (30355)------------------------------
% 0.21/0.53  % (30356)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (30348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30348)Memory used [KB]: 10618
% 0.21/0.53  % (30348)Time elapsed: 0.085 s
% 0.21/0.53  % (30348)------------------------------
% 0.21/0.53  % (30348)------------------------------
% 0.21/0.53  % (30351)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (30346)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (30361)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (30367)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (30362)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  % (30354)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.43/0.55  % (30357)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.72/0.60  % (30361)Refutation found. Thanks to Tanya!
% 1.72/0.60  % SZS status Theorem for theBenchmark
% 1.72/0.60  % SZS output start Proof for theBenchmark
% 1.72/0.60  fof(f1066,plain,(
% 1.72/0.60    $false),
% 1.72/0.60    inference(subsumption_resolution,[],[f1064,f815])).
% 1.72/0.60  fof(f815,plain,(
% 1.72/0.60    ~r1_tarski(sK2,sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f434,f752])).
% 1.72/0.60  fof(f752,plain,(
% 1.72/0.60    sK0 != sK2),
% 1.72/0.60    inference(subsumption_resolution,[],[f15,f750])).
% 1.72/0.60  fof(f750,plain,(
% 1.72/0.60    sK1 = sK3),
% 1.72/0.60    inference(subsumption_resolution,[],[f501,f749])).
% 1.72/0.60  fof(f749,plain,(
% 1.72/0.60    r1_tarski(sK1,sK3)),
% 1.72/0.60    inference(subsumption_resolution,[],[f731,f29])).
% 1.72/0.60  fof(f29,plain,(
% 1.72/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.72/0.60    inference(equality_resolution,[],[f24])).
% 1.72/0.60  fof(f24,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.72/0.60    inference(cnf_transformation,[],[f3])).
% 1.72/0.60  fof(f3,axiom,(
% 1.72/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.72/0.60  fof(f731,plain,(
% 1.72/0.60    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK1,sK3)),
% 1.72/0.60    inference(superposition,[],[f442,f710])).
% 1.72/0.60  fof(f710,plain,(
% 1.72/0.60    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 1.72/0.60    inference(forward_demodulation,[],[f709,f16])).
% 1.72/0.60  fof(f16,plain,(
% 1.72/0.60    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 1.72/0.60    inference(cnf_transformation,[],[f12])).
% 1.72/0.60  fof(f12,plain,(
% 1.72/0.60    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.72/0.60    inference(flattening,[],[f11])).
% 1.72/0.60  fof(f11,plain,(
% 1.72/0.60    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.72/0.60    inference(ennf_transformation,[],[f9])).
% 1.72/0.60  fof(f9,negated_conjecture,(
% 1.72/0.60    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.72/0.60    inference(negated_conjecture,[],[f8])).
% 1.72/0.60  fof(f8,conjecture,(
% 1.72/0.60    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.72/0.60  fof(f709,plain,(
% 1.72/0.60    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3)),
% 1.72/0.60    inference(forward_demodulation,[],[f708,f503])).
% 1.72/0.60  fof(f503,plain,(
% 1.72/0.60    sK3 = k3_xboole_0(sK1,sK3)),
% 1.72/0.60    inference(superposition,[],[f502,f21])).
% 1.72/0.60  fof(f21,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f1])).
% 1.72/0.60  fof(f1,axiom,(
% 1.72/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.72/0.60  fof(f502,plain,(
% 1.72/0.60    sK3 = k3_xboole_0(sK3,sK1)),
% 1.72/0.60    inference(resolution,[],[f500,f22])).
% 1.72/0.60  fof(f22,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f13,plain,(
% 1.72/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.72/0.60    inference(ennf_transformation,[],[f5])).
% 1.72/0.60  fof(f5,axiom,(
% 1.72/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.72/0.60  fof(f500,plain,(
% 1.72/0.60    r1_tarski(sK3,sK1)),
% 1.72/0.60    inference(subsumption_resolution,[],[f497,f17])).
% 1.72/0.60  fof(f17,plain,(
% 1.72/0.60    k1_xboole_0 != sK0),
% 1.72/0.60    inference(cnf_transformation,[],[f12])).
% 1.72/0.60  fof(f497,plain,(
% 1.72/0.60    k1_xboole_0 = sK0 | r1_tarski(sK3,sK1)),
% 1.72/0.60    inference(resolution,[],[f456,f27])).
% 1.72/0.60  fof(f27,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f14])).
% 1.72/0.60  fof(f14,plain,(
% 1.72/0.60    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 1.72/0.60    inference(ennf_transformation,[],[f6])).
% 1.72/0.60  fof(f6,axiom,(
% 1.72/0.60    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.72/0.60  fof(f456,plain,(
% 1.72/0.60    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))),
% 1.72/0.60    inference(superposition,[],[f255,f435])).
% 1.72/0.60  fof(f435,plain,(
% 1.72/0.60    sK0 = k3_xboole_0(sK0,sK2)),
% 1.72/0.60    inference(resolution,[],[f433,f22])).
% 1.72/0.60  fof(f433,plain,(
% 1.72/0.60    r1_tarski(sK0,sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f430,f18])).
% 1.72/0.60  fof(f18,plain,(
% 1.72/0.60    k1_xboole_0 != sK1),
% 1.72/0.60    inference(cnf_transformation,[],[f12])).
% 1.72/0.60  fof(f430,plain,(
% 1.72/0.60    k1_xboole_0 = sK1 | r1_tarski(sK0,sK2)),
% 1.72/0.60    inference(resolution,[],[f406,f26])).
% 1.72/0.60  fof(f26,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f14])).
% 1.72/0.60  fof(f406,plain,(
% 1.72/0.60    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 1.72/0.60    inference(superposition,[],[f189,f347])).
% 1.72/0.60  fof(f347,plain,(
% 1.72/0.60    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 1.72/0.60    inference(backward_demodulation,[],[f304,f346])).
% 1.72/0.60  fof(f346,plain,(
% 1.72/0.60    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 1.72/0.60    inference(subsumption_resolution,[],[f344,f205])).
% 1.72/0.60  fof(f205,plain,(
% 1.72/0.60    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 1.72/0.60    inference(superposition,[],[f171,f21])).
% 1.72/0.60  fof(f171,plain,(
% 1.72/0.60    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1))) )),
% 1.72/0.60    inference(superposition,[],[f145,f16])).
% 1.72/0.60  fof(f145,plain,(
% 1.72/0.60    ( ! [X4,X2,X3] : (r1_tarski(k2_zfmisc_1(X2,k3_xboole_0(X3,X4)),k2_zfmisc_1(X2,X3))) )),
% 1.72/0.60    inference(superposition,[],[f20,f111])).
% 1.72/0.60  fof(f111,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 1.72/0.60    inference(superposition,[],[f28,f19])).
% 1.72/0.60  fof(f19,plain,(
% 1.72/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.72/0.60    inference(cnf_transformation,[],[f10])).
% 1.72/0.60  fof(f10,plain,(
% 1.72/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.72/0.60    inference(rectify,[],[f2])).
% 1.72/0.60  fof(f2,axiom,(
% 1.72/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.72/0.60  fof(f28,plain,(
% 1.72/0.60    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f7])).
% 1.72/0.60  fof(f7,axiom,(
% 1.72/0.60    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 1.72/0.60  fof(f20,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f4])).
% 1.72/0.60  fof(f4,axiom,(
% 1.72/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.72/0.60  fof(f344,plain,(
% 1.72/0.60    ~r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 1.72/0.60    inference(resolution,[],[f342,f25])).
% 1.72/0.60  fof(f25,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.72/0.60    inference(cnf_transformation,[],[f3])).
% 1.72/0.60  fof(f342,plain,(
% 1.72/0.60    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))),
% 1.72/0.60    inference(forward_demodulation,[],[f337,f16])).
% 1.72/0.60  fof(f337,plain,(
% 1.72/0.60    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))),
% 1.72/0.60    inference(superposition,[],[f330,f19])).
% 1.72/0.60  fof(f330,plain,(
% 1.72/0.60    ( ! [X8] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X8)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) )),
% 1.72/0.60    inference(forward_demodulation,[],[f329,f137])).
% 1.72/0.60  fof(f137,plain,(
% 1.72/0.60    ( ! [X0] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))) )),
% 1.72/0.60    inference(superposition,[],[f111,f16])).
% 1.72/0.60  fof(f329,plain,(
% 1.72/0.60    ( ! [X8] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X8)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) )),
% 1.72/0.60    inference(forward_demodulation,[],[f316,f28])).
% 1.72/0.60  fof(f316,plain,(
% 1.72/0.60    ( ! [X8] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X8)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) )),
% 1.72/0.60    inference(superposition,[],[f145,f304])).
% 1.72/0.60  fof(f304,plain,(
% 1.72/0.60    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 1.72/0.60    inference(forward_demodulation,[],[f286,f21])).
% 1.72/0.60  fof(f286,plain,(
% 1.72/0.60    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,sK1))),
% 1.72/0.60    inference(superposition,[],[f137,f118])).
% 1.72/0.60  fof(f118,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 1.72/0.60    inference(superposition,[],[f28,f19])).
% 1.72/0.60  fof(f189,plain,(
% 1.72/0.60    ( ! [X24,X23,X25] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X23,X25),X24),k2_zfmisc_1(X25,X24))) )),
% 1.72/0.60    inference(superposition,[],[f32,f118])).
% 1.72/0.60  fof(f32,plain,(
% 1.72/0.60    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.72/0.60    inference(superposition,[],[f20,f21])).
% 1.72/0.60  fof(f255,plain,(
% 1.72/0.60    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 1.72/0.60    inference(superposition,[],[f248,f21])).
% 1.72/0.60  fof(f248,plain,(
% 1.72/0.60    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 1.72/0.60    inference(superposition,[],[f184,f16])).
% 1.72/0.60  fof(f184,plain,(
% 1.72/0.60    ( ! [X6,X4,X5] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X4,X6),X5),k2_zfmisc_1(X4,X5))) )),
% 1.72/0.60    inference(superposition,[],[f20,f118])).
% 1.72/0.60  fof(f708,plain,(
% 1.72/0.60    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 1.72/0.60    inference(forward_demodulation,[],[f684,f21])).
% 1.72/0.60  fof(f684,plain,(
% 1.72/0.60    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK1))),
% 1.72/0.60    inference(superposition,[],[f491,f19])).
% 1.72/0.60  fof(f491,plain,(
% 1.72/0.60    ( ! [X0] : (k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,sK1))) )),
% 1.72/0.60    inference(backward_demodulation,[],[f139,f478])).
% 1.72/0.60  fof(f478,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k2_zfmisc_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,X1))) )),
% 1.72/0.60    inference(superposition,[],[f28,f466])).
% 1.72/0.60  fof(f466,plain,(
% 1.72/0.60    sK0 = k3_xboole_0(sK2,sK0)),
% 1.72/0.60    inference(superposition,[],[f58,f435])).
% 1.72/0.60  fof(f58,plain,(
% 1.72/0.60    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 1.72/0.60    inference(superposition,[],[f39,f21])).
% 1.72/0.60  fof(f39,plain,(
% 1.72/0.60    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X4)) )),
% 1.72/0.60    inference(resolution,[],[f22,f32])).
% 1.72/0.60  fof(f139,plain,(
% 1.72/0.60    ( ! [X0] : (k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1))) )),
% 1.72/0.60    inference(superposition,[],[f111,f16])).
% 1.72/0.60  fof(f442,plain,(
% 1.72/0.60    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X2)) | r1_tarski(sK1,X2)) )),
% 1.72/0.60    inference(forward_demodulation,[],[f441,f435])).
% 1.72/0.60  fof(f441,plain,(
% 1.72/0.60    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2)) | r1_tarski(sK1,X2)) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f436,f17])).
% 1.72/0.60  fof(f436,plain,(
% 1.72/0.60    ( ! [X2] : (k1_xboole_0 = sK0 | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2)) | r1_tarski(sK1,X2)) )),
% 1.72/0.60    inference(backward_demodulation,[],[f348,f435])).
% 1.72/0.60  fof(f348,plain,(
% 1.72/0.60    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2)) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | r1_tarski(sK1,X2)) )),
% 1.72/0.60    inference(backward_demodulation,[],[f310,f346])).
% 1.72/0.60  fof(f310,plain,(
% 1.72/0.60    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2)) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | r1_tarski(sK1,X2)) )),
% 1.72/0.60    inference(superposition,[],[f27,f304])).
% 1.72/0.60  fof(f501,plain,(
% 1.72/0.60    ~r1_tarski(sK1,sK3) | sK1 = sK3),
% 1.72/0.60    inference(resolution,[],[f500,f25])).
% 1.72/0.60  fof(f15,plain,(
% 1.72/0.60    sK1 != sK3 | sK0 != sK2),
% 1.72/0.60    inference(cnf_transformation,[],[f12])).
% 1.72/0.60  fof(f434,plain,(
% 1.72/0.60    ~r1_tarski(sK2,sK0) | sK0 = sK2),
% 1.72/0.60    inference(resolution,[],[f433,f25])).
% 1.72/0.60  fof(f1064,plain,(
% 1.72/0.60    r1_tarski(sK2,sK0)),
% 1.72/0.60    inference(resolution,[],[f819,f29])).
% 1.72/0.60  fof(f819,plain,(
% 1.72/0.60    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1)) | r1_tarski(sK2,X0)) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f818,f18])).
% 1.72/0.60  fof(f818,plain,(
% 1.72/0.60    ( ! [X0] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1)) | r1_tarski(sK2,X0)) )),
% 1.72/0.60    inference(forward_demodulation,[],[f754,f750])).
% 1.72/0.60  fof(f754,plain,(
% 1.72/0.60    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1)) | k1_xboole_0 = sK3 | r1_tarski(sK2,X0)) )),
% 1.72/0.60    inference(backward_demodulation,[],[f102,f750])).
% 1.72/0.60  fof(f102,plain,(
% 1.72/0.60    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | k1_xboole_0 = sK3 | r1_tarski(sK2,X0)) )),
% 1.72/0.60    inference(superposition,[],[f26,f16])).
% 1.72/0.60  % SZS output end Proof for theBenchmark
% 1.72/0.60  % (30361)------------------------------
% 1.72/0.60  % (30361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (30361)Termination reason: Refutation
% 1.72/0.60  
% 1.72/0.60  % (30361)Memory used [KB]: 2430
% 1.72/0.60  % (30361)Time elapsed: 0.173 s
% 1.72/0.60  % (30361)------------------------------
% 1.72/0.60  % (30361)------------------------------
% 1.72/0.60  % (30341)Success in time 0.238 s
%------------------------------------------------------------------------------
