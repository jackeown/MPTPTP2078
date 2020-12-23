%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  52 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 ( 144 expanded)
%              Number of equality atoms :   51 ( 133 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f58,f51])).

fof(f51,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f37,f10])).

fof(f10,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f37,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f26,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f26,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f12,f8])).

fof(f8,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f58,plain,(
    ! [X5] : sK1 != k1_tarski(X5) ),
    inference(subsumption_resolution,[],[f57,f9])).

fof(f9,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X5] :
      ( sK1 != k1_tarski(X5)
      | sK1 = sK2 ) ),
    inference(inner_rewriting,[],[f52])).

fof(f52,plain,(
    ! [X5] :
      ( sK1 != k1_tarski(X5)
      | sK2 = k1_tarski(X5) ) ),
    inference(backward_demodulation,[],[f36,f51])).

fof(f36,plain,(
    ! [X5] :
      ( k1_tarski(sK0) != k1_tarski(X5)
      | sK2 = k1_tarski(X5) ) ),
    inference(subsumption_resolution,[],[f32,f11])).

fof(f11,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X5] :
      ( k1_tarski(sK0) != k1_tarski(X5)
      | sK2 = k1_tarski(X5)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f21,f8])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:38:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (9149)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (9137)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (9149)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (9141)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    sK1 != sK1),
% 0.21/0.48    inference(superposition,[],[f58,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    sK1 = k1_tarski(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f37,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 0.21/0.48    inference(resolution,[],[f26,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r1_tarski(sK1,k1_tarski(sK0))),
% 0.21/0.48    inference(superposition,[],[f12,f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X5] : (sK1 != k1_tarski(X5)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    sK1 != sK2),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X5] : (sK1 != k1_tarski(X5) | sK1 = sK2) )),
% 0.21/0.48    inference(inner_rewriting,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X5] : (sK1 != k1_tarski(X5) | sK2 = k1_tarski(X5)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f36,f51])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X5] : (k1_tarski(sK0) != k1_tarski(X5) | sK2 = k1_tarski(X5)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f32,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    k1_xboole_0 != sK2),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X5] : (k1_tarski(sK0) != k1_tarski(X5) | sK2 = k1_tarski(X5) | k1_xboole_0 = sK2) )),
% 0.21/0.48    inference(superposition,[],[f21,f8])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9149)------------------------------
% 0.21/0.48  % (9149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9149)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9149)Memory used [KB]: 1663
% 0.21/0.48  % (9149)Time elapsed: 0.054 s
% 0.21/0.48  % (9149)------------------------------
% 0.21/0.48  % (9149)------------------------------
% 0.21/0.48  % (9135)Success in time 0.116 s
%------------------------------------------------------------------------------
