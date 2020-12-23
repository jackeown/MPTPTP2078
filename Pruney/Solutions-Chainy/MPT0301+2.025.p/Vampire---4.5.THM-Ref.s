%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:55 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   80 (1034 expanded)
%              Number of leaves         :   14 ( 325 expanded)
%              Depth                    :   27
%              Number of atoms          :  153 (1335 expanded)
%              Number of equality atoms :   89 ( 934 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f717,plain,(
    $false ),
    inference(subsumption_resolution,[],[f715,f230])).

% (21412)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f230,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4) ),
    inference(resolution,[],[f115,f110])).

fof(f110,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(superposition,[],[f102,f75])).

fof(f75,plain,(
    ! [X1] : k5_xboole_0(X1,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = X1 ),
    inference(superposition,[],[f55,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f25,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f102,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))))) ),
    inference(resolution,[],[f65,f24])).

fof(f24,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ) ),
    inference(backward_demodulation,[],[f57,f32])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f54])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f115,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK3(k1_xboole_0,X8,X9),X9)
      | k2_zfmisc_1(k1_xboole_0,X8) = X9 ) ),
    inference(resolution,[],[f110,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f715,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(trivial_inequality_removal,[],[f714])).

fof(f714,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f64,f712])).

fof(f712,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f711,f396])).

fof(f396,plain,(
    ! [X12] : k1_xboole_0 = k2_zfmisc_1(X12,k1_xboole_0) ),
    inference(forward_demodulation,[],[f234,f230])).

fof(f234,plain,(
    ! [X12,X11] : k2_zfmisc_1(k1_xboole_0,X11) = k2_zfmisc_1(X12,k1_xboole_0) ),
    inference(resolution,[],[f115,f114])).

fof(f114,plain,(
    ! [X6,X7] : ~ r2_hidden(X6,k2_zfmisc_1(X7,k1_xboole_0)) ),
    inference(resolution,[],[f110,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f711,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f710])).

fof(f710,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f63,f706])).

fof(f706,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f697])).

fof(f697,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f693,f251])).

fof(f251,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK3(k1_xboole_0,X8,X9),X9)
      | k1_xboole_0 = X9 ) ),
    inference(backward_demodulation,[],[f115,f230])).

fof(f693,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(forward_demodulation,[],[f692,f75])).

fof(f692,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ) ),
    inference(resolution,[],[f691,f65])).

fof(f691,plain,
    ( r1_xboole_0(sK1,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f682])).

fof(f682,plain,
    ( r1_xboole_0(sK1,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f678,f251])).

fof(f678,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_xboole_0(sK1,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f675,f110])).

% (21424)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f675,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK2(sK1,sK1)),k1_xboole_0)
      | ~ r2_hidden(X0,sK0)
      | r1_xboole_0(sK1,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f206,f23])).

fof(f23,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,sK2(X0,X0)),k2_zfmisc_1(X2,X0))
      | ~ r2_hidden(X1,X2)
      | r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f205,f59])).

fof(f59,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f205,plain,(
    ! [X3] :
      ( r2_hidden(sK2(X3,X3),X3)
      | r1_xboole_0(X3,X3) ) ),
    inference(superposition,[],[f66,f75])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))
      | r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f56,f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(definition_unfolding,[],[f30,f54])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:17:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (21425)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (21417)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (21419)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (21409)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (21416)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (21425)Refutation not found, incomplete strategy% (21425)------------------------------
% 0.22/0.52  % (21425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21427)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (21411)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (21425)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21425)Memory used [KB]: 10746
% 0.22/0.52  % (21425)Time elapsed: 0.063 s
% 0.22/0.52  % (21425)------------------------------
% 0.22/0.52  % (21425)------------------------------
% 0.22/0.52  % (21411)Refutation not found, incomplete strategy% (21411)------------------------------
% 0.22/0.52  % (21411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21411)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21411)Memory used [KB]: 10746
% 0.22/0.52  % (21411)Time elapsed: 0.100 s
% 0.22/0.52  % (21411)------------------------------
% 0.22/0.52  % (21411)------------------------------
% 0.22/0.53  % (21407)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (21406)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (21405)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (21404)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (21426)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (21405)Refutation not found, incomplete strategy% (21405)------------------------------
% 0.22/0.54  % (21405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21405)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21405)Memory used [KB]: 10618
% 0.22/0.54  % (21405)Time elapsed: 0.120 s
% 0.22/0.54  % (21405)------------------------------
% 0.22/0.54  % (21405)------------------------------
% 0.22/0.54  % (21431)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (21403)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (21407)Refutation not found, incomplete strategy% (21407)------------------------------
% 0.22/0.54  % (21407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21423)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (21414)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (21408)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (21418)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (21415)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (21407)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21407)Memory used [KB]: 6140
% 0.22/0.55  % (21407)Time elapsed: 0.126 s
% 0.22/0.55  % (21407)------------------------------
% 0.22/0.55  % (21407)------------------------------
% 0.22/0.55  % (21403)Refutation not found, incomplete strategy% (21403)------------------------------
% 0.22/0.55  % (21403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21403)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21403)Memory used [KB]: 1663
% 0.22/0.55  % (21403)Time elapsed: 0.134 s
% 0.22/0.55  % (21403)------------------------------
% 0.22/0.55  % (21403)------------------------------
% 0.22/0.55  % (21420)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (21421)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (21429)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (21410)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.55  % (21430)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.55  % (21428)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.55  % (21413)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.55  % (21428)Refutation not found, incomplete strategy% (21428)------------------------------
% 1.47/0.55  % (21428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (21428)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (21428)Memory used [KB]: 6268
% 1.47/0.55  % (21428)Time elapsed: 0.137 s
% 1.47/0.55  % (21428)------------------------------
% 1.47/0.55  % (21428)------------------------------
% 1.47/0.56  % (21409)Refutation found. Thanks to Tanya!
% 1.47/0.56  % SZS status Theorem for theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f717,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(subsumption_resolution,[],[f715,f230])).
% 1.47/0.56  % (21412)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.56  fof(f230,plain,(
% 1.47/0.56    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) )),
% 1.47/0.56    inference(resolution,[],[f115,f110])).
% 1.47/0.56  fof(f110,plain,(
% 1.47/0.56    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 1.47/0.56    inference(superposition,[],[f102,f75])).
% 1.47/0.56  fof(f75,plain,(
% 1.47/0.56    ( ! [X1] : (k5_xboole_0(X1,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = X1) )),
% 1.47/0.56    inference(superposition,[],[f55,f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.47/0.56    inference(definition_unfolding,[],[f25,f54])).
% 1.47/0.56  fof(f54,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f28,f53])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f26,f52])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f27,f51])).
% 1.47/0.56  fof(f51,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f31,f50])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f41,f49])).
% 1.47/0.56  fof(f49,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f45,f48])).
% 1.47/0.56  fof(f48,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f46,f47])).
% 1.47/0.56  fof(f47,plain,(
% 1.47/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f11])).
% 1.47/0.56  fof(f11,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f6])).
% 1.47/0.56  fof(f6,axiom,(
% 1.47/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f13])).
% 1.47/0.56  fof(f13,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f5])).
% 1.47/0.56  fof(f5,axiom,(
% 1.47/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f17])).
% 1.47/0.56  fof(f17,plain,(
% 1.47/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.47/0.56    inference(rectify,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.47/0.56  fof(f102,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)))))) )),
% 1.47/0.56    inference(resolution,[],[f65,f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.47/0.56  fof(f65,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 1.47/0.56    inference(backward_demodulation,[],[f57,f32])).
% 1.47/0.56  fof(f57,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f29,f54])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f18])).
% 1.47/0.56  fof(f18,plain,(
% 1.47/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(rectify,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.47/0.56  fof(f115,plain,(
% 1.47/0.56    ( ! [X8,X9] : (r2_hidden(sK3(k1_xboole_0,X8,X9),X9) | k2_zfmisc_1(k1_xboole_0,X8) = X9) )),
% 1.47/0.56    inference(resolution,[],[f110,f34])).
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.47/0.56  fof(f715,plain,(
% 1.47/0.56    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.47/0.56    inference(trivial_inequality_removal,[],[f714])).
% 1.47/0.56  fof(f714,plain,(
% 1.47/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.47/0.56    inference(backward_demodulation,[],[f64,f712])).
% 1.47/0.56  fof(f712,plain,(
% 1.47/0.56    k1_xboole_0 = sK0),
% 1.47/0.56    inference(subsumption_resolution,[],[f711,f396])).
% 1.47/0.56  fof(f396,plain,(
% 1.47/0.56    ( ! [X12] : (k1_xboole_0 = k2_zfmisc_1(X12,k1_xboole_0)) )),
% 1.47/0.56    inference(forward_demodulation,[],[f234,f230])).
% 1.47/0.56  fof(f234,plain,(
% 1.47/0.56    ( ! [X12,X11] : (k2_zfmisc_1(k1_xboole_0,X11) = k2_zfmisc_1(X12,k1_xboole_0)) )),
% 1.47/0.56    inference(resolution,[],[f115,f114])).
% 1.47/0.56  fof(f114,plain,(
% 1.47/0.56    ( ! [X6,X7] : (~r2_hidden(X6,k2_zfmisc_1(X7,k1_xboole_0))) )),
% 1.47/0.56    inference(resolution,[],[f110,f61])).
% 1.47/0.56  fof(f61,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.47/0.56    inference(equality_resolution,[],[f38])).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f711,plain,(
% 1.47/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.47/0.56    inference(trivial_inequality_removal,[],[f710])).
% 1.47/0.56  fof(f710,plain,(
% 1.47/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.47/0.56    inference(superposition,[],[f63,f706])).
% 1.47/0.56  fof(f706,plain,(
% 1.47/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f697])).
% 1.47/0.56  fof(f697,plain,(
% 1.47/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.47/0.56    inference(resolution,[],[f693,f251])).
% 1.47/0.56  fof(f251,plain,(
% 1.47/0.56    ( ! [X8,X9] : (r2_hidden(sK3(k1_xboole_0,X8,X9),X9) | k1_xboole_0 = X9) )),
% 1.47/0.56    inference(backward_demodulation,[],[f115,f230])).
% 1.47/0.56  fof(f693,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.47/0.56    inference(forward_demodulation,[],[f692,f75])).
% 1.47/0.56  fof(f692,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) )),
% 1.47/0.56    inference(resolution,[],[f691,f65])).
% 1.47/0.56  fof(f691,plain,(
% 1.47/0.56    r1_xboole_0(sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f682])).
% 1.47/0.56  fof(f682,plain,(
% 1.47/0.56    r1_xboole_0(sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.47/0.56    inference(resolution,[],[f678,f251])).
% 1.47/0.56  fof(f678,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_xboole_0(sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f675,f110])).
% 1.47/0.56  % (21424)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.56  fof(f675,plain,(
% 1.47/0.56    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK2(sK1,sK1)),k1_xboole_0) | ~r2_hidden(X0,sK0) | r1_xboole_0(sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.47/0.56    inference(superposition,[],[f206,f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.47/0.56    inference(cnf_transformation,[],[f19])).
% 1.47/0.56  fof(f19,plain,(
% 1.47/0.56    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.47/0.56    inference(negated_conjecture,[],[f15])).
% 1.47/0.56  fof(f15,conjecture,(
% 1.47/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.47/0.56  fof(f206,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,sK2(X0,X0)),k2_zfmisc_1(X2,X0)) | ~r2_hidden(X1,X2) | r1_xboole_0(X0,X0)) )),
% 1.47/0.56    inference(resolution,[],[f205,f59])).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    ( ! [X4,X0,X5,X1] : (~r2_hidden(X5,X1) | ~r2_hidden(X4,X0) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 1.47/0.56    inference(equality_resolution,[],[f58])).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.47/0.56    inference(equality_resolution,[],[f40])).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f205,plain,(
% 1.47/0.56    ( ! [X3] : (r2_hidden(sK2(X3,X3),X3) | r1_xboole_0(X3,X3)) )),
% 1.47/0.56    inference(superposition,[],[f66,f75])).
% 1.47/0.56  fof(f66,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) | r1_xboole_0(X0,X1)) )),
% 1.47/0.56    inference(backward_demodulation,[],[f56,f32])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f30,f54])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  fof(f63,plain,(
% 1.47/0.56    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.47/0.56    inference(inner_rewriting,[],[f22])).
% 1.47/0.56  fof(f22,plain,(
% 1.47/0.56    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f19])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.47/0.56    inference(inner_rewriting,[],[f21])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f19])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (21409)------------------------------
% 1.47/0.56  % (21409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21409)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (21409)Memory used [KB]: 6652
% 1.47/0.56  % (21409)Time elapsed: 0.100 s
% 1.47/0.56  % (21409)------------------------------
% 1.47/0.56  % (21409)------------------------------
% 1.47/0.56  % (21423)Refutation not found, incomplete strategy% (21423)------------------------------
% 1.47/0.56  % (21423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21423)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (21423)Memory used [KB]: 10746
% 1.47/0.56  % (21423)Time elapsed: 0.148 s
% 1.47/0.56  % (21423)------------------------------
% 1.47/0.56  % (21423)------------------------------
% 1.47/0.56  % (21413)Refutation not found, incomplete strategy% (21413)------------------------------
% 1.47/0.56  % (21413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21413)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (21413)Memory used [KB]: 10618
% 1.47/0.56  % (21413)Time elapsed: 0.139 s
% 1.47/0.56  % (21413)------------------------------
% 1.47/0.56  % (21413)------------------------------
% 1.47/0.56  % (21412)Refutation not found, incomplete strategy% (21412)------------------------------
% 1.47/0.56  % (21412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21412)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (21412)Memory used [KB]: 10618
% 1.47/0.56  % (21412)Time elapsed: 0.149 s
% 1.47/0.56  % (21412)------------------------------
% 1.47/0.56  % (21412)------------------------------
% 1.47/0.56  % (21422)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.56  % (21424)Refutation not found, incomplete strategy% (21424)------------------------------
% 1.47/0.56  % (21424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21424)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (21424)Memory used [KB]: 1663
% 1.47/0.56  % (21424)Time elapsed: 0.150 s
% 1.47/0.56  % (21424)------------------------------
% 1.47/0.56  % (21424)------------------------------
% 1.47/0.56  % (21420)Refutation not found, incomplete strategy% (21420)------------------------------
% 1.47/0.56  % (21420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21420)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (21420)Memory used [KB]: 10618
% 1.47/0.56  % (21420)Time elapsed: 0.147 s
% 1.47/0.56  % (21420)------------------------------
% 1.47/0.56  % (21420)------------------------------
% 1.47/0.56  % (21432)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.47/0.56  % (21414)Refutation not found, incomplete strategy% (21414)------------------------------
% 1.47/0.56  % (21414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21414)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (21414)Memory used [KB]: 10618
% 1.47/0.56  % (21414)Time elapsed: 0.148 s
% 1.47/0.56  % (21414)------------------------------
% 1.47/0.56  % (21414)------------------------------
% 1.47/0.56  % (21418)Refutation not found, incomplete strategy% (21418)------------------------------
% 1.47/0.56  % (21418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21418)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (21418)Memory used [KB]: 6140
% 1.47/0.56  % (21418)Time elapsed: 0.003 s
% 1.47/0.56  % (21418)------------------------------
% 1.47/0.56  % (21418)------------------------------
% 1.47/0.57  % (21402)Success in time 0.195 s
%------------------------------------------------------------------------------
