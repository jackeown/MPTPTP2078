%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:34 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 102 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  118 ( 227 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(subsumption_resolution,[],[f123,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

fof(f123,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f119,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f119,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f118,f62])).

fof(f62,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f118,plain,
    ( ~ r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f116,f61])).

fof(f61,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f94,f72])).

fof(f72,plain,(
    ~ r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f71,f29])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

% (27813)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f71,plain,
    ( ~ r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f56,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ~ m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f27,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X10,X8,X9] :
      ( r2_hidden(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X8),k1_zfmisc_1(X9))
      | ~ r2_hidden(X10,X9)
      | ~ r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f57,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f69,f66])).

fof(f66,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f63,f29])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f37,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f31,f30])).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X2))
      | r2_hidden(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.50  % (27809)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.52  % (27809)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % (27817)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.53  % (27812)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.53  % (27826)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.53  % (27806)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.53  % (27807)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f124,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(subsumption_resolution,[],[f123,f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    k1_xboole_0 != sK0),
% 0.23/0.53    inference(cnf_transformation,[],[f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.23/0.53    inference(flattening,[],[f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ? [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f17])).
% 0.23/0.53  fof(f17,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.23/0.53    inference(negated_conjecture,[],[f16])).
% 0.23/0.53  fof(f16,conjecture,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).
% 0.23/0.53  fof(f123,plain,(
% 0.23/0.53    k1_xboole_0 = sK0),
% 0.23/0.53    inference(resolution,[],[f119,f32])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f20])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.23/0.53  fof(f119,plain,(
% 0.23/0.53    v1_xboole_0(sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f118,f62])).
% 0.23/0.53  fof(f62,plain,(
% 0.23/0.53    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.23/0.53    inference(resolution,[],[f37,f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    m1_subset_1(sK1,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f19])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,axiom,(
% 0.23/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.23/0.53  fof(f118,plain,(
% 0.23/0.53    ~r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.23/0.53    inference(resolution,[],[f116,f61])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 0.23/0.53    inference(resolution,[],[f37,f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    m1_subset_1(sK2,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f19])).
% 0.23/0.53  fof(f116,plain,(
% 0.23/0.53    ~r2_hidden(sK2,sK0) | ~r2_hidden(sK1,sK0)),
% 0.23/0.53    inference(resolution,[],[f94,f72])).
% 0.23/0.53  fof(f72,plain,(
% 0.23/0.53    ~r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.23/0.53    inference(subsumption_resolution,[],[f71,f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f15])).
% 0.23/0.53  % (27813)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.53  fof(f15,axiom,(
% 0.23/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.23/0.53  fof(f71,plain,(
% 0.23/0.53    ~r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.23/0.53    inference(resolution,[],[f56,f36])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f21])).
% 0.23/0.53  fof(f56,plain,(
% 0.23/0.53    ~m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.23/0.53    inference(definition_unfolding,[],[f27,f55])).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f33,f54])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f43,f53])).
% 0.23/0.53  fof(f53,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f47,f52])).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f48,f51])).
% 0.23/0.53  fof(f51,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f49,f50])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.23/0.53    inference(cnf_transformation,[],[f19])).
% 0.23/0.53  fof(f94,plain,(
% 0.23/0.53    ( ! [X10,X8,X9] : (r2_hidden(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X8),k1_zfmisc_1(X9)) | ~r2_hidden(X10,X9) | ~r2_hidden(X8,X9)) )),
% 0.23/0.53    inference(resolution,[],[f57,f73])).
% 0.23/0.53  fof(f73,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.53    inference(resolution,[],[f69,f66])).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f63,f29])).
% 0.23/0.53  fof(f63,plain,(
% 0.23/0.53    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(resolution,[],[f37,f60])).
% 0.23/0.53  fof(f60,plain,(
% 0.23/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(forward_demodulation,[],[f31,f30])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f13])).
% 0.23/0.53  fof(f13,axiom,(
% 0.23/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,axiom,(
% 0.23/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.23/0.53  fof(f69,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X2)) | r2_hidden(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X2,X1)) )),
% 0.23/0.53    inference(resolution,[],[f39,f38])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,axiom,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.53  fof(f57,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f46,f55])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (27809)------------------------------
% 0.23/0.53  % (27809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (27809)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (27809)Memory used [KB]: 6268
% 0.23/0.53  % (27809)Time elapsed: 0.099 s
% 0.23/0.53  % (27809)------------------------------
% 0.23/0.53  % (27809)------------------------------
% 0.23/0.53  % (27802)Success in time 0.161 s
%------------------------------------------------------------------------------
