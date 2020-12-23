%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 224 expanded)
%              Number of leaves         :   15 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  142 ( 376 expanded)
%              Number of equality atoms :   79 ( 282 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28681)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f476,plain,(
    $false ),
    inference(resolution,[],[f470,f149])).

fof(f149,plain,(
    r2_hidden(sK2,k2_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(resolution,[],[f147,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK2,X1) ) ),
    inference(superposition,[],[f39,f22])).

fof(f22,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f147,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k2_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f139,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f56])).

% (28662)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f139,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_zfmisc_1(k1_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k2_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f137,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

% (28661)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f137,plain,(
    v1_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f132,f22])).

fof(f132,plain,(
    ! [X0,X1] : v1_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,k4_tarski(X0,X1))) ),
    inference(superposition,[],[f61,f22])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f470,plain,(
    ! [X4] : ~ r2_hidden(sK2,X4) ),
    inference(subsumption_resolution,[],[f469,f457])).

fof(f457,plain,(
    ! [X0] : k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(superposition,[],[f58,f57])).

fof(f57,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f23,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f54])).

fof(f27,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f26,f55,f56])).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f469,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK2,X4)
      | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ) ),
    inference(subsumption_resolution,[],[f467,f63])).

fof(f63,plain,(
    ! [X6,X2,X0,X3,X1] : r2_hidden(X6,k3_enumset1(X0,X1,X2,X3,X6)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X6) != X5 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X4 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(f467,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2,X4)
      | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ) ),
    inference(backward_demodulation,[],[f157,f461])).

fof(f461,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f458])).

% (28672)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f458,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK1 ),
    inference(superposition,[],[f457,f173])).

fof(f173,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f172,f63])).

fof(f172,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
      | sK0 = sK1 ) ),
    inference(subsumption_resolution,[],[f169,f63])).

fof(f169,plain,(
    ! [X3] :
      ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
      | ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK1,X3)
      | sK0 = sK1 ) ),
    inference(resolution,[],[f91,f96])).

fof(f96,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK0,X3)
      | ~ r2_hidden(sK1,X2)
      | sK0 = sK1 ) ),
    inference(superposition,[],[f40,f83])).

fof(f83,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f22,f81])).

fof(f81,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f80,f79])).

fof(f79,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f21,f78])).

fof(f78,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f29,f22])).

fof(f29,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f21,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f30,f22])).

fof(f30,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f91,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(X3,k3_enumset1(X2,X2,X2,X2,X2)))
      | k1_xboole_0 = k3_enumset1(X2,X2,X2,X2,X2) ) ),
    inference(resolution,[],[f60,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f56])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f157,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2,X4)
      | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ) ),
    inference(resolution,[],[f90,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f40,f22])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),X1))
      | k1_xboole_0 = k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (28680)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (28663)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (28663)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (28671)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (28670)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  % (28681)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f476,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f470,f149])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    r2_hidden(sK2,k2_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(resolution,[],[f147,f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(sK2,X1)) )),
% 0.22/0.54    inference(superposition,[],[f39,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    sK0 = k4_tarski(sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.54    inference(negated_conjecture,[],[f15])).
% 0.22/0.54  fof(f15,conjecture,(
% 0.22/0.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    r2_hidden(sK0,k2_zfmisc_1(k1_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k2_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 0.22/0.54    inference(resolution,[],[f139,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f34,f56])).
% 0.22/0.54  % (28662)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f24,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f35,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_zfmisc_1(k1_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k2_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 0.22/0.54    inference(resolution,[],[f137,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  % (28661)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    v1_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(superposition,[],[f132,f22])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k3_enumset1(sK0,sK0,sK0,sK0,k4_tarski(X0,X1)))) )),
% 0.22/0.54    inference(superposition,[],[f61,f22])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (v1_relat_1(k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f36,f54])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.22/0.54  fof(f470,plain,(
% 0.22/0.54    ( ! [X4] : (~r2_hidden(sK2,X4)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f469,f457])).
% 0.22/0.54  fof(f457,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(superposition,[],[f58,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f23,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f27,f54])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f26,f55,f56])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.54  fof(f469,plain,(
% 0.22/0.54    ( ! [X4] : (~r2_hidden(sK2,X4) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f467,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X6,X2,X0,X3,X1] : (r2_hidden(X6,k3_enumset1(X0,X1,X2,X3,X6))) )),
% 0.22/0.54    inference(equality_resolution,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X6,X2,X0,X5,X3,X1] : (r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X6) != X5) )),
% 0.22/0.54    inference(equality_resolution,[],[f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 0.22/0.54  fof(f467,plain,(
% 0.22/0.54    ( ! [X4] : (~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2,X4) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )),
% 0.22/0.54    inference(backward_demodulation,[],[f157,f461])).
% 0.22/0.54  fof(f461,plain,(
% 0.22/0.54    sK0 = sK1),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f458])).
% 0.22/0.54  % (28672)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f458,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | sK0 = sK1),
% 0.22/0.54    inference(superposition,[],[f457,f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK1),
% 0.22/0.54    inference(resolution,[],[f172,f63])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ( ! [X3] : (~r2_hidden(sK1,X3) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK1) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f169,f63])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ( ! [X3] : (k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,X3) | sK0 = sK1) )),
% 0.22/0.54    inference(resolution,[],[f91,f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK0,X3) | ~r2_hidden(sK1,X2) | sK0 = sK1) )),
% 0.22/0.54    inference(superposition,[],[f40,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    sK0 = k4_tarski(sK1,sK0) | sK0 = sK1),
% 0.22/0.54    inference(superposition,[],[f22,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    sK0 = sK2 | sK0 = sK1),
% 0.22/0.54    inference(superposition,[],[f80,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.22/0.54    inference(backward_demodulation,[],[f21,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    sK1 = k1_mcart_1(sK0)),
% 0.22/0.54    inference(superposition,[],[f29,f22])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    sK2 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(superposition,[],[f30,f22])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k3_enumset1(X2,X2,X2,X2,X2))) | k1_xboole_0 = k3_enumset1(X2,X2,X2,X2,X2)) )),
% 0.22/0.54    inference(resolution,[],[f60,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f33,f56])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ( ! [X4] : (~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2,X4) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f90,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK2,X1) | ~r2_hidden(sK1,X0)) )),
% 0.22/0.54    inference(superposition,[],[f40,f22])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),X1)) | k1_xboole_0 = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f60,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (28663)------------------------------
% 0.22/0.54  % (28663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28663)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (28663)Memory used [KB]: 6396
% 0.22/0.54  % (28663)Time elapsed: 0.101 s
% 0.22/0.54  % (28663)------------------------------
% 0.22/0.54  % (28663)------------------------------
% 0.22/0.54  % (28684)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (28656)Success in time 0.175 s
%------------------------------------------------------------------------------
