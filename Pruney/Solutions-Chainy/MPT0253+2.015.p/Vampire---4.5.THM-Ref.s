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
% DateTime   : Thu Dec  3 12:39:08 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 226 expanded)
%              Number of leaves         :   16 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 321 expanded)
%              Number of equality atoms :   52 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(subsumption_resolution,[],[f407,f73])).

fof(f73,plain,(
    sK1 != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(backward_demodulation,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f53,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f55,plain,(
    sK1 != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f24,f54,f53])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f24,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f407,plain,(
    sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(forward_demodulation,[],[f406,f56])).

fof(f56,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f26,f54])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f406,plain,(
    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f398,f102])).

fof(f102,plain,(
    ! [X7] : k1_xboole_0 = k5_xboole_0(X7,X7) ),
    inference(resolution,[],[f97,f86])).

fof(f86,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f84,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f84,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f83,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f83,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f80,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f71,f74])).

fof(f74,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f32,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f95,f37])).

fof(f95,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k5_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f93,f80])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f72,f74])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f30])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f398,plain,(
    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))) ),
    inference(superposition,[],[f58,f150])).

fof(f150,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(resolution,[],[f139,f32])).

fof(f139,plain,(
    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f137,f57])).

fof(f137,plain,(
    r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),sK1) ),
    inference(resolution,[],[f134,f23])).

fof(f23,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f134,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,sK1)
      | r1_tarski(k4_enumset1(X13,X13,X13,X13,X13,sK0),sK1) ) ),
    inference(resolution,[],[f65,f22])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f31,f54,f30,f54])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.12/0.52  % (5522)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.12/0.52  % (5497)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.52  % (5507)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.53  % (5498)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.53  % (5493)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.53  % (5496)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.53  % (5499)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.54  % (5508)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.54  % (5516)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.54  % (5502)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.54  % (5506)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.54  % (5495)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.54  % (5513)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.54  % (5515)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.24/0.54  % (5518)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.54  % (5513)Refutation not found, incomplete strategy% (5513)------------------------------
% 1.24/0.54  % (5513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (5513)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (5513)Memory used [KB]: 10746
% 1.24/0.54  % (5513)Time elapsed: 0.127 s
% 1.24/0.54  % (5513)------------------------------
% 1.24/0.54  % (5513)------------------------------
% 1.24/0.55  % (5521)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.24/0.55  % (5509)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.55  % (5512)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.55  % (5511)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.55  % (5514)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.55  % (5520)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.55  % (5494)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.56  % (5514)Refutation not found, incomplete strategy% (5514)------------------------------
% 1.24/0.56  % (5514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.56  % (5514)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.56  
% 1.24/0.56  % (5514)Memory used [KB]: 1663
% 1.24/0.56  % (5514)Time elapsed: 0.139 s
% 1.24/0.56  % (5514)------------------------------
% 1.24/0.56  % (5514)------------------------------
% 1.24/0.56  % (5505)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.56  % (5501)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.56  % (5504)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.56  % (5503)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.56  % (5503)Refutation not found, incomplete strategy% (5503)------------------------------
% 1.24/0.56  % (5503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.56  % (5503)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.56  
% 1.24/0.56  % (5503)Memory used [KB]: 10618
% 1.24/0.56  % (5503)Time elapsed: 0.136 s
% 1.24/0.56  % (5503)------------------------------
% 1.24/0.56  % (5503)------------------------------
% 1.24/0.57  % (5517)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.57  % (5519)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.24/0.57  % (5515)Refutation not found, incomplete strategy% (5515)------------------------------
% 1.24/0.57  % (5515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.57  % (5515)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.57  
% 1.24/0.57  % (5515)Memory used [KB]: 10746
% 1.24/0.57  % (5515)Time elapsed: 0.158 s
% 1.24/0.57  % (5515)------------------------------
% 1.24/0.57  % (5515)------------------------------
% 1.24/0.57  % (5500)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.57  % (5510)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.58  % (5499)Refutation found. Thanks to Tanya!
% 1.24/0.58  % SZS status Theorem for theBenchmark
% 1.24/0.58  % SZS output start Proof for theBenchmark
% 1.24/0.58  fof(f408,plain,(
% 1.24/0.58    $false),
% 1.24/0.58    inference(subsumption_resolution,[],[f407,f73])).
% 1.24/0.58  fof(f73,plain,(
% 1.24/0.58    sK1 != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))),
% 1.24/0.58    inference(backward_demodulation,[],[f55,f57])).
% 1.24/0.58  fof(f57,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 1.24/0.58    inference(definition_unfolding,[],[f27,f53,f53])).
% 1.24/0.58  fof(f53,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.24/0.58    inference(definition_unfolding,[],[f29,f52])).
% 1.24/0.58  fof(f52,plain,(
% 1.24/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.24/0.58    inference(definition_unfolding,[],[f39,f51])).
% 1.24/0.58  fof(f51,plain,(
% 1.24/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.24/0.58    inference(definition_unfolding,[],[f49,f50])).
% 1.24/0.58  fof(f50,plain,(
% 1.24/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.24/0.58    inference(cnf_transformation,[],[f13])).
% 1.24/0.58  fof(f13,axiom,(
% 1.24/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.24/0.58  fof(f49,plain,(
% 1.24/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.24/0.58    inference(cnf_transformation,[],[f12])).
% 1.24/0.58  fof(f12,axiom,(
% 1.24/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.24/0.58  fof(f39,plain,(
% 1.24/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.24/0.58    inference(cnf_transformation,[],[f11])).
% 1.24/0.58  fof(f11,axiom,(
% 1.24/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.24/0.58  fof(f29,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.24/0.58    inference(cnf_transformation,[],[f10])).
% 1.24/0.58  fof(f10,axiom,(
% 1.24/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.24/0.58  fof(f27,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.24/0.58    inference(cnf_transformation,[],[f9])).
% 1.24/0.58  fof(f9,axiom,(
% 1.24/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.24/0.58  fof(f55,plain,(
% 1.24/0.58    sK1 != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1))),
% 1.24/0.58    inference(definition_unfolding,[],[f24,f54,f53])).
% 1.24/0.58  fof(f54,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.24/0.58    inference(definition_unfolding,[],[f28,f53])).
% 1.24/0.58  fof(f28,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.24/0.58    inference(cnf_transformation,[],[f14])).
% 1.24/0.58  fof(f14,axiom,(
% 1.24/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.24/0.58  fof(f24,plain,(
% 1.24/0.58    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.24/0.58    inference(cnf_transformation,[],[f19])).
% 1.24/0.58  fof(f19,plain,(
% 1.24/0.58    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.24/0.58    inference(flattening,[],[f18])).
% 1.24/0.58  fof(f18,plain,(
% 1.24/0.58    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.24/0.58    inference(ennf_transformation,[],[f17])).
% 1.24/0.58  fof(f17,negated_conjecture,(
% 1.24/0.58    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.24/0.58    inference(negated_conjecture,[],[f16])).
% 1.24/0.58  fof(f16,conjecture,(
% 1.24/0.58    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.24/0.58  fof(f407,plain,(
% 1.24/0.58    sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))),
% 1.24/0.58    inference(forward_demodulation,[],[f406,f56])).
% 1.24/0.58  fof(f56,plain,(
% 1.24/0.58    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.24/0.58    inference(definition_unfolding,[],[f26,f54])).
% 1.24/0.58  fof(f26,plain,(
% 1.24/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.58    inference(cnf_transformation,[],[f5])).
% 1.24/0.58  fof(f5,axiom,(
% 1.24/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.24/0.58  fof(f406,plain,(
% 1.24/0.58    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k1_xboole_0))),
% 1.24/0.58    inference(forward_demodulation,[],[f398,f102])).
% 1.24/0.58  fof(f102,plain,(
% 1.24/0.58    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(X7,X7)) )),
% 1.24/0.58    inference(resolution,[],[f97,f86])).
% 1.24/0.58  fof(f86,plain,(
% 1.24/0.58    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 1.24/0.58    inference(resolution,[],[f84,f35])).
% 1.24/0.58  fof(f35,plain,(
% 1.24/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.24/0.58    inference(cnf_transformation,[],[f3])).
% 1.24/0.58  fof(f3,axiom,(
% 1.24/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.58  fof(f84,plain,(
% 1.24/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.24/0.58    inference(resolution,[],[f83,f37])).
% 1.24/0.58  fof(f37,plain,(
% 1.24/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.24/0.58    inference(cnf_transformation,[],[f21])).
% 1.24/0.58  fof(f21,plain,(
% 1.24/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.24/0.58    inference(ennf_transformation,[],[f1])).
% 1.24/0.58  fof(f1,axiom,(
% 1.24/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.24/0.58  fof(f83,plain,(
% 1.24/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.24/0.58    inference(duplicate_literal_removal,[],[f82])).
% 1.24/0.58  fof(f82,plain,(
% 1.24/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.24/0.58    inference(superposition,[],[f80,f25])).
% 1.24/0.58  fof(f25,plain,(
% 1.24/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.58    inference(cnf_transformation,[],[f8])).
% 1.24/0.58  fof(f8,axiom,(
% 1.24/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.24/0.58  fof(f80,plain,(
% 1.24/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | ~r2_hidden(X1,X0)) )),
% 1.24/0.58    inference(superposition,[],[f71,f74])).
% 1.24/0.58  fof(f74,plain,(
% 1.24/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.24/0.58    inference(resolution,[],[f32,f68])).
% 1.24/0.58  fof(f68,plain,(
% 1.24/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.24/0.58    inference(equality_resolution,[],[f34])).
% 1.24/0.58  fof(f34,plain,(
% 1.24/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.24/0.58    inference(cnf_transformation,[],[f3])).
% 1.24/0.58  fof(f32,plain,(
% 1.24/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.24/0.58    inference(cnf_transformation,[],[f20])).
% 1.24/0.58  fof(f20,plain,(
% 1.24/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.24/0.58    inference(ennf_transformation,[],[f6])).
% 1.24/0.58  fof(f6,axiom,(
% 1.24/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.24/0.58  fof(f71,plain,(
% 1.24/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.24/0.58    inference(equality_resolution,[],[f60])).
% 1.24/0.58  fof(f60,plain,(
% 1.24/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.24/0.58    inference(definition_unfolding,[],[f44,f30])).
% 1.24/0.58  fof(f30,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.58    inference(cnf_transformation,[],[f4])).
% 1.24/0.58  fof(f4,axiom,(
% 1.24/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.58  fof(f44,plain,(
% 1.24/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.24/0.58    inference(cnf_transformation,[],[f2])).
% 1.24/0.58  fof(f2,axiom,(
% 1.24/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.24/0.58  fof(f97,plain,(
% 1.24/0.58    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X0),X1)) )),
% 1.24/0.58    inference(resolution,[],[f95,f37])).
% 1.24/0.58  fof(f95,plain,(
% 1.24/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0))) )),
% 1.24/0.58    inference(subsumption_resolution,[],[f93,f80])).
% 1.24/0.58  fof(f93,plain,(
% 1.24/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | r2_hidden(X1,X0)) )),
% 1.24/0.58    inference(superposition,[],[f72,f74])).
% 1.24/0.58  fof(f72,plain,(
% 1.24/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 1.24/0.58    inference(equality_resolution,[],[f61])).
% 1.24/0.58  fof(f61,plain,(
% 1.24/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.24/0.58    inference(definition_unfolding,[],[f43,f30])).
% 1.24/0.58  fof(f43,plain,(
% 1.24/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.24/0.58    inference(cnf_transformation,[],[f2])).
% 1.24/0.58  fof(f398,plain,(
% 1.24/0.58    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))))),
% 1.24/0.58    inference(superposition,[],[f58,f150])).
% 1.24/0.58  fof(f150,plain,(
% 1.24/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.24/0.58    inference(resolution,[],[f139,f32])).
% 1.24/0.58  fof(f139,plain,(
% 1.24/0.58    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 1.24/0.58    inference(forward_demodulation,[],[f137,f57])).
% 1.24/0.58  fof(f137,plain,(
% 1.24/0.58    r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),sK1)),
% 1.24/0.58    inference(resolution,[],[f134,f23])).
% 1.24/0.58  fof(f23,plain,(
% 1.24/0.58    r2_hidden(sK2,sK1)),
% 1.24/0.58    inference(cnf_transformation,[],[f19])).
% 1.24/0.58  fof(f134,plain,(
% 1.24/0.58    ( ! [X13] : (~r2_hidden(X13,sK1) | r1_tarski(k4_enumset1(X13,X13,X13,X13,X13,sK0),sK1)) )),
% 1.24/0.58    inference(resolution,[],[f65,f22])).
% 1.24/0.58  fof(f22,plain,(
% 1.24/0.58    r2_hidden(sK0,sK1)),
% 1.24/0.58    inference(cnf_transformation,[],[f19])).
% 1.24/0.58  fof(f65,plain,(
% 1.24/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 1.24/0.58    inference(definition_unfolding,[],[f48,f53])).
% 1.24/0.58  fof(f48,plain,(
% 1.24/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.24/0.58    inference(cnf_transformation,[],[f15])).
% 1.24/0.58  fof(f15,axiom,(
% 1.24/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.24/0.58  fof(f58,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.24/0.58    inference(definition_unfolding,[],[f31,f54,f30,f54])).
% 1.24/0.58  fof(f31,plain,(
% 1.24/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.24/0.58    inference(cnf_transformation,[],[f7])).
% 1.24/0.58  fof(f7,axiom,(
% 1.24/0.58    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.24/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.24/0.58  % SZS output end Proof for theBenchmark
% 1.24/0.58  % (5499)------------------------------
% 1.24/0.58  % (5499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.58  % (5499)Termination reason: Refutation
% 1.24/0.58  
% 1.24/0.58  % (5499)Memory used [KB]: 6780
% 1.24/0.58  % (5499)Time elapsed: 0.156 s
% 1.24/0.58  % (5499)------------------------------
% 1.24/0.58  % (5499)------------------------------
% 1.24/0.58  % (5492)Success in time 0.216 s
%------------------------------------------------------------------------------
