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
% DateTime   : Thu Dec  3 12:40:06 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 281 expanded)
%              Number of leaves         :   15 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          :  115 ( 369 expanded)
%              Number of equality atoms :   62 ( 229 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1706,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1705,f106])).

fof(f106,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f42,f30])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( r2_hidden(sK0,sK1)
    & r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) )
   => ( r2_hidden(sK0,sK1)
      & r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,X1)
      & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_hidden(X0,X1)
          & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
     => ~ r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f1705,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(forward_demodulation,[],[f1672,f61])).

fof(f61,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f54,f33])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f54,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f37,f49])).

fof(f49,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1672,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f38,f1603])).

fof(f1603,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f1598,f571])).

fof(f571,plain,(
    r1_xboole_0(k3_xboole_0(k1_tarski(sK0),sK1),k3_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f566,f62])).

fof(f62,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f55,f61])).

fof(f55,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(k3_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f37,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f41,f34])).

fof(f566,plain,(
    r1_xboole_0(k3_xboole_0(k3_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(superposition,[],[f209,f33])).

fof(f209,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(X0,k1_tarski(sK0)),k3_xboole_0(X0,k3_xboole_0(k1_tarski(sK0),sK1))) ),
    inference(resolution,[],[f200,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f200,plain,(
    r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(superposition,[],[f196,f33])).

fof(f196,plain,(
    ! [X13] : r1_xboole_0(k3_xboole_0(X13,k1_tarski(sK0)),k3_xboole_0(X13,sK1)) ),
    inference(resolution,[],[f44,f29])).

fof(f29,plain,(
    r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1598,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(trivial_inequality_removal,[],[f1584])).

fof(f1584,plain,(
    ! [X0] :
      ( X0 != X0
      | ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f1002,f706])).

fof(f706,plain,(
    ! [X10] : k2_xboole_0(X10,X10) = X10 ),
    inference(superposition,[],[f693,f61])).

fof(f693,plain,(
    ! [X17,X16] : k2_xboole_0(X16,k4_xboole_0(X16,X17)) = X16 ),
    inference(forward_demodulation,[],[f692,f61])).

fof(f692,plain,(
    ! [X17,X16] : k4_xboole_0(X16,k1_xboole_0) = k2_xboole_0(X16,k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f678,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f53,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f37,f31])).

fof(f678,plain,(
    ! [X17,X16] : k4_xboole_0(X16,k3_xboole_0(k1_xboole_0,X17)) = k2_xboole_0(X16,k4_xboole_0(X16,X17)) ),
    inference(superposition,[],[f43,f61])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f1002,plain,(
    ! [X23,X22] :
      ( k2_xboole_0(X23,X22) != X22
      | ~ r1_xboole_0(X23,X22)
      | k1_xboole_0 = X23 ) ),
    inference(subsumption_resolution,[],[f982,f47])).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f35,f31])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f982,plain,(
    ! [X23,X22] :
      ( k2_xboole_0(X23,X22) != X22
      | ~ r1_xboole_0(X23,X22)
      | ~ r1_xboole_0(k1_xboole_0,X22)
      | k1_xboole_0 = X23 ) ),
    inference(superposition,[],[f45,f722])).

fof(f722,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f303,f707])).

fof(f707,plain,(
    ! [X10] : k5_xboole_0(k5_xboole_0(X10,k1_xboole_0),k1_xboole_0) = X10 ),
    inference(backward_demodulation,[],[f293,f700])).

fof(f700,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f693,f49])).

fof(f293,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X10,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f39,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f67,f49])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f37,f61])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f303,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f290,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f290,plain,(
    ! [X5] : k2_xboole_0(k1_xboole_0,X5) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X5),k1_xboole_0) ),
    inference(superposition,[],[f39,f60])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:43:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (28170)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.49  % (28178)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (28159)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (28164)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28163)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (28162)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (28166)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (28158)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (28153)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (28174)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (28157)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (28156)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28155)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (28154)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (28175)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28154)Refutation not found, incomplete strategy% (28154)------------------------------
% 0.21/0.54  % (28154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28154)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28154)Memory used [KB]: 10618
% 0.21/0.54  % (28154)Time elapsed: 0.126 s
% 0.21/0.54  % (28154)------------------------------
% 0.21/0.54  % (28154)------------------------------
% 0.21/0.54  % (28174)Refutation not found, incomplete strategy% (28174)------------------------------
% 0.21/0.54  % (28174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28174)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28174)Memory used [KB]: 10618
% 0.21/0.54  % (28174)Time elapsed: 0.100 s
% 0.21/0.54  % (28174)------------------------------
% 0.21/0.54  % (28174)------------------------------
% 1.44/0.54  % (28161)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.44/0.54  % (28167)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.54  % (28177)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.54  % (28181)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.55  % (28152)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.55  % (28171)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (28176)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.55  % (28180)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.55  % (28160)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.55  % (28168)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.55  % (28169)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.55  % (28172)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (28169)Refutation not found, incomplete strategy% (28169)------------------------------
% 1.44/0.55  % (28169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (28179)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.54/0.56  % (28160)Refutation not found, incomplete strategy% (28160)------------------------------
% 1.54/0.56  % (28160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (28160)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (28160)Memory used [KB]: 10618
% 1.54/0.56  % (28160)Time elapsed: 0.149 s
% 1.54/0.56  % (28160)------------------------------
% 1.54/0.56  % (28160)------------------------------
% 1.54/0.56  % (28173)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.54/0.57  % (28169)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (28169)Memory used [KB]: 10618
% 1.54/0.57  % (28169)Time elapsed: 0.154 s
% 1.54/0.57  % (28169)------------------------------
% 1.54/0.57  % (28169)------------------------------
% 1.54/0.57  % (28165)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.54/0.60  % (28159)Refutation found. Thanks to Tanya!
% 1.54/0.60  % SZS status Theorem for theBenchmark
% 1.54/0.61  % SZS output start Proof for theBenchmark
% 1.54/0.61  fof(f1706,plain,(
% 1.54/0.61    $false),
% 1.54/0.61    inference(subsumption_resolution,[],[f1705,f106])).
% 1.54/0.62  fof(f106,plain,(
% 1.54/0.62    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.62    inference(resolution,[],[f42,f30])).
% 1.54/0.62  fof(f30,plain,(
% 1.54/0.62    r2_hidden(sK0,sK1)),
% 1.54/0.62    inference(cnf_transformation,[],[f28])).
% 1.54/0.62  fof(f28,plain,(
% 1.54/0.62    r2_hidden(sK0,sK1) & r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f27])).
% 1.54/0.62  fof(f27,plain,(
% 1.54/0.62    ? [X0,X1] : (r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1)) => (r2_hidden(sK0,sK1) & r1_xboole_0(k1_tarski(sK0),sK1))),
% 1.54/0.62    introduced(choice_axiom,[])).
% 1.54/0.62  fof(f21,plain,(
% 1.54/0.62    ? [X0,X1] : (r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.54/0.62    inference(ennf_transformation,[],[f17])).
% 1.54/0.62  fof(f17,negated_conjecture,(
% 1.54/0.62    ~! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.54/0.62    inference(negated_conjecture,[],[f16])).
% 1.54/0.62  fof(f16,conjecture,(
% 1.54/0.62    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).
% 1.54/0.62  fof(f42,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f23])).
% 1.54/0.62  fof(f23,plain,(
% 1.54/0.62    ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1))),
% 1.54/0.62    inference(ennf_transformation,[],[f19])).
% 1.54/0.62  fof(f19,plain,(
% 1.54/0.62    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) => ~r2_hidden(X0,X1))),
% 1.54/0.62    inference(unused_predicate_definition_removal,[],[f15])).
% 1.54/0.62  fof(f15,axiom,(
% 1.54/0.62    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.54/0.62  fof(f1705,plain,(
% 1.54/0.62    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.62    inference(forward_demodulation,[],[f1672,f61])).
% 1.54/0.62  fof(f61,plain,(
% 1.54/0.62    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.54/0.62    inference(forward_demodulation,[],[f54,f33])).
% 1.54/0.62  fof(f33,plain,(
% 1.54/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.62    inference(cnf_transformation,[],[f18])).
% 1.54/0.62  fof(f18,plain,(
% 1.54/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.62    inference(rectify,[],[f2])).
% 1.54/0.62  fof(f2,axiom,(
% 1.54/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.54/0.62  fof(f54,plain,(
% 1.54/0.62    ( ! [X1] : (k3_xboole_0(X1,X1) = k4_xboole_0(X1,k1_xboole_0)) )),
% 1.54/0.62    inference(superposition,[],[f37,f49])).
% 1.54/0.62  fof(f49,plain,(
% 1.54/0.62    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 1.54/0.62    inference(resolution,[],[f41,f46])).
% 1.54/0.62  fof(f46,plain,(
% 1.54/0.62    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.54/0.62    inference(superposition,[],[f34,f33])).
% 1.54/0.62  fof(f34,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f4])).
% 1.54/0.62  fof(f4,axiom,(
% 1.54/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.54/0.62  fof(f41,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.54/0.62    inference(cnf_transformation,[],[f22])).
% 1.54/0.62  fof(f22,plain,(
% 1.54/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.54/0.62    inference(ennf_transformation,[],[f20])).
% 1.54/0.62  fof(f20,plain,(
% 1.54/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 1.54/0.62    inference(unused_predicate_definition_removal,[],[f3])).
% 1.54/0.62  fof(f3,axiom,(
% 1.54/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.54/0.62  fof(f37,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f6])).
% 1.54/0.62  fof(f6,axiom,(
% 1.54/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.54/0.62  fof(f1672,plain,(
% 1.54/0.62    k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 1.54/0.62    inference(superposition,[],[f38,f1603])).
% 1.54/0.62  fof(f1603,plain,(
% 1.54/0.62    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.62    inference(resolution,[],[f1598,f571])).
% 1.54/0.62  fof(f571,plain,(
% 1.54/0.62    r1_xboole_0(k3_xboole_0(k1_tarski(sK0),sK1),k3_xboole_0(k1_tarski(sK0),sK1))),
% 1.54/0.62    inference(forward_demodulation,[],[f566,f62])).
% 1.54/0.62  fof(f62,plain,(
% 1.54/0.62    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 1.54/0.62    inference(forward_demodulation,[],[f55,f61])).
% 1.54/0.62  fof(f55,plain,(
% 1.54/0.62    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(k3_xboole_0(X2,X3),k1_xboole_0)) )),
% 1.54/0.62    inference(superposition,[],[f37,f48])).
% 1.54/0.62  fof(f48,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 1.54/0.62    inference(resolution,[],[f41,f34])).
% 1.54/0.62  fof(f566,plain,(
% 1.54/0.62    r1_xboole_0(k3_xboole_0(k3_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),sK1))),
% 1.54/0.62    inference(superposition,[],[f209,f33])).
% 1.54/0.62  fof(f209,plain,(
% 1.54/0.62    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,k1_tarski(sK0)),k3_xboole_0(X0,k3_xboole_0(k1_tarski(sK0),sK1)))) )),
% 1.54/0.62    inference(resolution,[],[f200,f44])).
% 1.54/0.62  fof(f44,plain,(
% 1.54/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f24])).
% 1.54/0.62  fof(f24,plain,(
% 1.54/0.62    ! [X0,X1,X2] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 1.54/0.62    inference(ennf_transformation,[],[f10])).
% 1.54/0.62  fof(f10,axiom,(
% 1.54/0.62    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).
% 1.54/0.62  fof(f200,plain,(
% 1.54/0.62    r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK1))),
% 1.54/0.62    inference(superposition,[],[f196,f33])).
% 1.54/0.62  fof(f196,plain,(
% 1.54/0.62    ( ! [X13] : (r1_xboole_0(k3_xboole_0(X13,k1_tarski(sK0)),k3_xboole_0(X13,sK1))) )),
% 1.54/0.62    inference(resolution,[],[f44,f29])).
% 1.54/0.62  fof(f29,plain,(
% 1.54/0.62    r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.62    inference(cnf_transformation,[],[f28])).
% 1.54/0.62  fof(f1598,plain,(
% 1.54/0.62    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.54/0.62    inference(trivial_inequality_removal,[],[f1584])).
% 1.54/0.62  fof(f1584,plain,(
% 1.54/0.62    ( ! [X0] : (X0 != X0 | ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.54/0.62    inference(superposition,[],[f1002,f706])).
% 1.54/0.62  fof(f706,plain,(
% 1.54/0.62    ( ! [X10] : (k2_xboole_0(X10,X10) = X10) )),
% 1.54/0.62    inference(superposition,[],[f693,f61])).
% 1.54/0.62  fof(f693,plain,(
% 1.54/0.62    ( ! [X17,X16] : (k2_xboole_0(X16,k4_xboole_0(X16,X17)) = X16) )),
% 1.54/0.62    inference(forward_demodulation,[],[f692,f61])).
% 1.54/0.62  fof(f692,plain,(
% 1.54/0.62    ( ! [X17,X16] : (k4_xboole_0(X16,k1_xboole_0) = k2_xboole_0(X16,k4_xboole_0(X16,X17))) )),
% 1.54/0.62    inference(forward_demodulation,[],[f678,f60])).
% 1.54/0.62  fof(f60,plain,(
% 1.54/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.62    inference(forward_demodulation,[],[f53,f31])).
% 1.54/0.62  fof(f31,plain,(
% 1.54/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f7])).
% 1.54/0.62  fof(f7,axiom,(
% 1.54/0.62    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.54/0.62  fof(f53,plain,(
% 1.54/0.62    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.62    inference(superposition,[],[f37,f31])).
% 1.54/0.62  fof(f678,plain,(
% 1.54/0.62    ( ! [X17,X16] : (k4_xboole_0(X16,k3_xboole_0(k1_xboole_0,X17)) = k2_xboole_0(X16,k4_xboole_0(X16,X17))) )),
% 1.54/0.62    inference(superposition,[],[f43,f61])).
% 1.54/0.62  fof(f43,plain,(
% 1.54/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f8])).
% 1.54/0.62  fof(f8,axiom,(
% 1.54/0.62    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).
% 1.54/0.62  fof(f1002,plain,(
% 1.54/0.62    ( ! [X23,X22] : (k2_xboole_0(X23,X22) != X22 | ~r1_xboole_0(X23,X22) | k1_xboole_0 = X23) )),
% 1.54/0.62    inference(subsumption_resolution,[],[f982,f47])).
% 1.54/0.62  fof(f47,plain,(
% 1.54/0.62    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.62    inference(superposition,[],[f35,f31])).
% 1.54/0.62  fof(f35,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f11])).
% 1.54/0.62  fof(f11,axiom,(
% 1.54/0.62    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.54/0.62  fof(f982,plain,(
% 1.54/0.62    ( ! [X23,X22] : (k2_xboole_0(X23,X22) != X22 | ~r1_xboole_0(X23,X22) | ~r1_xboole_0(k1_xboole_0,X22) | k1_xboole_0 = X23) )),
% 1.54/0.62    inference(superposition,[],[f45,f722])).
% 1.54/0.62  fof(f722,plain,(
% 1.54/0.62    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.62    inference(backward_demodulation,[],[f303,f707])).
% 1.54/0.62  fof(f707,plain,(
% 1.54/0.62    ( ! [X10] : (k5_xboole_0(k5_xboole_0(X10,k1_xboole_0),k1_xboole_0) = X10) )),
% 1.54/0.62    inference(backward_demodulation,[],[f293,f700])).
% 1.54/0.62  fof(f700,plain,(
% 1.54/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.62    inference(superposition,[],[f693,f49])).
% 1.54/0.62  fof(f293,plain,(
% 1.54/0.62    ( ! [X10] : (k2_xboole_0(X10,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X10,k1_xboole_0),k1_xboole_0)) )),
% 1.54/0.62    inference(superposition,[],[f39,f70])).
% 1.54/0.62  fof(f70,plain,(
% 1.54/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.54/0.62    inference(forward_demodulation,[],[f67,f49])).
% 1.54/0.62  fof(f67,plain,(
% 1.54/0.62    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.54/0.62    inference(superposition,[],[f37,f61])).
% 1.54/0.62  fof(f39,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f12])).
% 1.54/0.62  fof(f12,axiom,(
% 1.54/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.54/0.62  fof(f303,plain,(
% 1.54/0.62    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 1.54/0.62    inference(superposition,[],[f290,f36])).
% 1.54/0.62  fof(f36,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f1])).
% 1.54/0.62  fof(f1,axiom,(
% 1.54/0.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.54/0.62  fof(f290,plain,(
% 1.54/0.62    ( ! [X5] : (k2_xboole_0(k1_xboole_0,X5) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X5),k1_xboole_0)) )),
% 1.54/0.62    inference(superposition,[],[f39,f60])).
% 1.54/0.62  fof(f45,plain,(
% 1.54/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) | ~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | X0 = X2) )),
% 1.54/0.62    inference(cnf_transformation,[],[f26])).
% 1.54/0.62  fof(f26,plain,(
% 1.54/0.62    ! [X0,X1,X2] : (X0 = X2 | ~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1))),
% 1.54/0.62    inference(flattening,[],[f25])).
% 1.54/0.62  fof(f25,plain,(
% 1.54/0.62    ! [X0,X1,X2] : (X0 = X2 | (~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)))),
% 1.54/0.62    inference(ennf_transformation,[],[f9])).
% 1.54/0.62  fof(f9,axiom,(
% 1.54/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 1.54/0.62  fof(f38,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f5])).
% 1.54/0.62  fof(f5,axiom,(
% 1.54/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.54/0.62  % SZS output end Proof for theBenchmark
% 1.54/0.62  % (28159)------------------------------
% 1.54/0.62  % (28159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.62  % (28159)Termination reason: Refutation
% 1.54/0.62  
% 1.54/0.62  % (28159)Memory used [KB]: 7164
% 1.54/0.62  % (28159)Time elapsed: 0.158 s
% 1.54/0.62  % (28159)------------------------------
% 1.54/0.62  % (28159)------------------------------
% 1.54/0.62  % (28151)Success in time 0.264 s
%------------------------------------------------------------------------------
