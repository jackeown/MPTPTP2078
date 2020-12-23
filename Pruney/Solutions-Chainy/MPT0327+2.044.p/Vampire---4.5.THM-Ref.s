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
% DateTime   : Thu Dec  3 12:42:54 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 247 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  111 ( 438 expanded)
%              Number of equality atoms :   69 ( 243 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2087,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2086,f32])).

fof(f32,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f2086,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f2085,f135])).

fof(f135,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f127,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f127,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f89,f61])).

fof(f61,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f48,f55])).

fof(f55,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f80,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f39,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f50,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2085,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f2084,f33])).

fof(f2084,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2083,f894])).

fof(f894,plain,(
    ! [X21,X22] : k1_xboole_0 = k3_xboole_0(X21,k4_xboole_0(X22,X21)) ),
    inference(forward_demodulation,[],[f869,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f92,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f48,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f92,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f39,f57])).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f41,f53])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f869,plain,(
    ! [X21,X22] : k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X21,X22)) = k3_xboole_0(X21,k4_xboole_0(X22,X21)) ),
    inference(superposition,[],[f180,f141])).

fof(f141,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f132,f140])).

fof(f140,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f129,f89])).

fof(f129,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f89,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f132,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f40,f89])).

fof(f180,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k5_xboole_0(X6,X7)) = X7 ),
    inference(forward_demodulation,[],[f179,f137])).

fof(f137,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f94,f136])).

fof(f136,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f128,f33])).

fof(f128,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f89,f60])).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f91,f93])).

fof(f91,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f40,f57])).

fof(f179,plain,(
    ! [X6,X7] : k5_xboole_0(k1_xboole_0,X7) = k5_xboole_0(X6,k5_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f168,f60])).

fof(f168,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X6,X6),X7) = k5_xboole_0(X6,k5_xboole_0(X6,X7)) ),
    inference(superposition,[],[f77,f57])).

fof(f77,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f50,f39])).

fof(f2083,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f2017,f433])).

fof(f433,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f62,f58])).

fof(f58,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f41,f55])).

fof(f2017,plain,(
    k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(superposition,[],[f147,f58])).

fof(f147,plain,(
    ! [X10,X9] : k2_xboole_0(k5_xboole_0(X9,X10),k3_xboole_0(X10,X9)) = k5_xboole_0(k2_xboole_0(X9,X10),k3_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X10))) ),
    inference(superposition,[],[f69,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f40,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 15:16:04 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.45  % (8713)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.46  % (8729)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (8722)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (8722)Refutation not found, incomplete strategy% (8722)------------------------------
% 0.21/0.51  % (8722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8722)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8722)Memory used [KB]: 10618
% 0.21/0.51  % (8722)Time elapsed: 0.109 s
% 0.21/0.51  % (8722)------------------------------
% 0.21/0.51  % (8722)------------------------------
% 0.21/0.51  % (8734)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (8706)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (8710)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (8716)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (8711)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (8715)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (8714)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (8726)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (8728)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (8720)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (8709)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (8718)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (8724)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (8724)Refutation not found, incomplete strategy% (8724)------------------------------
% 0.21/0.53  % (8724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8724)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8724)Memory used [KB]: 1663
% 0.21/0.53  % (8724)Time elapsed: 0.134 s
% 0.21/0.53  % (8724)------------------------------
% 0.21/0.53  % (8724)------------------------------
% 0.21/0.53  % (8719)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (8723)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (8708)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (8734)Refutation not found, incomplete strategy% (8734)------------------------------
% 0.21/0.54  % (8734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8734)Memory used [KB]: 10746
% 0.21/0.54  % (8734)Time elapsed: 0.134 s
% 0.21/0.54  % (8734)------------------------------
% 0.21/0.54  % (8734)------------------------------
% 0.21/0.54  % (8735)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (8735)Refutation not found, incomplete strategy% (8735)------------------------------
% 0.21/0.54  % (8735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8735)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8735)Memory used [KB]: 1663
% 0.21/0.54  % (8735)Time elapsed: 0.139 s
% 0.21/0.54  % (8735)------------------------------
% 0.21/0.54  % (8735)------------------------------
% 0.21/0.54  % (8707)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (8707)Refutation not found, incomplete strategy% (8707)------------------------------
% 0.21/0.54  % (8707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8707)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8707)Memory used [KB]: 1663
% 0.21/0.54  % (8707)Time elapsed: 0.137 s
% 0.21/0.54  % (8707)------------------------------
% 0.21/0.54  % (8707)------------------------------
% 0.21/0.54  % (8712)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8716)Refutation not found, incomplete strategy% (8716)------------------------------
% 0.21/0.54  % (8716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8716)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8716)Memory used [KB]: 10746
% 0.21/0.54  % (8716)Time elapsed: 0.119 s
% 0.21/0.54  % (8716)------------------------------
% 0.21/0.54  % (8716)------------------------------
% 0.21/0.54  % (8727)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (8721)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (8731)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (8731)Refutation not found, incomplete strategy% (8731)------------------------------
% 0.21/0.55  % (8731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8731)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8731)Memory used [KB]: 6268
% 0.21/0.55  % (8731)Time elapsed: 0.141 s
% 0.21/0.55  % (8731)------------------------------
% 0.21/0.55  % (8731)------------------------------
% 0.21/0.55  % (8732)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (8730)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (8733)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.56/0.56  % (8733)Refutation not found, incomplete strategy% (8733)------------------------------
% 1.56/0.56  % (8733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (8733)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (8733)Memory used [KB]: 6140
% 1.56/0.56  % (8733)Time elapsed: 0.158 s
% 1.56/0.56  % (8733)------------------------------
% 1.56/0.56  % (8733)------------------------------
% 1.56/0.56  % (8717)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.56/0.57  % (8725)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.57  % (8713)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.70/0.59  % SZS output start Proof for theBenchmark
% 1.70/0.59  fof(f2087,plain,(
% 1.70/0.59    $false),
% 1.70/0.59    inference(subsumption_resolution,[],[f2086,f32])).
% 1.70/0.59  fof(f32,plain,(
% 1.70/0.59    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.70/0.59    inference(cnf_transformation,[],[f27])).
% 1.70/0.59  fof(f27,plain,(
% 1.70/0.59    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26])).
% 1.70/0.59  fof(f26,plain,(
% 1.70/0.59    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f22,plain,(
% 1.70/0.59    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f19])).
% 1.70/0.59  fof(f19,negated_conjecture,(
% 1.70/0.59    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.70/0.59    inference(negated_conjecture,[],[f18])).
% 1.70/0.59  fof(f18,conjecture,(
% 1.70/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.70/0.59  fof(f2086,plain,(
% 1.70/0.59    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.70/0.59    inference(forward_demodulation,[],[f2085,f135])).
% 1.70/0.59  fof(f135,plain,(
% 1.70/0.59    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.70/0.59    inference(forward_demodulation,[],[f127,f33])).
% 1.70/0.59  fof(f33,plain,(
% 1.70/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f6])).
% 1.70/0.59  fof(f6,axiom,(
% 1.70/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.70/0.59  fof(f127,plain,(
% 1.70/0.59    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.70/0.59    inference(superposition,[],[f89,f61])).
% 1.70/0.59  fof(f61,plain,(
% 1.70/0.59    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.70/0.59    inference(resolution,[],[f48,f55])).
% 1.70/0.59  fof(f55,plain,(
% 1.70/0.59    r1_tarski(k1_tarski(sK0),sK1)),
% 1.70/0.59    inference(resolution,[],[f46,f31])).
% 1.70/0.59  fof(f31,plain,(
% 1.70/0.59    r2_hidden(sK0,sK1)),
% 1.70/0.59    inference(cnf_transformation,[],[f27])).
% 1.70/0.59  fof(f46,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f25])).
% 1.70/0.59  fof(f25,plain,(
% 1.70/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f20])).
% 1.70/0.59  fof(f20,plain,(
% 1.70/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 1.70/0.59    inference(unused_predicate_definition_removal,[],[f16])).
% 1.70/0.59  fof(f16,axiom,(
% 1.70/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.70/0.59  fof(f48,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f30,plain,(
% 1.70/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.70/0.59    inference(nnf_transformation,[],[f3])).
% 1.70/0.59  fof(f3,axiom,(
% 1.70/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.70/0.59  fof(f89,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.70/0.59    inference(forward_demodulation,[],[f80,f62])).
% 1.70/0.59  fof(f62,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.70/0.59    inference(superposition,[],[f39,f36])).
% 1.70/0.59  fof(f36,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f1])).
% 1.70/0.59  fof(f1,axiom,(
% 1.70/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.70/0.59  fof(f39,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f4])).
% 1.70/0.59  fof(f4,axiom,(
% 1.70/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.70/0.59  fof(f80,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 1.70/0.59    inference(superposition,[],[f50,f40])).
% 1.70/0.59  fof(f40,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f10])).
% 1.70/0.59  fof(f10,axiom,(
% 1.70/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.70/0.59  fof(f50,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f9])).
% 1.70/0.59  fof(f9,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.70/0.59  fof(f2085,plain,(
% 1.70/0.59    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.70/0.59    inference(forward_demodulation,[],[f2084,f33])).
% 1.70/0.59  fof(f2084,plain,(
% 1.70/0.59    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_xboole_0)),
% 1.70/0.59    inference(forward_demodulation,[],[f2083,f894])).
% 1.70/0.59  fof(f894,plain,(
% 1.70/0.59    ( ! [X21,X22] : (k1_xboole_0 = k3_xboole_0(X21,k4_xboole_0(X22,X21))) )),
% 1.70/0.59    inference(forward_demodulation,[],[f869,f93])).
% 1.70/0.59  fof(f93,plain,(
% 1.70/0.59    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f92,f60])).
% 1.70/0.59  fof(f60,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.70/0.59    inference(resolution,[],[f48,f53])).
% 1.70/0.59  fof(f53,plain,(
% 1.70/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.70/0.59    inference(equality_resolution,[],[f43])).
% 1.70/0.59  fof(f43,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.70/0.59    inference(cnf_transformation,[],[f29])).
% 1.70/0.59  fof(f29,plain,(
% 1.70/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.59    inference(flattening,[],[f28])).
% 1.70/0.59  fof(f28,plain,(
% 1.70/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.59    inference(nnf_transformation,[],[f2])).
% 1.70/0.59  fof(f2,axiom,(
% 1.70/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.70/0.59  fof(f92,plain,(
% 1.70/0.59    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 1.70/0.59    inference(superposition,[],[f39,f57])).
% 1.70/0.59  fof(f57,plain,(
% 1.70/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.70/0.59    inference(resolution,[],[f41,f53])).
% 1.70/0.59  fof(f41,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f23])).
% 1.70/0.59  fof(f23,plain,(
% 1.70/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f5])).
% 1.70/0.59  fof(f5,axiom,(
% 1.70/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.70/0.59  fof(f869,plain,(
% 1.70/0.59    ( ! [X21,X22] : (k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X21,X22)) = k3_xboole_0(X21,k4_xboole_0(X22,X21))) )),
% 1.70/0.59    inference(superposition,[],[f180,f141])).
% 1.70/0.59  fof(f141,plain,(
% 1.70/0.59    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 1.70/0.59    inference(forward_demodulation,[],[f132,f140])).
% 1.70/0.59  fof(f140,plain,(
% 1.70/0.59    ( ! [X2,X1] : (k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k2_xboole_0(X2,X1)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f129,f89])).
% 1.70/0.59  fof(f129,plain,(
% 1.70/0.59    ( ! [X2,X1] : (k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k5_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 1.70/0.59    inference(superposition,[],[f89,f59])).
% 1.70/0.59  fof(f59,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.70/0.59    inference(resolution,[],[f45,f35])).
% 1.70/0.59  fof(f35,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f7])).
% 1.70/0.59  fof(f7,axiom,(
% 1.70/0.59    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.70/0.59  fof(f45,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f24])).
% 1.70/0.59  fof(f24,plain,(
% 1.70/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f21])).
% 1.70/0.59  fof(f21,plain,(
% 1.70/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.70/0.59    inference(unused_predicate_definition_removal,[],[f8])).
% 1.70/0.59  fof(f8,axiom,(
% 1.70/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.70/0.59  fof(f132,plain,(
% 1.70/0.59    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 1.70/0.59    inference(superposition,[],[f40,f89])).
% 1.70/0.59  fof(f180,plain,(
% 1.70/0.59    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(X6,X7)) = X7) )),
% 1.70/0.59    inference(forward_demodulation,[],[f179,f137])).
% 1.70/0.59  fof(f137,plain,(
% 1.70/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.70/0.59    inference(backward_demodulation,[],[f94,f136])).
% 1.70/0.59  fof(f136,plain,(
% 1.70/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.70/0.59    inference(forward_demodulation,[],[f128,f33])).
% 1.70/0.59  fof(f128,plain,(
% 1.70/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)) )),
% 1.70/0.59    inference(superposition,[],[f89,f60])).
% 1.70/0.59  fof(f94,plain,(
% 1.70/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.70/0.59    inference(backward_demodulation,[],[f91,f93])).
% 1.70/0.59  fof(f91,plain,(
% 1.70/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 1.70/0.59    inference(superposition,[],[f40,f57])).
% 1.70/0.59  fof(f179,plain,(
% 1.70/0.59    ( ! [X6,X7] : (k5_xboole_0(k1_xboole_0,X7) = k5_xboole_0(X6,k5_xboole_0(X6,X7))) )),
% 1.70/0.59    inference(forward_demodulation,[],[f168,f60])).
% 1.70/0.59  fof(f168,plain,(
% 1.70/0.59    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X6,X6),X7) = k5_xboole_0(X6,k5_xboole_0(X6,X7))) )),
% 1.70/0.59    inference(superposition,[],[f77,f57])).
% 1.70/0.59  fof(f77,plain,(
% 1.70/0.59    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 1.70/0.59    inference(superposition,[],[f50,f39])).
% 1.70/0.59  fof(f2083,plain,(
% 1.70/0.59    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 1.70/0.59    inference(forward_demodulation,[],[f2017,f433])).
% 1.70/0.59  fof(f433,plain,(
% 1.70/0.59    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 1.70/0.59    inference(superposition,[],[f62,f58])).
% 1.70/0.59  fof(f58,plain,(
% 1.70/0.59    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.70/0.59    inference(resolution,[],[f41,f55])).
% 1.70/0.59  fof(f2017,plain,(
% 1.70/0.59    k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))))),
% 1.70/0.59    inference(superposition,[],[f147,f58])).
% 1.70/0.59  fof(f147,plain,(
% 1.70/0.59    ( ! [X10,X9] : (k2_xboole_0(k5_xboole_0(X9,X10),k3_xboole_0(X10,X9)) = k5_xboole_0(k2_xboole_0(X9,X10),k3_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X10)))) )),
% 1.70/0.59    inference(superposition,[],[f69,f69])).
% 1.70/0.59  fof(f69,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 1.70/0.59    inference(superposition,[],[f40,f36])).
% 1.70/0.59  % SZS output end Proof for theBenchmark
% 1.70/0.59  % (8713)------------------------------
% 1.70/0.59  % (8713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (8713)Termination reason: Refutation
% 1.70/0.59  
% 1.70/0.59  % (8713)Memory used [KB]: 3709
% 1.70/0.59  % (8713)Time elapsed: 0.156 s
% 1.70/0.59  % (8713)------------------------------
% 1.70/0.59  % (8713)------------------------------
% 1.70/0.60  % (8705)Success in time 0.227 s
%------------------------------------------------------------------------------
