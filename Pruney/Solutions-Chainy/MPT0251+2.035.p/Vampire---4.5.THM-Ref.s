%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:39 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 189 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :   88 ( 291 expanded)
%              Number of equality atoms :   54 ( 180 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f761,plain,(
    $false ),
    inference(subsumption_resolution,[],[f760,f97])).

fof(f97,plain,(
    sK2 != k2_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f44,f95])).

fof(f95,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f85,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f85,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f44,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f760,plain,(
    sK2 = k2_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f749,f178])).

fof(f178,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f114,f177])).

fof(f177,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f169,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f169,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f53,f46])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f114,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f113,f46])).

fof(f113,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f111,f109])).

fof(f109,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f52,f88])).

fof(f88,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f55,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f111,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f51,f108])).

fof(f108,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f52,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f749,plain,(
    k2_xboole_0(sK2,k1_tarski(sK1)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f51,f748])).

fof(f748,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK2) ),
    inference(forward_demodulation,[],[f747,f185])).

fof(f185,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f109,f180])).

fof(f180,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(backward_demodulation,[],[f175,f178])).

fof(f175,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X7,k1_xboole_0),X7) ),
    inference(forward_demodulation,[],[f167,f122])).

fof(f122,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f110,f46])).

fof(f110,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f108,f108])).

fof(f167,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(k5_xboole_0(X7,k1_xboole_0),X7) ),
    inference(superposition,[],[f53,f151])).

fof(f151,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f114,f95])).

fof(f747,plain,(
    k4_xboole_0(k1_tarski(sK1),sK2) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f52,f744])).

fof(f744,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK2) ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),X3) ) ),
    inference(resolution,[],[f55,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:56:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.17/0.53  % (11796)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.17/0.53  % (11808)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.53  % (11803)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.17/0.53  % (11800)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.17/0.54  % (11821)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.17/0.54  % (11822)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.17/0.54  % (11799)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.54  % (11794)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.17/0.54  % (11820)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.17/0.54  % (11815)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.54  % (11801)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.54  % (11797)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.43/0.55  % (11795)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.43/0.55  % (11798)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.43/0.55  % (11804)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (11810)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.55  % (11823)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (11816)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.55  % (11816)Refutation not found, incomplete strategy% (11816)------------------------------
% 1.43/0.55  % (11816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (11816)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (11816)Memory used [KB]: 10746
% 1.43/0.55  % (11816)Time elapsed: 0.112 s
% 1.43/0.55  % (11816)------------------------------
% 1.43/0.55  % (11816)------------------------------
% 1.43/0.55  % (11811)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.55  % (11817)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.55  % (11818)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.56  % (11807)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.56  % (11806)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (11802)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.56  % (11819)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.56  % (11814)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.56  % (11805)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (11809)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.43/0.56  % (11813)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.57  % (11812)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.58  % (11801)Refutation found. Thanks to Tanya!
% 1.43/0.58  % SZS status Theorem for theBenchmark
% 1.43/0.59  % SZS output start Proof for theBenchmark
% 1.43/0.59  fof(f761,plain,(
% 1.43/0.59    $false),
% 1.43/0.59    inference(subsumption_resolution,[],[f760,f97])).
% 1.43/0.59  fof(f97,plain,(
% 1.43/0.59    sK2 != k2_xboole_0(sK2,k1_tarski(sK1))),
% 1.43/0.59    inference(superposition,[],[f44,f95])).
% 1.43/0.59  fof(f95,plain,(
% 1.43/0.59    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.43/0.59    inference(superposition,[],[f85,f50])).
% 1.43/0.59  fof(f50,plain,(
% 1.43/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.43/0.59    inference(cnf_transformation,[],[f18])).
% 1.43/0.59  fof(f18,axiom,(
% 1.43/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.43/0.59  fof(f85,plain,(
% 1.43/0.59    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 1.43/0.59    inference(superposition,[],[f50,f48])).
% 1.43/0.59  fof(f48,plain,(
% 1.43/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.43/0.59    inference(cnf_transformation,[],[f12])).
% 1.43/0.59  fof(f12,axiom,(
% 1.43/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.43/0.59  fof(f44,plain,(
% 1.43/0.59    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.43/0.59    inference(cnf_transformation,[],[f28])).
% 1.43/0.59  fof(f28,plain,(
% 1.43/0.59    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.43/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27])).
% 1.43/0.59  fof(f27,plain,(
% 1.43/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.43/0.59    introduced(choice_axiom,[])).
% 1.43/0.59  fof(f21,plain,(
% 1.43/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.43/0.59    inference(ennf_transformation,[],[f20])).
% 1.43/0.59  fof(f20,negated_conjecture,(
% 1.43/0.59    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.43/0.59    inference(negated_conjecture,[],[f19])).
% 1.43/0.59  fof(f19,conjecture,(
% 1.43/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.43/0.59  fof(f760,plain,(
% 1.43/0.59    sK2 = k2_xboole_0(sK2,k1_tarski(sK1))),
% 1.43/0.59    inference(forward_demodulation,[],[f749,f178])).
% 1.43/0.59  fof(f178,plain,(
% 1.43/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.59    inference(backward_demodulation,[],[f114,f177])).
% 1.43/0.59  fof(f177,plain,(
% 1.43/0.59    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.43/0.59    inference(forward_demodulation,[],[f169,f46])).
% 1.43/0.59  fof(f46,plain,(
% 1.43/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.59    inference(cnf_transformation,[],[f9])).
% 1.43/0.59  fof(f9,axiom,(
% 1.43/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.43/0.59  fof(f169,plain,(
% 1.43/0.59    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.43/0.59    inference(superposition,[],[f53,f46])).
% 1.43/0.59  fof(f53,plain,(
% 1.43/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.43/0.59    inference(cnf_transformation,[],[f10])).
% 1.43/0.59  fof(f10,axiom,(
% 1.43/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.43/0.59  fof(f114,plain,(
% 1.43/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.43/0.59    inference(forward_demodulation,[],[f113,f46])).
% 1.43/0.59  fof(f113,plain,(
% 1.43/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.43/0.59    inference(forward_demodulation,[],[f111,f109])).
% 1.43/0.59  fof(f109,plain,(
% 1.43/0.59    ( ! [X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1)) )),
% 1.43/0.59    inference(superposition,[],[f52,f88])).
% 1.43/0.59  fof(f88,plain,(
% 1.43/0.59    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.43/0.59    inference(resolution,[],[f55,f78])).
% 1.43/0.59  fof(f78,plain,(
% 1.43/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.43/0.59    inference(equality_resolution,[],[f57])).
% 1.43/0.59  fof(f57,plain,(
% 1.43/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.43/0.59    inference(cnf_transformation,[],[f30])).
% 1.43/0.59  fof(f30,plain,(
% 1.43/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.59    inference(flattening,[],[f29])).
% 1.43/0.59  fof(f29,plain,(
% 1.43/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.59    inference(nnf_transformation,[],[f4])).
% 1.43/0.59  fof(f4,axiom,(
% 1.43/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.59  fof(f55,plain,(
% 1.43/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.43/0.59    inference(cnf_transformation,[],[f22])).
% 1.43/0.59  fof(f22,plain,(
% 1.43/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.43/0.59    inference(ennf_transformation,[],[f6])).
% 1.43/0.59  fof(f6,axiom,(
% 1.43/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.43/0.59  fof(f52,plain,(
% 1.43/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.43/0.59    inference(cnf_transformation,[],[f5])).
% 1.43/0.59  fof(f5,axiom,(
% 1.43/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.43/0.59  fof(f111,plain,(
% 1.43/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.43/0.59    inference(superposition,[],[f51,f108])).
% 1.43/0.59  fof(f108,plain,(
% 1.43/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.43/0.59    inference(superposition,[],[f52,f87])).
% 1.43/0.59  fof(f87,plain,(
% 1.43/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.43/0.59    inference(resolution,[],[f55,f45])).
% 1.43/0.59  fof(f45,plain,(
% 1.43/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.43/0.59    inference(cnf_transformation,[],[f7])).
% 1.43/0.59  fof(f7,axiom,(
% 1.43/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.43/0.59  fof(f51,plain,(
% 1.43/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.43/0.59    inference(cnf_transformation,[],[f11])).
% 1.43/0.59  fof(f11,axiom,(
% 1.43/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.43/0.59  fof(f749,plain,(
% 1.43/0.59    k2_xboole_0(sK2,k1_tarski(sK1)) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.43/0.59    inference(superposition,[],[f51,f748])).
% 1.43/0.59  fof(f748,plain,(
% 1.43/0.59    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK2)),
% 1.43/0.59    inference(forward_demodulation,[],[f747,f185])).
% 1.43/0.59  fof(f185,plain,(
% 1.43/0.59    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.43/0.59    inference(backward_demodulation,[],[f109,f180])).
% 1.43/0.59  fof(f180,plain,(
% 1.43/0.59    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 1.43/0.59    inference(backward_demodulation,[],[f175,f178])).
% 1.43/0.59  fof(f175,plain,(
% 1.43/0.59    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X7,k1_xboole_0),X7)) )),
% 1.43/0.59    inference(forward_demodulation,[],[f167,f122])).
% 1.43/0.59  fof(f122,plain,(
% 1.43/0.59    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8)) )),
% 1.43/0.59    inference(superposition,[],[f110,f46])).
% 1.43/0.59  fof(f110,plain,(
% 1.43/0.59    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.43/0.59    inference(superposition,[],[f108,f108])).
% 1.43/0.59  fof(f167,plain,(
% 1.43/0.59    ( ! [X7] : (k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(k5_xboole_0(X7,k1_xboole_0),X7)) )),
% 1.43/0.59    inference(superposition,[],[f53,f151])).
% 1.43/0.59  fof(f151,plain,(
% 1.43/0.59    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.43/0.59    inference(superposition,[],[f114,f95])).
% 1.43/0.59  fof(f747,plain,(
% 1.43/0.59    k4_xboole_0(k1_tarski(sK1),sK2) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 1.43/0.59    inference(superposition,[],[f52,f744])).
% 1.43/0.59  fof(f744,plain,(
% 1.43/0.59    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK2)),
% 1.43/0.59    inference(resolution,[],[f89,f43])).
% 1.43/0.59  fof(f43,plain,(
% 1.43/0.59    r2_hidden(sK1,sK2)),
% 1.43/0.59    inference(cnf_transformation,[],[f28])).
% 1.43/0.59  fof(f89,plain,(
% 1.43/0.59    ( ! [X2,X3] : (~r2_hidden(X2,X3) | k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),X3)) )),
% 1.43/0.59    inference(resolution,[],[f55,f63])).
% 1.43/0.59  fof(f63,plain,(
% 1.43/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.43/0.59    inference(cnf_transformation,[],[f35])).
% 1.43/0.59  fof(f35,plain,(
% 1.43/0.59    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.43/0.59    inference(nnf_transformation,[],[f17])).
% 1.43/0.59  fof(f17,axiom,(
% 1.43/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.43/0.59  % SZS output end Proof for theBenchmark
% 1.43/0.59  % (11801)------------------------------
% 1.43/0.59  % (11801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.59  % (11801)Termination reason: Refutation
% 1.43/0.59  
% 1.43/0.59  % (11801)Memory used [KB]: 6524
% 1.43/0.59  % (11801)Time elapsed: 0.168 s
% 1.43/0.59  % (11801)------------------------------
% 1.43/0.59  % (11801)------------------------------
% 1.43/0.59  % (11793)Success in time 0.226 s
%------------------------------------------------------------------------------
