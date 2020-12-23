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
% DateTime   : Thu Dec  3 12:38:13 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 359 expanded)
%              Number of leaves         :   15 ( 102 expanded)
%              Depth                    :   19
%              Number of atoms          :  131 ( 956 expanded)
%              Number of equality atoms :   95 ( 857 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(subsumption_resolution,[],[f354,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f354,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f251,f353])).

fof(f353,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f352,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f352,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f348,f161])).

fof(f161,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f37,f160])).

fof(f160,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f159,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f159,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f54,f67])).

fof(f67,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f37,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f348,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f302,f343])).

fof(f343,plain,(
    sK1 = k5_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f342,f38])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f342,plain,
    ( sK1 = sK2
    | sK1 = k5_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f340,f161])).

fof(f340,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | sK2 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f264,f202])).

fof(f202,plain,(
    ! [X0] :
      ( sK1 = k4_xboole_0(sK1,X0)
      | k2_xboole_0(sK1,X0) = X0 ) ),
    inference(resolution,[],[f197,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f197,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | k2_xboole_0(sK1,X0) = X0 ) ),
    inference(forward_demodulation,[],[f196,f160])).

fof(f196,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | k2_xboole_0(k1_tarski(sK0),X0) = X0 ) ),
    inference(resolution,[],[f171,f73])).

fof(f73,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | k2_xboole_0(k1_tarski(X4),X5) = X5 ) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f171,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | r1_xboole_0(sK1,X0) ) ),
    inference(superposition,[],[f51,f160])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f264,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f49,f251])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f302,plain,(
    k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = k5_xboole_0(sK1,k2_xboole_0(k5_xboole_0(sK1,sK2),sK2)) ),
    inference(superposition,[],[f50,f284])).

fof(f284,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK2) ),
    inference(superposition,[],[f250,f254])).

fof(f254,plain,(
    sK2 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f164,f251])).

fof(f164,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f94,f160])).

fof(f94,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f50,f37])).

fof(f250,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f219,f98])).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f97,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f97,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f87,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f87,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f50,f41])).

fof(f219,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f59,f41])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f251,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f166,f250])).

fof(f166,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f150,f160])).

fof(f150,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f94,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (20474)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (20482)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (20471)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (20475)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (20494)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (20493)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.19/0.51  % (20470)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.19/0.52  % (20473)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.52  % (20477)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.19/0.52  % (20486)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.19/0.52  % (20486)Refutation not found, incomplete strategy% (20486)------------------------------
% 1.19/0.52  % (20486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (20491)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.19/0.52  % (20490)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.19/0.52  % (20484)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.19/0.52  % (20485)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.19/0.52  % (20486)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (20486)Memory used [KB]: 6140
% 1.19/0.52  % (20486)Time elapsed: 0.003 s
% 1.19/0.52  % (20486)------------------------------
% 1.19/0.52  % (20486)------------------------------
% 1.19/0.52  % (20472)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.53  % (20476)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.53  % (20479)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.19/0.53  % (20487)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.53  % (20478)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.53  % (20492)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.53  % (20481)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.53  % (20495)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (20488)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.54  % (20489)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.54  % (20500)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.54  % (20488)Refutation not found, incomplete strategy% (20488)------------------------------
% 1.34/0.54  % (20488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (20481)Refutation not found, incomplete strategy% (20481)------------------------------
% 1.34/0.54  % (20481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (20481)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (20481)Memory used [KB]: 10618
% 1.34/0.54  % (20481)Time elapsed: 0.138 s
% 1.34/0.54  % (20481)------------------------------
% 1.34/0.54  % (20481)------------------------------
% 1.34/0.55  % (20496)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.55  % (20480)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.55  % (20488)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (20488)Memory used [KB]: 10618
% 1.34/0.55  % (20488)Time elapsed: 0.140 s
% 1.34/0.55  % (20488)------------------------------
% 1.34/0.55  % (20488)------------------------------
% 1.34/0.55  % (20499)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (20480)Refutation not found, incomplete strategy% (20480)------------------------------
% 1.34/0.55  % (20480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (20480)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (20480)Memory used [KB]: 10618
% 1.34/0.55  % (20480)Time elapsed: 0.152 s
% 1.34/0.55  % (20480)------------------------------
% 1.34/0.55  % (20480)------------------------------
% 1.34/0.55  % (20477)Refutation found. Thanks to Tanya!
% 1.34/0.55  % SZS status Theorem for theBenchmark
% 1.34/0.55  % SZS output start Proof for theBenchmark
% 1.34/0.55  fof(f355,plain,(
% 1.34/0.55    $false),
% 1.34/0.55    inference(subsumption_resolution,[],[f354,f40])).
% 1.34/0.55  fof(f40,plain,(
% 1.34/0.55    k1_xboole_0 != sK2),
% 1.34/0.55    inference(cnf_transformation,[],[f34])).
% 1.34/0.55  fof(f34,plain,(
% 1.34/0.55    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).
% 1.34/0.55  fof(f33,plain,(
% 1.34/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f28,plain,(
% 1.34/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.34/0.55    inference(ennf_transformation,[],[f23])).
% 1.34/0.55  fof(f23,negated_conjecture,(
% 1.34/0.55    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.34/0.55    inference(negated_conjecture,[],[f22])).
% 1.34/0.55  fof(f22,conjecture,(
% 1.34/0.55    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.34/0.55  fof(f354,plain,(
% 1.34/0.55    k1_xboole_0 = sK2),
% 1.34/0.55    inference(backward_demodulation,[],[f251,f353])).
% 1.34/0.55  fof(f353,plain,(
% 1.34/0.55    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(forward_demodulation,[],[f352,f41])).
% 1.34/0.55  fof(f41,plain,(
% 1.34/0.55    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f9])).
% 1.34/0.55  fof(f9,axiom,(
% 1.34/0.55    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.34/0.55  fof(f352,plain,(
% 1.34/0.55    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK1)),
% 1.34/0.55    inference(forward_demodulation,[],[f348,f161])).
% 1.34/0.55  fof(f161,plain,(
% 1.34/0.55    sK1 = k2_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(backward_demodulation,[],[f37,f160])).
% 1.34/0.55  fof(f160,plain,(
% 1.34/0.55    sK1 = k1_tarski(sK0)),
% 1.34/0.55    inference(subsumption_resolution,[],[f159,f39])).
% 1.34/0.55  fof(f39,plain,(
% 1.34/0.55    k1_xboole_0 != sK1),
% 1.34/0.55    inference(cnf_transformation,[],[f34])).
% 1.34/0.55  fof(f159,plain,(
% 1.34/0.55    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 1.34/0.55    inference(resolution,[],[f54,f67])).
% 1.34/0.55  fof(f67,plain,(
% 1.34/0.55    r1_tarski(sK1,k1_tarski(sK0))),
% 1.34/0.55    inference(superposition,[],[f45,f37])).
% 1.34/0.55  fof(f45,plain,(
% 1.34/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f6])).
% 1.34/0.55  fof(f6,axiom,(
% 1.34/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.34/0.55  fof(f54,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f36])).
% 1.34/0.55  fof(f36,plain,(
% 1.34/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.34/0.55    inference(flattening,[],[f35])).
% 1.34/0.55  fof(f35,plain,(
% 1.34/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.34/0.55    inference(nnf_transformation,[],[f20])).
% 1.34/0.55  fof(f20,axiom,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.34/0.55  fof(f37,plain,(
% 1.34/0.55    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(cnf_transformation,[],[f34])).
% 1.34/0.55  fof(f348,plain,(
% 1.34/0.55    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k2_xboole_0(sK1,sK2))),
% 1.34/0.55    inference(backward_demodulation,[],[f302,f343])).
% 1.34/0.55  fof(f343,plain,(
% 1.34/0.55    sK1 = k5_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(subsumption_resolution,[],[f342,f38])).
% 1.34/0.55  fof(f38,plain,(
% 1.34/0.55    sK1 != sK2),
% 1.34/0.55    inference(cnf_transformation,[],[f34])).
% 1.34/0.55  fof(f342,plain,(
% 1.34/0.55    sK1 = sK2 | sK1 = k5_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(forward_demodulation,[],[f340,f161])).
% 1.34/0.55  fof(f340,plain,(
% 1.34/0.55    sK1 = k5_xboole_0(sK1,sK2) | sK2 = k2_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(superposition,[],[f264,f202])).
% 1.34/0.55  fof(f202,plain,(
% 1.34/0.55    ( ! [X0] : (sK1 = k4_xboole_0(sK1,X0) | k2_xboole_0(sK1,X0) = X0) )),
% 1.34/0.55    inference(resolution,[],[f197,f53])).
% 1.34/0.55  fof(f53,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f31])).
% 1.34/0.55  fof(f31,plain,(
% 1.34/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f27])).
% 1.34/0.55  fof(f27,plain,(
% 1.34/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.34/0.55    inference(unused_predicate_definition_removal,[],[f7])).
% 1.34/0.55  fof(f7,axiom,(
% 1.34/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.34/0.55  fof(f197,plain,(
% 1.34/0.55    ( ! [X0] : (r1_xboole_0(sK1,X0) | k2_xboole_0(sK1,X0) = X0) )),
% 1.34/0.55    inference(forward_demodulation,[],[f196,f160])).
% 1.34/0.55  fof(f196,plain,(
% 1.34/0.55    ( ! [X0] : (r1_xboole_0(sK1,X0) | k2_xboole_0(k1_tarski(sK0),X0) = X0) )),
% 1.34/0.55    inference(resolution,[],[f171,f73])).
% 1.34/0.55  fof(f73,plain,(
% 1.34/0.55    ( ! [X4,X5] : (~r2_hidden(X4,X5) | k2_xboole_0(k1_tarski(X4),X5) = X5) )),
% 1.34/0.55    inference(resolution,[],[f52,f57])).
% 1.34/0.55  fof(f57,plain,(
% 1.34/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f32])).
% 1.34/0.55  fof(f32,plain,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f26])).
% 1.34/0.55  fof(f26,plain,(
% 1.34/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 1.34/0.55    inference(unused_predicate_definition_removal,[],[f18])).
% 1.34/0.55  fof(f18,axiom,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.34/0.55  fof(f52,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f30])).
% 1.34/0.55  fof(f30,plain,(
% 1.34/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f5])).
% 1.34/0.55  fof(f5,axiom,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.34/0.55  fof(f171,plain,(
% 1.34/0.55    ( ! [X0] : (r2_hidden(sK0,X0) | r1_xboole_0(sK1,X0)) )),
% 1.34/0.55    inference(superposition,[],[f51,f160])).
% 1.34/0.55  fof(f51,plain,(
% 1.34/0.55    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f29])).
% 1.34/0.55  fof(f29,plain,(
% 1.34/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f19])).
% 1.34/0.55  fof(f19,axiom,(
% 1.34/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.34/0.55  fof(f264,plain,(
% 1.34/0.55    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(superposition,[],[f49,f251])).
% 1.34/0.55  fof(f49,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f4])).
% 1.34/0.55  fof(f4,axiom,(
% 1.34/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.34/0.55  fof(f302,plain,(
% 1.34/0.55    k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = k5_xboole_0(sK1,k2_xboole_0(k5_xboole_0(sK1,sK2),sK2))),
% 1.34/0.55    inference(superposition,[],[f50,f284])).
% 1.34/0.55  fof(f284,plain,(
% 1.34/0.55    sK1 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK2)),
% 1.34/0.55    inference(superposition,[],[f250,f254])).
% 1.34/0.55  fof(f254,plain,(
% 1.34/0.55    sK2 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 1.34/0.55    inference(backward_demodulation,[],[f164,f251])).
% 1.34/0.55  fof(f164,plain,(
% 1.34/0.55    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 1.34/0.55    inference(backward_demodulation,[],[f94,f160])).
% 1.34/0.55  fof(f94,plain,(
% 1.34/0.55    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.34/0.55    inference(superposition,[],[f50,f37])).
% 1.34/0.55  fof(f250,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.34/0.55    inference(forward_demodulation,[],[f219,f98])).
% 1.34/0.55  fof(f98,plain,(
% 1.34/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.34/0.55    inference(forward_demodulation,[],[f97,f43])).
% 1.34/0.55  fof(f43,plain,(
% 1.34/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f24])).
% 1.34/0.55  fof(f24,plain,(
% 1.34/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.34/0.55    inference(rectify,[],[f3])).
% 1.34/0.55  fof(f3,axiom,(
% 1.34/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.34/0.55  fof(f97,plain,(
% 1.34/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.34/0.55    inference(forward_demodulation,[],[f87,f44])).
% 1.34/0.55  fof(f44,plain,(
% 1.34/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f25])).
% 1.34/0.55  fof(f25,plain,(
% 1.34/0.55    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.34/0.55    inference(rectify,[],[f2])).
% 1.34/0.55  fof(f2,axiom,(
% 1.34/0.55    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.34/0.55  fof(f87,plain,(
% 1.34/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.34/0.55    inference(superposition,[],[f50,f41])).
% 1.34/0.55  fof(f219,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(superposition,[],[f59,f41])).
% 1.34/0.55  fof(f59,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f8])).
% 1.34/0.55  fof(f8,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.34/0.55  fof(f50,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f10])).
% 1.34/0.55  fof(f10,axiom,(
% 1.34/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.34/0.55  fof(f251,plain,(
% 1.34/0.55    sK2 = k3_xboole_0(sK1,sK2)),
% 1.34/0.55    inference(backward_demodulation,[],[f166,f250])).
% 1.34/0.55  fof(f166,plain,(
% 1.34/0.55    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 1.34/0.55    inference(backward_demodulation,[],[f150,f160])).
% 1.34/0.55  fof(f150,plain,(
% 1.34/0.55    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 1.34/0.55    inference(superposition,[],[f94,f46])).
% 1.34/0.55  fof(f46,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f1])).
% 1.34/0.55  fof(f1,axiom,(
% 1.34/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (20477)------------------------------
% 1.34/0.55  % (20477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (20477)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (20477)Memory used [KB]: 6524
% 1.34/0.55  % (20477)Time elapsed: 0.113 s
% 1.34/0.55  % (20477)------------------------------
% 1.34/0.55  % (20477)------------------------------
% 1.34/0.56  % (20466)Success in time 0.196 s
%------------------------------------------------------------------------------
