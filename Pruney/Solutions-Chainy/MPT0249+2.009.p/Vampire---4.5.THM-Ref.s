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
% DateTime   : Thu Dec  3 12:38:11 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 118 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :   95 ( 301 expanded)
%              Number of equality atoms :   78 ( 267 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1765,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1764,f35])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30])).

fof(f30,plain,
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

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f1764,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f1763,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f1763,plain,
    ( k1_xboole_0 = sK2
    | sK1 = sK2 ),
    inference(resolution,[],[f1161,f1539])).

fof(f1539,plain,(
    r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f42,f1535])).

fof(f1535,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1503,f1394])).

fof(f1394,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1374,f68])).

fof(f68,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f44,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1374,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f57,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1503,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1400,f1479])).

fof(f1479,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f1134,f413])).

fof(f413,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,X9) ),
    inference(forward_demodulation,[],[f401,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f401,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f228,f99])).

fof(f99,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X3) ),
    inference(resolution,[],[f49,f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f228,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1134,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f689,f1109])).

fof(f1109,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f1108,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f1108,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f51,f63])).

fof(f63,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f41,f34])).

fof(f34,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f689,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f48,f34])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f1400,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f1394,f47])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1161,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k1_xboole_0 = X0
      | sK1 = X0 ) ),
    inference(superposition,[],[f51,f1109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:39:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (25681)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (25695)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (25695)Refutation not found, incomplete strategy% (25695)------------------------------
% 0.21/0.51  % (25695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25684)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (25696)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (25689)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (25680)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (25703)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (25695)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25695)Memory used [KB]: 6140
% 0.21/0.51  % (25695)Time elapsed: 0.103 s
% 0.21/0.51  % (25695)------------------------------
% 0.21/0.51  % (25695)------------------------------
% 0.21/0.51  % (25685)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (25687)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (25694)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (25700)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (25702)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (25682)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (25691)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (25683)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (25704)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (25708)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (25707)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.53  % (25701)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.54  % (25686)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.54  % (25709)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.54  % (25697)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.54  % (25699)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.54  % (25697)Refutation not found, incomplete strategy% (25697)------------------------------
% 1.41/0.54  % (25697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (25697)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (25697)Memory used [KB]: 10618
% 1.41/0.54  % (25697)Time elapsed: 0.139 s
% 1.41/0.54  % (25697)------------------------------
% 1.41/0.54  % (25697)------------------------------
% 1.41/0.54  % (25692)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (25691)Refutation not found, incomplete strategy% (25691)------------------------------
% 1.41/0.55  % (25691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (25691)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (25691)Memory used [KB]: 10618
% 1.41/0.55  % (25691)Time elapsed: 0.135 s
% 1.41/0.55  % (25691)------------------------------
% 1.41/0.55  % (25691)------------------------------
% 1.41/0.55  % (25690)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (25693)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (25690)Refutation not found, incomplete strategy% (25690)------------------------------
% 1.41/0.55  % (25690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (25690)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (25690)Memory used [KB]: 10618
% 1.41/0.55  % (25690)Time elapsed: 0.149 s
% 1.41/0.55  % (25690)------------------------------
% 1.41/0.55  % (25690)------------------------------
% 1.41/0.55  % (25705)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.55/0.55  % (25688)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.55/0.56  % (25698)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.55/0.57  % (25706)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.55/0.59  % (25687)Refutation found. Thanks to Tanya!
% 1.55/0.59  % SZS status Theorem for theBenchmark
% 1.55/0.59  % SZS output start Proof for theBenchmark
% 1.55/0.59  fof(f1765,plain,(
% 1.55/0.59    $false),
% 1.55/0.59    inference(subsumption_resolution,[],[f1764,f35])).
% 1.55/0.59  fof(f35,plain,(
% 1.55/0.59    sK1 != sK2),
% 1.55/0.59    inference(cnf_transformation,[],[f31])).
% 1.55/0.59  fof(f31,plain,(
% 1.55/0.59    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30])).
% 1.55/0.59  fof(f30,plain,(
% 1.55/0.59    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f25,plain,(
% 1.55/0.59    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.55/0.59    inference(ennf_transformation,[],[f23])).
% 1.55/0.59  fof(f23,negated_conjecture,(
% 1.55/0.59    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.55/0.59    inference(negated_conjecture,[],[f22])).
% 1.55/0.59  fof(f22,conjecture,(
% 1.55/0.59    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.55/0.59  fof(f1764,plain,(
% 1.55/0.59    sK1 = sK2),
% 1.55/0.59    inference(subsumption_resolution,[],[f1763,f37])).
% 1.55/0.59  fof(f37,plain,(
% 1.55/0.59    k1_xboole_0 != sK2),
% 1.55/0.59    inference(cnf_transformation,[],[f31])).
% 1.55/0.59  fof(f1763,plain,(
% 1.55/0.59    k1_xboole_0 = sK2 | sK1 = sK2),
% 1.55/0.59    inference(resolution,[],[f1161,f1539])).
% 1.55/0.59  fof(f1539,plain,(
% 1.55/0.59    r1_tarski(sK2,sK1)),
% 1.55/0.59    inference(superposition,[],[f42,f1535])).
% 1.55/0.59  fof(f1535,plain,(
% 1.55/0.59    sK2 = k3_xboole_0(sK1,sK2)),
% 1.55/0.59    inference(forward_demodulation,[],[f1503,f1394])).
% 1.55/0.59  fof(f1394,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.55/0.59    inference(forward_demodulation,[],[f1374,f68])).
% 1.55/0.59  fof(f68,plain,(
% 1.55/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.55/0.59    inference(superposition,[],[f44,f39])).
% 1.55/0.59  fof(f39,plain,(
% 1.55/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f10])).
% 1.55/0.59  fof(f10,axiom,(
% 1.55/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.55/0.59  fof(f44,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f2])).
% 1.55/0.59  fof(f2,axiom,(
% 1.55/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.55/0.59  fof(f1374,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.55/0.59    inference(superposition,[],[f57,f38])).
% 1.55/0.59  fof(f38,plain,(
% 1.55/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f13])).
% 1.55/0.59  fof(f13,axiom,(
% 1.55/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.55/0.59  fof(f57,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f12])).
% 1.55/0.59  fof(f12,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.55/0.59  fof(f1503,plain,(
% 1.55/0.59    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 1.55/0.59    inference(superposition,[],[f1400,f1479])).
% 1.55/0.59  fof(f1479,plain,(
% 1.55/0.59    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 1.55/0.59    inference(superposition,[],[f1134,f413])).
% 1.55/0.59  fof(f413,plain,(
% 1.55/0.59    ( ! [X8,X9] : (k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,X9)) )),
% 1.55/0.59    inference(forward_demodulation,[],[f401,f47])).
% 1.55/0.59  fof(f47,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f5])).
% 1.55/0.59  fof(f5,axiom,(
% 1.55/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.55/0.59  fof(f401,plain,(
% 1.55/0.59    ( ! [X8,X9] : (k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k5_xboole_0(X8,k3_xboole_0(X8,X9))) )),
% 1.55/0.59    inference(superposition,[],[f228,f99])).
% 1.55/0.59  fof(f99,plain,(
% 1.55/0.59    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X3)) )),
% 1.55/0.59    inference(resolution,[],[f49,f42])).
% 1.55/0.59  fof(f49,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f26])).
% 1.55/0.59  fof(f26,plain,(
% 1.55/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.55/0.59    inference(ennf_transformation,[],[f8])).
% 1.55/0.59  fof(f8,axiom,(
% 1.55/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.55/0.59  fof(f228,plain,(
% 1.55/0.59    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.55/0.59    inference(superposition,[],[f47,f43])).
% 1.55/0.59  fof(f43,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f1])).
% 1.55/0.59  fof(f1,axiom,(
% 1.55/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.55/0.59  fof(f1134,plain,(
% 1.55/0.59    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.55/0.59    inference(backward_demodulation,[],[f689,f1109])).
% 1.55/0.59  fof(f1109,plain,(
% 1.55/0.59    sK1 = k1_tarski(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f1108,f36])).
% 1.55/0.59  fof(f36,plain,(
% 1.55/0.59    k1_xboole_0 != sK1),
% 1.55/0.59    inference(cnf_transformation,[],[f31])).
% 1.55/0.59  fof(f1108,plain,(
% 1.55/0.59    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 1.55/0.59    inference(resolution,[],[f51,f63])).
% 1.55/0.59  fof(f63,plain,(
% 1.55/0.59    r1_tarski(sK1,k1_tarski(sK0))),
% 1.55/0.59    inference(superposition,[],[f41,f34])).
% 1.55/0.59  fof(f34,plain,(
% 1.55/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.55/0.59    inference(cnf_transformation,[],[f31])).
% 1.55/0.59  fof(f41,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f11])).
% 1.55/0.59  fof(f11,axiom,(
% 1.55/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.55/0.59  fof(f51,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f33])).
% 1.55/0.59  fof(f33,plain,(
% 1.55/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.55/0.59    inference(flattening,[],[f32])).
% 1.55/0.59  fof(f32,plain,(
% 1.55/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.55/0.59    inference(nnf_transformation,[],[f20])).
% 1.55/0.59  fof(f20,axiom,(
% 1.55/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.55/0.59  fof(f689,plain,(
% 1.55/0.59    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))),
% 1.55/0.59    inference(superposition,[],[f48,f34])).
% 1.55/0.59  fof(f48,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f4])).
% 1.55/0.59  fof(f4,axiom,(
% 1.55/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 1.55/0.59  fof(f1400,plain,(
% 1.55/0.59    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.55/0.59    inference(superposition,[],[f1394,f47])).
% 1.55/0.59  fof(f42,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f7])).
% 1.55/0.59  fof(f7,axiom,(
% 1.55/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.55/0.59  fof(f1161,plain,(
% 1.55/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) )),
% 1.55/0.59    inference(superposition,[],[f51,f1109])).
% 1.55/0.59  % SZS output end Proof for theBenchmark
% 1.55/0.59  % (25687)------------------------------
% 1.55/0.59  % (25687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (25687)Termination reason: Refutation
% 1.55/0.59  
% 1.55/0.59  % (25687)Memory used [KB]: 7164
% 1.55/0.59  % (25687)Time elapsed: 0.186 s
% 1.55/0.59  % (25687)------------------------------
% 1.55/0.59  % (25687)------------------------------
% 1.55/0.59  % (25679)Success in time 0.238 s
%------------------------------------------------------------------------------
