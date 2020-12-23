%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:49 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 467 expanded)
%              Number of leaves         :    9 ( 144 expanded)
%              Depth                    :   21
%              Number of atoms          :   97 ( 654 expanded)
%              Number of equality atoms :   78 ( 503 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(global_subsumption,[],[f16,f443])).

% (14610)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f443,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f442,f376])).

fof(f376,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f163,f329])).

fof(f329,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f55,f234])).

fof(f234,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(backward_demodulation,[],[f160,f216])).

fof(f216,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f159,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f159,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f28,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f160,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = X1
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f28,f29])).

% (14619)Refutation not found, incomplete strategy% (14619)------------------------------
% (14619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14619)Termination reason: Refutation not found, incomplete strategy

% (14619)Memory used [KB]: 10618
% (14619)Time elapsed: 0.097 s
% (14619)------------------------------
% (14619)------------------------------
fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f26,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f163,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[],[f28,f26])).

fof(f442,plain,(
    sK2 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f435,f280])).

fof(f280,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f279,f216])).

fof(f279,plain,(
    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f275,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f275,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f259,f274])).

fof(f274,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f273,f26])).

fof(f273,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f261,f222])).

fof(f222,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK0,X0) ),
    inference(backward_demodulation,[],[f178,f216])).

fof(f178,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f150,f18])).

fof(f150,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f146,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f146,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[],[f25,f109])).

fof(f109,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f27,f42])).

fof(f42,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f14,f29])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f261,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f220,f151])).

fof(f151,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f149,f18])).

fof(f149,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f20,f109])).

fof(f220,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
    inference(backward_demodulation,[],[f150,f216])).

fof(f259,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK0,sK0)) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f257,f18])).

fof(f257,plain,(
    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f20,f244])).

fof(f244,plain,(
    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f239,f216])).

fof(f239,plain,(
    k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f188,f216])).

fof(f188,plain,(
    k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f175,f187])).

fof(f187,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f176,f20])).

fof(f176,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f150,f151])).

fof(f175,plain,(
    k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f150,f31])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f18,f13])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f435,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f20,f392])).

fof(f392,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f243,f368])).

fof(f368,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f26,f329])).

fof(f243,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f237,f216])).

fof(f237,plain,(
    k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f208,f216])).

fof(f208,plain,(
    k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f195,f207])).

fof(f207,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f196,f20])).

fof(f196,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f157,f151])).

fof(f157,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f153,f25])).

fof(f153,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0) ),
    inference(superposition,[],[f25,f110])).

fof(f110,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f27,f43])).

fof(f43,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f15,f29])).

fof(f15,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f195,plain,(
    k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f157,f31])).

fof(f16,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n019.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 11:50:22 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.38  % (14607)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.11/0.38  % (14626)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.11/0.39  % (14603)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.11/0.40  % (14617)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.11/0.40  % (14602)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.11/0.40  % (14617)Refutation not found, incomplete strategy% (14617)------------------------------
% 0.11/0.40  % (14617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (14617)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (14617)Memory used [KB]: 6140
% 0.11/0.40  % (14617)Time elapsed: 0.007 s
% 0.11/0.40  % (14617)------------------------------
% 0.11/0.40  % (14617)------------------------------
% 0.11/0.40  % (14608)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.11/0.41  % (14619)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.11/0.41  % (14606)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.11/0.42  % (14611)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.11/0.42  % (14604)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.11/0.42  % (14626)Refutation found. Thanks to Tanya!
% 0.11/0.42  % SZS status Theorem for theBenchmark
% 0.11/0.42  % SZS output start Proof for theBenchmark
% 0.11/0.42  fof(f444,plain,(
% 0.11/0.42    $false),
% 0.11/0.42    inference(global_subsumption,[],[f16,f443])).
% 0.11/0.42  % (14610)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.11/0.42  fof(f443,plain,(
% 0.11/0.42    sK0 = sK2),
% 0.11/0.42    inference(forward_demodulation,[],[f442,f376])).
% 0.11/0.42  fof(f376,plain,(
% 0.11/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.11/0.42    inference(backward_demodulation,[],[f163,f329])).
% 0.11/0.42  fof(f329,plain,(
% 0.11/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.11/0.42    inference(unit_resulting_resolution,[],[f55,f234])).
% 0.11/0.42  fof(f234,plain,(
% 0.11/0.42    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | ~r1_xboole_0(X1,X2)) )),
% 0.11/0.42    inference(backward_demodulation,[],[f160,f216])).
% 0.11/0.42  fof(f216,plain,(
% 0.11/0.42    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.11/0.42    inference(superposition,[],[f159,f20])).
% 0.11/0.42  fof(f20,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.11/0.42    inference(cnf_transformation,[],[f4])).
% 0.11/0.42  fof(f4,axiom,(
% 0.11/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.11/0.42  fof(f159,plain,(
% 0.11/0.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.11/0.42    inference(superposition,[],[f28,f26])).
% 0.11/0.42  fof(f26,plain,(
% 0.11/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.11/0.42    inference(definition_unfolding,[],[f17,f19])).
% 0.11/0.42  fof(f19,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.11/0.42    inference(cnf_transformation,[],[f7])).
% 0.11/0.42  fof(f7,axiom,(
% 0.11/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.11/0.42  fof(f17,plain,(
% 0.11/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.11/0.42    inference(cnf_transformation,[],[f3])).
% 0.11/0.42  fof(f3,axiom,(
% 0.11/0.42    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.11/0.42  fof(f28,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.11/0.42    inference(definition_unfolding,[],[f22,f19])).
% 0.11/0.42  fof(f22,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.11/0.42    inference(cnf_transformation,[],[f8])).
% 0.11/0.42  fof(f8,axiom,(
% 0.11/0.42    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.11/0.42  fof(f160,plain,(
% 0.11/0.42    ( ! [X2,X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = X1 | ~r1_xboole_0(X1,X2)) )),
% 0.11/0.42    inference(superposition,[],[f28,f29])).
% 0.11/0.42  % (14619)Refutation not found, incomplete strategy% (14619)------------------------------
% 0.11/0.42  % (14619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.42  % (14619)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.42  
% 0.11/0.42  % (14619)Memory used [KB]: 10618
% 0.11/0.42  % (14619)Time elapsed: 0.097 s
% 0.11/0.42  % (14619)------------------------------
% 0.11/0.42  % (14619)------------------------------
% 0.11/0.42  fof(f29,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.11/0.42    inference(definition_unfolding,[],[f24,f19])).
% 0.11/0.42  fof(f24,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.11/0.42    inference(cnf_transformation,[],[f2])).
% 0.11/0.42  fof(f2,axiom,(
% 0.11/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.11/0.42  fof(f55,plain,(
% 0.11/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.11/0.42    inference(unit_resulting_resolution,[],[f26,f30])).
% 0.11/0.42  fof(f30,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.11/0.42    inference(definition_unfolding,[],[f23,f19])).
% 0.11/0.42  fof(f23,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.11/0.42    inference(cnf_transformation,[],[f2])).
% 0.11/0.42  fof(f163,plain,(
% 0.11/0.42    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 0.11/0.42    inference(superposition,[],[f28,f26])).
% 0.11/0.42  fof(f442,plain,(
% 0.11/0.42    sK2 = k2_xboole_0(sK0,k1_xboole_0)),
% 0.11/0.42    inference(forward_demodulation,[],[f435,f280])).
% 0.11/0.42  fof(f280,plain,(
% 0.11/0.42    sK2 = k2_xboole_0(sK0,sK2)),
% 0.11/0.42    inference(forward_demodulation,[],[f279,f216])).
% 0.11/0.42  fof(f279,plain,(
% 0.11/0.42    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK0,sK2)),
% 0.11/0.42    inference(forward_demodulation,[],[f275,f18])).
% 0.11/0.42  fof(f18,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.11/0.42    inference(cnf_transformation,[],[f1])).
% 0.11/0.42  fof(f1,axiom,(
% 0.11/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.11/0.42  fof(f275,plain,(
% 0.11/0.42    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK0,sK2)),
% 0.11/0.42    inference(backward_demodulation,[],[f259,f274])).
% 0.11/0.42  fof(f274,plain,(
% 0.11/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.11/0.42    inference(forward_demodulation,[],[f273,f26])).
% 0.11/0.42  fof(f273,plain,(
% 0.11/0.42    k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,sK0)),
% 0.11/0.42    inference(forward_demodulation,[],[f261,f222])).
% 0.11/0.42  fof(f222,plain,(
% 0.11/0.42    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK0,X0)) )),
% 0.11/0.42    inference(backward_demodulation,[],[f178,f216])).
% 0.11/0.42  fof(f178,plain,(
% 0.11/0.42    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))) )),
% 0.11/0.42    inference(superposition,[],[f150,f18])).
% 0.11/0.42  fof(f150,plain,(
% 0.11/0.42    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0))) )),
% 0.11/0.42    inference(forward_demodulation,[],[f146,f25])).
% 0.11/0.42  fof(f25,plain,(
% 0.11/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.11/0.42    inference(cnf_transformation,[],[f5])).
% 0.11/0.42  fof(f5,axiom,(
% 0.11/0.42    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.11/0.42  fof(f146,plain,(
% 0.11/0.42    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) )),
% 0.11/0.42    inference(superposition,[],[f25,f109])).
% 0.11/0.42  fof(f109,plain,(
% 0.11/0.42    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.11/0.42    inference(superposition,[],[f27,f42])).
% 0.11/0.42  fof(f42,plain,(
% 0.11/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.11/0.42    inference(unit_resulting_resolution,[],[f14,f29])).
% 0.11/0.42  fof(f14,plain,(
% 0.11/0.42    r1_xboole_0(sK0,sK1)),
% 0.11/0.42    inference(cnf_transformation,[],[f12])).
% 0.11/0.42  fof(f12,plain,(
% 0.11/0.42    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 0.11/0.42    inference(flattening,[],[f11])).
% 0.11/0.42  fof(f11,plain,(
% 0.11/0.42    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 0.11/0.42    inference(ennf_transformation,[],[f10])).
% 0.11/0.42  fof(f10,negated_conjecture,(
% 0.11/0.42    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.11/0.42    inference(negated_conjecture,[],[f9])).
% 0.11/0.42  fof(f9,conjecture,(
% 0.11/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 0.11/0.42  fof(f27,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.11/0.42    inference(definition_unfolding,[],[f21,f19])).
% 0.11/0.43  fof(f21,plain,(
% 0.11/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.11/0.43    inference(cnf_transformation,[],[f6])).
% 0.11/0.43  fof(f6,axiom,(
% 0.11/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.11/0.43  fof(f261,plain,(
% 0.11/0.43    k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.11/0.43    inference(superposition,[],[f220,f151])).
% 0.11/0.43  fof(f151,plain,(
% 0.11/0.43    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0))),
% 0.11/0.43    inference(forward_demodulation,[],[f149,f18])).
% 0.11/0.43  fof(f149,plain,(
% 0.11/0.43    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0))),
% 0.11/0.43    inference(superposition,[],[f20,f109])).
% 0.11/0.43  fof(f220,plain,(
% 0.11/0.43    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) )),
% 0.11/0.43    inference(backward_demodulation,[],[f150,f216])).
% 0.11/0.43  fof(f259,plain,(
% 0.11/0.43    k2_xboole_0(sK2,k4_xboole_0(sK0,sK0)) = k2_xboole_0(sK0,sK2)),
% 0.11/0.43    inference(forward_demodulation,[],[f257,f18])).
% 0.11/0.43  fof(f257,plain,(
% 0.11/0.43    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK0))),
% 0.11/0.43    inference(superposition,[],[f20,f244])).
% 0.11/0.43  fof(f244,plain,(
% 0.11/0.43    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK2)),
% 0.11/0.43    inference(forward_demodulation,[],[f239,f216])).
% 0.11/0.43  fof(f239,plain,(
% 0.11/0.43    k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK0,sK0)),
% 0.11/0.43    inference(backward_demodulation,[],[f188,f216])).
% 0.11/0.43  fof(f188,plain,(
% 0.11/0.43    k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK0))),
% 0.11/0.43    inference(backward_demodulation,[],[f175,f187])).
% 0.11/0.43  fof(f187,plain,(
% 0.11/0.43    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK0))),
% 0.11/0.43    inference(forward_demodulation,[],[f176,f20])).
% 0.11/0.43  fof(f176,plain,(
% 0.11/0.43    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)))),
% 0.11/0.43    inference(superposition,[],[f150,f151])).
% 0.11/0.43  fof(f175,plain,(
% 0.11/0.43    k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.11/0.43    inference(superposition,[],[f150,f31])).
% 0.11/0.43  fof(f31,plain,(
% 0.11/0.43    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)),
% 0.11/0.43    inference(superposition,[],[f18,f13])).
% 0.11/0.43  fof(f13,plain,(
% 0.11/0.43    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.11/0.43    inference(cnf_transformation,[],[f12])).
% 0.11/0.43  fof(f435,plain,(
% 0.11/0.43    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2)),
% 0.11/0.43    inference(superposition,[],[f20,f392])).
% 0.11/0.43  fof(f392,plain,(
% 0.11/0.43    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.11/0.43    inference(backward_demodulation,[],[f243,f368])).
% 0.11/0.43  fof(f368,plain,(
% 0.11/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.11/0.43    inference(backward_demodulation,[],[f26,f329])).
% 0.11/0.43  fof(f243,plain,(
% 0.11/0.43    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2)),
% 0.11/0.43    inference(forward_demodulation,[],[f237,f216])).
% 0.11/0.43  fof(f237,plain,(
% 0.11/0.43    k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK2,sK0)),
% 0.11/0.43    inference(backward_demodulation,[],[f208,f216])).
% 0.11/0.43  fof(f208,plain,(
% 0.11/0.43    k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0))),
% 0.11/0.43    inference(backward_demodulation,[],[f195,f207])).
% 0.11/0.43  fof(f207,plain,(
% 0.11/0.43    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0))),
% 0.11/0.43    inference(forward_demodulation,[],[f196,f20])).
% 0.11/0.43  fof(f196,plain,(
% 0.11/0.43    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)))),
% 0.11/0.43    inference(superposition,[],[f157,f151])).
% 0.11/0.43  fof(f157,plain,(
% 0.11/0.43    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,X0))) )),
% 0.11/0.43    inference(forward_demodulation,[],[f153,f25])).
% 0.11/0.43  fof(f153,plain,(
% 0.11/0.43    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0)) )),
% 0.11/0.43    inference(superposition,[],[f25,f110])).
% 0.11/0.43  fof(f110,plain,(
% 0.11/0.43    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k1_xboole_0)),
% 0.11/0.43    inference(superposition,[],[f27,f43])).
% 0.11/0.43  fof(f43,plain,(
% 0.11/0.43    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 0.11/0.43    inference(unit_resulting_resolution,[],[f15,f29])).
% 0.11/0.43  fof(f15,plain,(
% 0.11/0.43    r1_xboole_0(sK2,sK1)),
% 0.11/0.43    inference(cnf_transformation,[],[f12])).
% 0.11/0.43  fof(f195,plain,(
% 0.11/0.43    k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK2)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.11/0.43    inference(superposition,[],[f157,f31])).
% 0.11/0.43  fof(f16,plain,(
% 0.11/0.43    sK0 != sK2),
% 0.11/0.43    inference(cnf_transformation,[],[f12])).
% 0.11/0.43  % SZS output end Proof for theBenchmark
% 0.11/0.43  % (14626)------------------------------
% 0.11/0.43  % (14626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.43  % (14626)Termination reason: Refutation
% 0.11/0.43  
% 0.11/0.43  % (14626)Memory used [KB]: 6524
% 0.11/0.43  % (14626)Time elapsed: 0.075 s
% 0.11/0.44  % (14627)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.11/0.44  % (14626)------------------------------
% 0.11/0.44  % (14626)------------------------------
% 0.11/0.44  % (14621)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.11/0.44  % (14601)Success in time 0.17 s
%------------------------------------------------------------------------------
