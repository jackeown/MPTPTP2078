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
% DateTime   : Thu Dec  3 12:30:48 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   82 (1887 expanded)
%              Number of leaves         :   11 ( 527 expanded)
%              Depth                    :   28
%              Number of atoms          :   97 (3351 expanded)
%              Number of equality atoms :   83 (2230 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10846)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f471,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f470])).

fof(f470,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f20,f427])).

fof(f427,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f426,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f426,plain,(
    sK2 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f421,f367])).

fof(f367,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f366,f304])).

fof(f304,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f300,f28])).

fof(f300,plain,(
    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f211,f299])).

fof(f299,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f293,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f293,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f75,f28])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f62,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f36,f39])).

fof(f39,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f18,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f25,f39])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f211,plain,(
    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f210,f154])).

fof(f154,plain,(
    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f148,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f148,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f27,f94])).

fof(f94,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f88,f69])).

fof(f69,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f60,f62])).

fof(f60,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f43,f59])).

fof(f59,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f56,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f56,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f26,f17])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f33])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f36,f70])).

fof(f70,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f59,f62])).

fof(f210,plain,(
    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f207,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f207,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f27,f185])).

fof(f185,plain,(
    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f36,f151])).

fof(f151,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f145,f69])).

fof(f145,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(superposition,[],[f37,f94])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f366,plain,(
    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f365,f24])).

fof(f365,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f359,f27])).

fof(f359,plain,(
    k2_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK0)) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f27,f352])).

fof(f352,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f349,f232])).

fof(f232,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f229,f26])).

fof(f229,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK0) ),
    inference(superposition,[],[f26,f74])).

fof(f74,plain,(
    k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f73,f27])).

fof(f73,plain,(
    k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f72,f62])).

fof(f72,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f65,f24])).

fof(f65,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f27,f39])).

fof(f349,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f26,f305])).

fof(f305,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
    inference(backward_demodulation,[],[f74,f304])).

fof(f421,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f27,f388])).

fof(f388,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f352,f383])).

fof(f383,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f374,f315])).

fof(f315,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f301,f304])).

fof(f301,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK2) ),
    inference(backward_demodulation,[],[f205,f299])).

fof(f205,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK2) ),
    inference(forward_demodulation,[],[f204,f185])).

fof(f204,plain,(
    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK2) ),
    inference(superposition,[],[f26,f154])).

fof(f374,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f81,f305])).

fof(f81,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(superposition,[],[f25,f69])).

fof(f20,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (10827)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (10829)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (10828)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (10834)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (10830)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.18/0.52  % (10836)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.18/0.52  % (10835)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.18/0.52  % (10826)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.18/0.52  % (10830)Refutation found. Thanks to Tanya!
% 1.18/0.52  % SZS status Theorem for theBenchmark
% 1.18/0.52  % SZS output start Proof for theBenchmark
% 1.18/0.52  % (10846)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.18/0.52  fof(f471,plain,(
% 1.18/0.52    $false),
% 1.18/0.52    inference(trivial_inequality_removal,[],[f470])).
% 1.18/0.52  fof(f470,plain,(
% 1.18/0.52    sK0 != sK0),
% 1.18/0.52    inference(superposition,[],[f20,f427])).
% 1.18/0.52  fof(f427,plain,(
% 1.18/0.52    sK0 = sK2),
% 1.18/0.52    inference(forward_demodulation,[],[f426,f28])).
% 1.18/0.52  fof(f28,plain,(
% 1.18/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.18/0.52    inference(cnf_transformation,[],[f5])).
% 1.18/0.52  fof(f5,axiom,(
% 1.18/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.18/0.52  fof(f426,plain,(
% 1.18/0.52    sK2 = k2_xboole_0(sK0,k1_xboole_0)),
% 1.18/0.52    inference(forward_demodulation,[],[f421,f367])).
% 1.18/0.52  fof(f367,plain,(
% 1.18/0.52    sK2 = k2_xboole_0(sK0,sK2)),
% 1.18/0.52    inference(forward_demodulation,[],[f366,f304])).
% 1.18/0.52  fof(f304,plain,(
% 1.18/0.52    sK2 = k2_xboole_0(k1_xboole_0,sK0)),
% 1.18/0.52    inference(forward_demodulation,[],[f300,f28])).
% 1.18/0.52  fof(f300,plain,(
% 1.18/0.52    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.18/0.52    inference(backward_demodulation,[],[f211,f299])).
% 1.18/0.52  fof(f299,plain,(
% 1.18/0.52    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.18/0.52    inference(forward_demodulation,[],[f293,f35])).
% 1.18/0.52  fof(f35,plain,(
% 1.18/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.18/0.52    inference(definition_unfolding,[],[f29,f31])).
% 1.18/0.52  fof(f31,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f11])).
% 1.18/0.52  fof(f11,axiom,(
% 1.18/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.18/0.52  fof(f29,plain,(
% 1.18/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f6])).
% 1.18/0.52  fof(f6,axiom,(
% 1.18/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.18/0.52  fof(f293,plain,(
% 1.18/0.52    k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.18/0.52    inference(superposition,[],[f75,f28])).
% 1.18/0.52  fof(f75,plain,(
% 1.18/0.52    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0))) )),
% 1.18/0.52    inference(forward_demodulation,[],[f66,f62])).
% 1.18/0.52  fof(f62,plain,(
% 1.18/0.52    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.18/0.52    inference(superposition,[],[f36,f39])).
% 1.18/0.52  fof(f39,plain,(
% 1.18/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.18/0.52    inference(unit_resulting_resolution,[],[f18,f33])).
% 1.18/0.52  fof(f33,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(definition_unfolding,[],[f22,f31])).
% 1.18/0.52  fof(f22,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f3])).
% 1.18/0.52  fof(f3,axiom,(
% 1.18/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.18/0.52  fof(f18,plain,(
% 1.18/0.52    r1_xboole_0(sK0,sK1)),
% 1.18/0.52    inference(cnf_transformation,[],[f15])).
% 1.18/0.52  fof(f15,plain,(
% 1.18/0.52    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 1.18/0.52    inference(flattening,[],[f14])).
% 1.18/0.52  fof(f14,plain,(
% 1.18/0.52    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 1.18/0.52    inference(ennf_transformation,[],[f13])).
% 1.18/0.52  fof(f13,negated_conjecture,(
% 1.18/0.52    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.18/0.52    inference(negated_conjecture,[],[f12])).
% 1.18/0.52  fof(f12,conjecture,(
% 1.18/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 1.18/0.52  fof(f36,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.18/0.52    inference(definition_unfolding,[],[f30,f31])).
% 1.18/0.52  fof(f30,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f10])).
% 1.18/0.52  fof(f10,axiom,(
% 1.18/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.18/0.52  fof(f66,plain,(
% 1.18/0.52    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.18/0.52    inference(superposition,[],[f25,f39])).
% 1.18/0.52  fof(f25,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f9])).
% 1.18/0.52  fof(f9,axiom,(
% 1.18/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.18/0.52  fof(f211,plain,(
% 1.18/0.52    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.18/0.52    inference(forward_demodulation,[],[f210,f154])).
% 1.18/0.52  fof(f154,plain,(
% 1.18/0.52    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.18/0.52    inference(forward_demodulation,[],[f148,f27])).
% 1.18/0.52  fof(f27,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f7])).
% 1.18/0.52  fof(f7,axiom,(
% 1.18/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.18/0.52  fof(f148,plain,(
% 1.18/0.52    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.18/0.52    inference(superposition,[],[f27,f94])).
% 1.18/0.52  fof(f94,plain,(
% 1.18/0.52    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.18/0.52    inference(forward_demodulation,[],[f88,f69])).
% 1.18/0.52  fof(f69,plain,(
% 1.18/0.52    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))),
% 1.18/0.52    inference(backward_demodulation,[],[f60,f62])).
% 1.18/0.52  fof(f60,plain,(
% 1.18/0.52    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 1.18/0.52    inference(backward_demodulation,[],[f43,f59])).
% 1.18/0.52  fof(f59,plain,(
% 1.18/0.52    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1)),
% 1.18/0.52    inference(forward_demodulation,[],[f56,f26])).
% 1.18/0.52  fof(f26,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f8])).
% 1.18/0.52  fof(f8,axiom,(
% 1.18/0.52    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.18/0.52  fof(f56,plain,(
% 1.18/0.52    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 1.18/0.52    inference(superposition,[],[f26,f17])).
% 1.18/0.52  fof(f17,plain,(
% 1.18/0.52    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.18/0.52    inference(cnf_transformation,[],[f15])).
% 1.18/0.52  fof(f43,plain,(
% 1.18/0.52    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 1.18/0.52    inference(unit_resulting_resolution,[],[f19,f33])).
% 1.18/0.52  fof(f19,plain,(
% 1.18/0.52    r1_xboole_0(sK2,sK1)),
% 1.18/0.52    inference(cnf_transformation,[],[f15])).
% 1.18/0.52  fof(f88,plain,(
% 1.18/0.52    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0)))),
% 1.18/0.52    inference(superposition,[],[f36,f70])).
% 1.18/0.52  fof(f70,plain,(
% 1.18/0.52    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.18/0.52    inference(backward_demodulation,[],[f59,f62])).
% 1.18/0.52  fof(f210,plain,(
% 1.18/0.52    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.18/0.52    inference(forward_demodulation,[],[f207,f24])).
% 1.18/0.52  fof(f24,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f1])).
% 1.18/0.52  fof(f1,axiom,(
% 1.18/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.18/0.53  fof(f207,plain,(
% 1.18/0.53    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.18/0.53    inference(superposition,[],[f27,f185])).
% 1.18/0.53  fof(f185,plain,(
% 1.18/0.53    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.18/0.53    inference(superposition,[],[f36,f151])).
% 1.18/0.53  fof(f151,plain,(
% 1.18/0.53    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))),
% 1.18/0.53    inference(forward_demodulation,[],[f145,f69])).
% 1.18/0.53  fof(f145,plain,(
% 1.18/0.53    k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))),
% 1.18/0.53    inference(superposition,[],[f37,f94])).
% 1.18/0.53  fof(f37,plain,(
% 1.18/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.18/0.53    inference(definition_unfolding,[],[f32,f31,f31])).
% 1.18/0.53  fof(f32,plain,(
% 1.18/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f2])).
% 1.18/0.53  fof(f2,axiom,(
% 1.18/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.18/0.53  fof(f366,plain,(
% 1.18/0.53    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK0,sK2)),
% 1.18/0.53    inference(forward_demodulation,[],[f365,f24])).
% 1.18/0.53  fof(f365,plain,(
% 1.18/0.53    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2)),
% 1.18/0.53    inference(forward_demodulation,[],[f359,f27])).
% 1.18/0.53  fof(f359,plain,(
% 1.18/0.53    k2_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK0)) = k2_xboole_0(sK0,sK2)),
% 1.18/0.53    inference(superposition,[],[f27,f352])).
% 1.18/0.53  fof(f352,plain,(
% 1.18/0.53    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK2,sK0)),
% 1.18/0.53    inference(forward_demodulation,[],[f349,f232])).
% 1.18/0.53  fof(f232,plain,(
% 1.18/0.53    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k4_xboole_0(k1_xboole_0,sK0)),
% 1.18/0.53    inference(forward_demodulation,[],[f229,f26])).
% 1.18/0.53  fof(f229,plain,(
% 1.18/0.53    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK0)),
% 1.18/0.53    inference(superposition,[],[f26,f74])).
% 1.18/0.53  fof(f74,plain,(
% 1.18/0.53    k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k2_xboole_0(k1_xboole_0,sK0)),
% 1.18/0.53    inference(forward_demodulation,[],[f73,f27])).
% 1.18/0.53  fof(f73,plain,(
% 1.18/0.53    k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 1.18/0.53    inference(forward_demodulation,[],[f72,f62])).
% 1.18/0.53  fof(f72,plain,(
% 1.18/0.53    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 1.18/0.53    inference(forward_demodulation,[],[f65,f24])).
% 1.18/0.53  fof(f65,plain,(
% 1.18/0.53    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.18/0.53    inference(superposition,[],[f27,f39])).
% 1.18/0.53  fof(f349,plain,(
% 1.18/0.53    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) = k4_xboole_0(sK2,sK0)),
% 1.18/0.53    inference(superposition,[],[f26,f305])).
% 1.18/0.53  fof(f305,plain,(
% 1.18/0.53    sK2 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)),
% 1.18/0.53    inference(backward_demodulation,[],[f74,f304])).
% 1.18/0.53  fof(f421,plain,(
% 1.18/0.53    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2)),
% 1.18/0.53    inference(superposition,[],[f27,f388])).
% 1.18/0.53  fof(f388,plain,(
% 1.18/0.53    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 1.18/0.53    inference(backward_demodulation,[],[f352,f383])).
% 1.18/0.53  fof(f383,plain,(
% 1.18/0.53    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 1.18/0.53    inference(forward_demodulation,[],[f374,f315])).
% 1.18/0.53  fof(f315,plain,(
% 1.18/0.53    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 1.18/0.53    inference(forward_demodulation,[],[f301,f304])).
% 1.18/0.53  fof(f301,plain,(
% 1.18/0.53    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK2)),
% 1.18/0.53    inference(backward_demodulation,[],[f205,f299])).
% 1.18/0.53  fof(f205,plain,(
% 1.18/0.53    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK2)),
% 1.18/0.53    inference(forward_demodulation,[],[f204,f185])).
% 1.18/0.53  fof(f204,plain,(
% 1.18/0.53    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK2)),
% 1.18/0.53    inference(superposition,[],[f26,f154])).
% 1.18/0.53  fof(f374,plain,(
% 1.18/0.53    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK2,sK2)),
% 1.18/0.53    inference(superposition,[],[f81,f305])).
% 1.18/0.53  fof(f81,plain,(
% 1.18/0.53    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0))) )),
% 1.18/0.53    inference(superposition,[],[f25,f69])).
% 1.18/0.53  fof(f20,plain,(
% 1.18/0.53    sK0 != sK2),
% 1.18/0.53    inference(cnf_transformation,[],[f15])).
% 1.18/0.53  % SZS output end Proof for theBenchmark
% 1.18/0.53  % (10830)------------------------------
% 1.18/0.53  % (10830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (10830)Termination reason: Refutation
% 1.18/0.53  
% 1.18/0.53  % (10830)Memory used [KB]: 6396
% 1.18/0.53  % (10830)Time elapsed: 0.105 s
% 1.18/0.53  % (10830)------------------------------
% 1.18/0.53  % (10830)------------------------------
% 1.18/0.53  % (10842)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.18/0.53  % (10838)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.18/0.53  % (10855)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.18/0.53  % (10852)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.18/0.53  % (10832)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.18/0.53  % (10850)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.18/0.54  % (10839)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.18/0.54  % (10840)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.18/0.54  % (10843)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.18/0.54  % (10844)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (10841)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.54  % (10831)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (10823)Success in time 0.169 s
%------------------------------------------------------------------------------
