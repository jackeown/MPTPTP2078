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
% DateTime   : Thu Dec  3 12:30:56 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 414 expanded)
%              Number of leaves         :   12 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  110 ( 918 expanded)
%              Number of equality atoms :   59 ( 487 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1180,f31])).

fof(f31,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1180,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1179,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1179,plain,(
    sK2 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f778,f789])).

fof(f789,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f788,f737])).

fof(f737,plain,(
    sK2 = k4_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f713,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f37,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f713,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f690,f203])).

fof(f203,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f195,f32])).

fof(f195,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f46,f127])).

fof(f127,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f48,f29])).

fof(f29,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f690,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f66,f671])).

fof(f671,plain,(
    sK0 = sK3 ),
    inference(backward_demodulation,[],[f473,f642])).

fof(f642,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f639,f34])).

fof(f639,plain,(
    sK0 = k2_xboole_0(sK3,sK0) ),
    inference(resolution,[],[f635,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f635,plain,(
    r1_tarski(sK3,sK0) ),
    inference(forward_demodulation,[],[f615,f204])).

fof(f204,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f196,f32])).

% (6533)Refutation not found, incomplete strategy% (6533)------------------------------
% (6533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6533)Termination reason: Refutation not found, incomplete strategy

% (6533)Memory used [KB]: 10618
% (6533)Time elapsed: 0.154 s
% (6533)------------------------------
% (6533)------------------------------
fof(f196,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f46,f128])).

fof(f128,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f615,plain,(
    r1_tarski(k4_xboole_0(sK3,sK1),sK0) ),
    inference(resolution,[],[f105,f56])).

fof(f56,plain,(
    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f53,f28])).

fof(f28,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f105,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k2_xboole_0(X3,X2))
      | r1_tarski(k4_xboole_0(X4,X2),X3) ) ),
    inference(superposition,[],[f43,f34])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f473,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f467,f38])).

fof(f467,plain,(
    r1_tarski(sK0,sK3) ),
    inference(backward_demodulation,[],[f326,f421])).

fof(f421,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f413,f32])).

fof(f413,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f46,f125])).

fof(f125,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f48,f50])).

fof(f50,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f39,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f326,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),sK3) ),
    inference(resolution,[],[f103,f33])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK0,sK1))
      | r1_tarski(k4_xboole_0(X0,sK2),sK3) ) ),
    inference(superposition,[],[f43,f28])).

fof(f66,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f37,f28])).

fof(f788,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f126,f671])).

fof(f126,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f48,f51])).

fof(f51,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f39,f30])).

fof(f778,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f46,f737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.35  % CPULimit   : 60
% 0.19/0.35  % WCLimit    : 600
% 0.19/0.35  % DateTime   : Tue Dec  1 16:56:22 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.22/0.51  % (6523)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (6526)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (6539)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (6518)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (6531)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (6540)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (6521)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.57  % (6520)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.57  % (6532)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (6525)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.57/0.57  % (6522)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.57/0.57  % (6542)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.57/0.57  % (6519)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.58  % (6545)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.58  % (6517)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.57/0.58  % (6524)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.58  % (6537)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.57/0.58  % (6538)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.57/0.59  % (6535)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.57/0.59  % (6530)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.57/0.59  % (6528)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.57/0.59  % (6529)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.57/0.59  % (6543)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.57/0.59  % (6546)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.82/0.60  % (6544)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.82/0.60  % (6536)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.82/0.60  % (6527)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.82/0.61  % (6534)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.82/0.61  % (6541)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.82/0.61  % (6533)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.82/0.62  % (6523)Refutation found. Thanks to Tanya!
% 1.82/0.62  % SZS status Theorem for theBenchmark
% 1.82/0.62  % SZS output start Proof for theBenchmark
% 1.82/0.62  fof(f1181,plain,(
% 1.82/0.62    $false),
% 1.82/0.62    inference(subsumption_resolution,[],[f1180,f31])).
% 1.82/0.62  fof(f31,plain,(
% 1.82/0.62    sK1 != sK2),
% 1.82/0.62    inference(cnf_transformation,[],[f26])).
% 1.82/0.62  fof(f26,plain,(
% 1.82/0.62    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.82/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f25])).
% 1.82/0.62  fof(f25,plain,(
% 1.82/0.62    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.82/0.62    introduced(choice_axiom,[])).
% 1.82/0.62  fof(f17,plain,(
% 1.82/0.62    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.82/0.62    inference(flattening,[],[f16])).
% 1.82/0.62  fof(f16,plain,(
% 1.82/0.62    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.82/0.62    inference(ennf_transformation,[],[f15])).
% 1.82/0.62  fof(f15,negated_conjecture,(
% 1.82/0.62    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.82/0.62    inference(negated_conjecture,[],[f14])).
% 1.82/0.62  fof(f14,conjecture,(
% 1.82/0.62    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.82/0.62  fof(f1180,plain,(
% 1.82/0.62    sK1 = sK2),
% 1.82/0.62    inference(forward_demodulation,[],[f1179,f32])).
% 1.82/0.62  fof(f32,plain,(
% 1.82/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.82/0.62    inference(cnf_transformation,[],[f5])).
% 1.82/0.62  fof(f5,axiom,(
% 1.82/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.82/0.62  fof(f1179,plain,(
% 1.82/0.62    sK2 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.82/0.62    inference(forward_demodulation,[],[f778,f789])).
% 1.82/0.62  fof(f789,plain,(
% 1.82/0.62    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.82/0.62    inference(forward_demodulation,[],[f788,f737])).
% 1.82/0.62  fof(f737,plain,(
% 1.82/0.62    sK2 = k4_xboole_0(sK1,sK0)),
% 1.82/0.62    inference(superposition,[],[f713,f68])).
% 1.82/0.62  fof(f68,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 1.82/0.62    inference(superposition,[],[f37,f34])).
% 1.82/0.62  fof(f34,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f1])).
% 1.82/0.62  fof(f1,axiom,(
% 1.82/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.82/0.62  fof(f37,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f6])).
% 1.82/0.62  fof(f6,axiom,(
% 1.82/0.62    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.82/0.62  fof(f713,plain,(
% 1.82/0.62    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 1.82/0.62    inference(forward_demodulation,[],[f690,f203])).
% 1.82/0.62  fof(f203,plain,(
% 1.82/0.62    sK2 = k4_xboole_0(sK2,sK0)),
% 1.82/0.62    inference(forward_demodulation,[],[f195,f32])).
% 1.82/0.62  fof(f195,plain,(
% 1.82/0.62    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.82/0.62    inference(superposition,[],[f46,f127])).
% 1.82/0.62  fof(f127,plain,(
% 1.82/0.62    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.82/0.62    inference(resolution,[],[f48,f29])).
% 1.82/0.62  fof(f29,plain,(
% 1.82/0.62    r1_xboole_0(sK2,sK0)),
% 1.82/0.62    inference(cnf_transformation,[],[f26])).
% 1.82/0.62  fof(f48,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.82/0.62    inference(definition_unfolding,[],[f40,f35])).
% 1.82/0.62  fof(f35,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f9])).
% 1.82/0.62  fof(f9,axiom,(
% 1.82/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.82/0.62  fof(f40,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f27])).
% 1.82/0.62  fof(f27,plain,(
% 1.82/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.82/0.62    inference(nnf_transformation,[],[f2])).
% 1.82/0.62  fof(f2,axiom,(
% 1.82/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.82/0.62  fof(f46,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.82/0.62    inference(definition_unfolding,[],[f36,f35])).
% 1.82/0.62  fof(f36,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f8])).
% 1.82/0.62  fof(f8,axiom,(
% 1.82/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.82/0.62  fof(f690,plain,(
% 1.82/0.62    k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK2,sK0)),
% 1.82/0.62    inference(backward_demodulation,[],[f66,f671])).
% 1.82/0.62  fof(f671,plain,(
% 1.82/0.62    sK0 = sK3),
% 1.82/0.62    inference(backward_demodulation,[],[f473,f642])).
% 1.82/0.62  fof(f642,plain,(
% 1.82/0.62    sK0 = k2_xboole_0(sK0,sK3)),
% 1.82/0.62    inference(superposition,[],[f639,f34])).
% 1.82/0.62  fof(f639,plain,(
% 1.82/0.62    sK0 = k2_xboole_0(sK3,sK0)),
% 1.82/0.62    inference(resolution,[],[f635,f38])).
% 1.82/0.62  fof(f38,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.82/0.62    inference(cnf_transformation,[],[f18])).
% 1.82/0.62  fof(f18,plain,(
% 1.82/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.82/0.62    inference(ennf_transformation,[],[f4])).
% 1.82/0.62  fof(f4,axiom,(
% 1.82/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.82/0.62  fof(f635,plain,(
% 1.82/0.62    r1_tarski(sK3,sK0)),
% 1.82/0.62    inference(forward_demodulation,[],[f615,f204])).
% 1.82/0.62  fof(f204,plain,(
% 1.82/0.62    sK3 = k4_xboole_0(sK3,sK1)),
% 1.82/0.62    inference(forward_demodulation,[],[f196,f32])).
% 1.82/0.62  % (6533)Refutation not found, incomplete strategy% (6533)------------------------------
% 1.82/0.62  % (6533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (6533)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.62  
% 1.82/0.62  % (6533)Memory used [KB]: 10618
% 1.82/0.62  % (6533)Time elapsed: 0.154 s
% 1.82/0.62  % (6533)------------------------------
% 1.82/0.62  % (6533)------------------------------
% 1.82/0.62  fof(f196,plain,(
% 1.82/0.62    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 1.82/0.62    inference(superposition,[],[f46,f128])).
% 1.82/0.62  fof(f128,plain,(
% 1.82/0.62    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.82/0.62    inference(resolution,[],[f48,f30])).
% 1.82/0.62  fof(f30,plain,(
% 1.82/0.62    r1_xboole_0(sK3,sK1)),
% 1.82/0.62    inference(cnf_transformation,[],[f26])).
% 1.82/0.62  fof(f615,plain,(
% 1.82/0.62    r1_tarski(k4_xboole_0(sK3,sK1),sK0)),
% 1.82/0.62    inference(resolution,[],[f105,f56])).
% 1.82/0.62  fof(f56,plain,(
% 1.82/0.62    r1_tarski(sK3,k2_xboole_0(sK0,sK1))),
% 1.82/0.62    inference(superposition,[],[f53,f28])).
% 1.82/0.62  fof(f28,plain,(
% 1.82/0.62    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.82/0.62    inference(cnf_transformation,[],[f26])).
% 1.82/0.62  fof(f53,plain,(
% 1.82/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.82/0.62    inference(superposition,[],[f33,f34])).
% 1.82/0.62  fof(f33,plain,(
% 1.82/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f13])).
% 1.82/0.62  fof(f13,axiom,(
% 1.82/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.82/0.62  fof(f105,plain,(
% 1.82/0.62    ( ! [X4,X2,X3] : (~r1_tarski(X4,k2_xboole_0(X3,X2)) | r1_tarski(k4_xboole_0(X4,X2),X3)) )),
% 1.82/0.62    inference(superposition,[],[f43,f34])).
% 1.82/0.62  fof(f43,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f20])).
% 1.82/0.62  fof(f20,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.82/0.62    inference(ennf_transformation,[],[f7])).
% 1.82/0.62  fof(f7,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.82/0.62  fof(f473,plain,(
% 1.82/0.62    sK3 = k2_xboole_0(sK0,sK3)),
% 1.82/0.62    inference(resolution,[],[f467,f38])).
% 1.82/0.62  fof(f467,plain,(
% 1.82/0.62    r1_tarski(sK0,sK3)),
% 1.82/0.62    inference(backward_demodulation,[],[f326,f421])).
% 1.82/0.62  fof(f421,plain,(
% 1.82/0.62    sK0 = k4_xboole_0(sK0,sK2)),
% 1.82/0.62    inference(forward_demodulation,[],[f413,f32])).
% 1.82/0.62  fof(f413,plain,(
% 1.82/0.62    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.82/0.62    inference(superposition,[],[f46,f125])).
% 1.82/0.62  fof(f125,plain,(
% 1.82/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.82/0.62    inference(resolution,[],[f48,f50])).
% 1.82/0.62  fof(f50,plain,(
% 1.82/0.62    r1_xboole_0(sK0,sK2)),
% 1.82/0.62    inference(resolution,[],[f39,f29])).
% 1.82/0.62  fof(f39,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f19])).
% 1.82/0.62  fof(f19,plain,(
% 1.82/0.62    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.82/0.62    inference(ennf_transformation,[],[f3])).
% 1.82/0.62  fof(f3,axiom,(
% 1.82/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.82/0.62  fof(f326,plain,(
% 1.82/0.62    r1_tarski(k4_xboole_0(sK0,sK2),sK3)),
% 1.82/0.62    inference(resolution,[],[f103,f33])).
% 1.82/0.62  fof(f103,plain,(
% 1.82/0.62    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X0,sK2),sK3)) )),
% 1.82/0.62    inference(superposition,[],[f43,f28])).
% 1.82/0.62  fof(f66,plain,(
% 1.82/0.62    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.82/0.62    inference(superposition,[],[f37,f28])).
% 1.82/0.62  fof(f788,plain,(
% 1.82/0.62    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.82/0.62    inference(forward_demodulation,[],[f126,f671])).
% 1.82/0.62  fof(f126,plain,(
% 1.82/0.62    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.82/0.62    inference(resolution,[],[f48,f51])).
% 1.82/0.62  fof(f51,plain,(
% 1.82/0.62    r1_xboole_0(sK1,sK3)),
% 1.82/0.62    inference(resolution,[],[f39,f30])).
% 1.82/0.62  fof(f778,plain,(
% 1.82/0.62    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.82/0.62    inference(superposition,[],[f46,f737])).
% 1.82/0.62  % SZS output end Proof for theBenchmark
% 1.82/0.62  % (6523)------------------------------
% 1.82/0.62  % (6523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (6523)Termination reason: Refutation
% 1.82/0.62  
% 1.82/0.62  % (6523)Memory used [KB]: 11641
% 1.82/0.62  % (6523)Time elapsed: 0.197 s
% 1.82/0.62  % (6523)------------------------------
% 1.82/0.62  % (6523)------------------------------
% 1.82/0.62  % (6516)Success in time 0.26 s
%------------------------------------------------------------------------------
