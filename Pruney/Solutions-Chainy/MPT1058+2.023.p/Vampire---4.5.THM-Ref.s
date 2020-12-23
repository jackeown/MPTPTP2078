%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:20 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 133 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 225 expanded)
%              Number of equality atoms :   43 ( 120 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2047,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1962,f27])).

fof(f27,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f1962,plain,(
    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(superposition,[],[f852,f980])).

fof(f980,plain,(
    k10_relat_1(sK0,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f460,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f460,plain,(
    k10_relat_1(sK0,sK2) = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k10_relat_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f439,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f439,plain,(
    k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f109,f259])).

fof(f259,plain,(
    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    inference(resolution,[],[f199,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k10_relat_1(sK0,sK2),X0),sK1) ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f37,f26])).

fof(f26,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f190,f29])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f44,f42])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f109,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f42,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f39,f39])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f852,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK0,X1))) ),
    inference(resolution,[],[f45,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    inference(forward_demodulation,[],[f43,f42])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (30562)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (30554)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (30549)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (30561)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (30550)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (30551)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (30556)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (30553)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (30560)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (30564)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (30563)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.53  % (30565)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  % (30552)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.53  % (30555)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (30559)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.54  % (30558)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.46/0.55  % (30566)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.46/0.55  % (30557)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.62/0.62  % (30558)Refutation found. Thanks to Tanya!
% 1.62/0.62  % SZS status Theorem for theBenchmark
% 1.62/0.62  % SZS output start Proof for theBenchmark
% 1.62/0.62  fof(f2047,plain,(
% 1.62/0.62    $false),
% 1.62/0.62    inference(subsumption_resolution,[],[f1962,f27])).
% 1.62/0.62  fof(f27,plain,(
% 1.62/0.62    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.62/0.62    inference(cnf_transformation,[],[f24])).
% 1.62/0.62  fof(f24,plain,(
% 1.62/0.62    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 1.62/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).
% 1.62/0.62  fof(f22,plain,(
% 1.62/0.62    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f23,plain,(
% 1.62/0.62    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f15,plain,(
% 1.62/0.62    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 1.62/0.62    inference(ennf_transformation,[],[f14])).
% 1.62/0.62  fof(f14,plain,(
% 1.62/0.62    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.62/0.62    inference(pure_predicate_removal,[],[f13])).
% 1.62/0.62  fof(f13,negated_conjecture,(
% 1.62/0.62    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.62/0.62    inference(negated_conjecture,[],[f12])).
% 1.62/0.62  fof(f12,conjecture,(
% 1.62/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.62/0.62  fof(f1962,plain,(
% 1.62/0.62    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.62/0.62    inference(superposition,[],[f852,f980])).
% 1.62/0.62  fof(f980,plain,(
% 1.62/0.62    k10_relat_1(sK0,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k10_relat_1(sK0,sK2)))),
% 1.62/0.62    inference(superposition,[],[f460,f42])).
% 1.62/0.62  fof(f42,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.62/0.62    inference(definition_unfolding,[],[f33,f40])).
% 1.62/0.62  fof(f40,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.62/0.62    inference(definition_unfolding,[],[f31,f39])).
% 1.62/0.62  fof(f39,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.62/0.62    inference(definition_unfolding,[],[f32,f35])).
% 1.62/0.62  fof(f35,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f9])).
% 1.62/0.62  fof(f9,axiom,(
% 1.62/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.62/0.62  fof(f32,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f8])).
% 1.62/0.62  fof(f8,axiom,(
% 1.62/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.62  fof(f31,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.62/0.62    inference(cnf_transformation,[],[f10])).
% 1.62/0.62  fof(f10,axiom,(
% 1.62/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.62/0.62  fof(f33,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f6])).
% 1.62/0.62  fof(f6,axiom,(
% 1.62/0.62    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.62/0.62  fof(f460,plain,(
% 1.62/0.62    k10_relat_1(sK0,sK2) = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k10_relat_1(sK0,sK2)))),
% 1.62/0.62    inference(forward_demodulation,[],[f439,f28])).
% 1.62/0.62  fof(f28,plain,(
% 1.62/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.62/0.62    inference(cnf_transformation,[],[f5])).
% 1.62/0.62  fof(f5,axiom,(
% 1.62/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.62/0.62  fof(f439,plain,(
% 1.62/0.62    k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k10_relat_1(sK0,sK2)))),
% 1.62/0.62    inference(superposition,[],[f109,f259])).
% 1.62/0.62  fof(f259,plain,(
% 1.62/0.62    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 1.62/0.62    inference(resolution,[],[f199,f52])).
% 1.62/0.62  fof(f52,plain,(
% 1.62/0.62    ( ! [X0] : (r1_tarski(k4_xboole_0(k10_relat_1(sK0,sK2),X0),sK1)) )),
% 1.62/0.62    inference(resolution,[],[f49,f29])).
% 1.62/0.62  fof(f29,plain,(
% 1.62/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f3])).
% 1.62/0.62  fof(f3,axiom,(
% 1.62/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.62/0.62  fof(f49,plain,(
% 1.62/0.62    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK0,sK2)) | r1_tarski(X0,sK1)) )),
% 1.62/0.62    inference(resolution,[],[f37,f26])).
% 1.62/0.62  fof(f26,plain,(
% 1.62/0.62    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.62/0.62    inference(cnf_transformation,[],[f24])).
% 1.62/0.62  fof(f37,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f19])).
% 1.62/0.62  fof(f19,plain,(
% 1.62/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.62/0.62    inference(flattening,[],[f18])).
% 1.62/0.62  fof(f18,plain,(
% 1.62/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.62/0.62    inference(ennf_transformation,[],[f2])).
% 1.62/0.62  fof(f2,axiom,(
% 1.62/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.62/0.62  fof(f199,plain,(
% 1.62/0.62    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.62/0.62    inference(subsumption_resolution,[],[f190,f29])).
% 1.62/0.62  fof(f190,plain,(
% 1.62/0.62    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | ~r1_tarski(k4_xboole_0(X0,X1),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.62/0.62    inference(resolution,[],[f46,f34])).
% 1.62/0.62  fof(f34,plain,(
% 1.62/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 1.62/0.62    inference(cnf_transformation,[],[f16])).
% 1.62/0.62  fof(f16,plain,(
% 1.62/0.62    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 1.62/0.62    inference(ennf_transformation,[],[f4])).
% 1.62/0.62  fof(f4,axiom,(
% 1.62/0.62    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 1.62/0.62  fof(f46,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.62/0.62    inference(forward_demodulation,[],[f44,f42])).
% 1.62/0.62  fof(f44,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.62/0.62    inference(definition_unfolding,[],[f38,f40])).
% 1.62/0.62  fof(f38,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f21])).
% 1.62/0.62  fof(f21,plain,(
% 1.62/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.62/0.62    inference(flattening,[],[f20])).
% 1.62/0.62  fof(f20,plain,(
% 1.62/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.62/0.62    inference(ennf_transformation,[],[f1])).
% 1.62/0.62  fof(f1,axiom,(
% 1.62/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.62/0.62  fof(f109,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 1.62/0.62    inference(superposition,[],[f42,f41])).
% 1.62/0.62  fof(f41,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.62/0.62    inference(definition_unfolding,[],[f30,f39,f39])).
% 1.62/0.62  fof(f30,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f7])).
% 1.62/0.62  fof(f7,axiom,(
% 1.62/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.62/0.62  fof(f852,plain,(
% 1.62/0.62    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK0,X1)))) )),
% 1.62/0.62    inference(resolution,[],[f45,f25])).
% 1.62/0.62  fof(f25,plain,(
% 1.62/0.62    v1_relat_1(sK0)),
% 1.62/0.62    inference(cnf_transformation,[],[f24])).
% 1.62/0.62  fof(f45,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1)))) )),
% 1.62/0.62    inference(forward_demodulation,[],[f43,f42])).
% 1.62/0.62  fof(f43,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 1.62/0.62    inference(definition_unfolding,[],[f36,f40])).
% 1.62/0.62  fof(f36,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f17])).
% 1.62/0.62  fof(f17,plain,(
% 1.62/0.62    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.62/0.62    inference(ennf_transformation,[],[f11])).
% 1.62/0.62  fof(f11,axiom,(
% 1.62/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.62/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.62/0.62  % SZS output end Proof for theBenchmark
% 1.62/0.62  % (30558)------------------------------
% 1.62/0.62  % (30558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.62  % (30558)Termination reason: Refutation
% 1.62/0.62  
% 1.62/0.62  % (30558)Memory used [KB]: 11769
% 1.62/0.62  % (30558)Time elapsed: 0.179 s
% 1.62/0.62  % (30558)------------------------------
% 1.62/0.62  % (30558)------------------------------
% 1.62/0.62  % (30548)Success in time 0.261 s
%------------------------------------------------------------------------------
