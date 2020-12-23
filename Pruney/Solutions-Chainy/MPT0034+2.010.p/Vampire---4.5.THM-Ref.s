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
% DateTime   : Thu Dec  3 12:29:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 239 expanded)
%              Number of leaves         :   14 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  108 ( 404 expanded)
%              Number of equality atoms :   38 ( 134 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2492,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2491,f620])).

fof(f620,plain,(
    ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f83,f475,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f475,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f80,f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f27,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f80,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f32,f25,f38])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f83,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f32,f26,f38])).

fof(f26,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f2491,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,k3_xboole_0(sK1,k2_xboole_0(sK3,X0)))) ),
    inference(forward_demodulation,[],[f2490,f1544])).

fof(f1544,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f744,f54])).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f744,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f743,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f743,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f742,f54])).

fof(f742,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f741,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f741,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f740,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f740,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f739,f54])).

fof(f739,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f692,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f692,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X0))) ),
    inference(forward_demodulation,[],[f37,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f2490,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,k3_xboole_0(sK1,k2_xboole_0(sK3,X0)))) ),
    inference(forward_demodulation,[],[f2461,f36])).

fof(f2461,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(sK2,sK1),k2_xboole_0(sK3,X0))) ),
    inference(unit_resulting_resolution,[],[f1672,f1809,f39])).

fof(f1809,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(sK2,X0),k2_xboole_0(sK3,X1)) ),
    inference(unit_resulting_resolution,[],[f32,f1791,f38])).

fof(f1791,plain,(
    ! [X0] : r1_tarski(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f32,f1626])).

fof(f1626,plain,(
    ! [X16] : sK2 = k3_xboole_0(k2_xboole_0(sK3,X16),sK2) ),
    inference(forward_demodulation,[],[f1540,f54])).

fof(f1540,plain,(
    ! [X16] : k2_xboole_0(k1_xboole_0,sK2) = k3_xboole_0(k2_xboole_0(sK3,X16),sK2) ),
    inference(superposition,[],[f744,f298])).

fof(f298,plain,(
    ! [X2] : sK2 = k3_xboole_0(sK2,k2_xboole_0(sK3,X2)) ),
    inference(superposition,[],[f33,f165])).

fof(f165,plain,(
    ! [X7] : k2_xboole_0(sK3,X7) = k2_xboole_0(sK2,k2_xboole_0(sK3,X7)) ),
    inference(superposition,[],[f35,f56])).

fof(f56,plain,(
    sK3 = k2_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f26,f34])).

fof(f1672,plain,(
    ! [X3] : r1_tarski(k3_xboole_0(X3,sK0),k3_xboole_0(X3,sK1)) ),
    inference(superposition,[],[f286,f1590])).

fof(f1590,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1534,f54])).

fof(f1534,plain,(
    k3_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f744,f62])).

fof(f62,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f33,f55])).

fof(f55,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f25,f34])).

fof(f286,plain,(
    ! [X4,X2,X3] : r1_tarski(k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f32,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:48:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (17317)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.41  % (17318)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (17315)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.41  % (17319)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (17323)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.43  % (17313)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.44  % (17315)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f2492,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f2491,f620])).
% 0.20/0.44  fof(f620,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,X0))) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f83,f475,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.44  fof(f475,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK3)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f80,f27,f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.20/0.44    inference(negated_conjecture,[],[f13])).
% 0.20/0.44  fof(f13,conjecture,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),sK1)) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f32,f25,f38])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),sK3)) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f32,f26,f38])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    r1_tarski(sK2,sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f2491,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,k3_xboole_0(sK1,k2_xboole_0(sK3,X0))))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f2490,f1544])).
% 0.20/0.44  fof(f1544,plain,(
% 0.20/0.44    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.20/0.44    inference(superposition,[],[f744,f54])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f28,f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.44  fof(f744,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f743,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.44  fof(f743,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f742,f54])).
% 0.20/0.44  fof(f742,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f741,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f32,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.44  fof(f741,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X0)))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f740,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.44  fof(f740,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X1,X0)))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f739,f54])).
% 0.20/0.44  fof(f739,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,X0)))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f692,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.44  fof(f692,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k2_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(superposition,[],[f40,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X0)))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f37,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).
% 0.20/0.44  fof(f2490,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,k3_xboole_0(sK1,k2_xboole_0(sK3,X0))))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f2461,f36])).
% 0.20/0.44  fof(f2461,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(sK2,sK1),k2_xboole_0(sK3,X0)))) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f1672,f1809,f39])).
% 0.20/0.44  fof(f1809,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(sK2,X0),k2_xboole_0(sK3,X1))) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f32,f1791,f38])).
% 0.20/0.44  fof(f1791,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(sK3,X0))) )),
% 0.20/0.44    inference(superposition,[],[f32,f1626])).
% 0.20/0.44  fof(f1626,plain,(
% 0.20/0.44    ( ! [X16] : (sK2 = k3_xboole_0(k2_xboole_0(sK3,X16),sK2)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f1540,f54])).
% 0.20/0.44  fof(f1540,plain,(
% 0.20/0.44    ( ! [X16] : (k2_xboole_0(k1_xboole_0,sK2) = k3_xboole_0(k2_xboole_0(sK3,X16),sK2)) )),
% 0.20/0.44    inference(superposition,[],[f744,f298])).
% 0.20/0.44  fof(f298,plain,(
% 0.20/0.44    ( ! [X2] : (sK2 = k3_xboole_0(sK2,k2_xboole_0(sK3,X2))) )),
% 0.20/0.44    inference(superposition,[],[f33,f165])).
% 0.20/0.44  fof(f165,plain,(
% 0.20/0.44    ( ! [X7] : (k2_xboole_0(sK3,X7) = k2_xboole_0(sK2,k2_xboole_0(sK3,X7))) )),
% 0.20/0.44    inference(superposition,[],[f35,f56])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    sK3 = k2_xboole_0(sK2,sK3)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f26,f34])).
% 0.20/0.44  fof(f1672,plain,(
% 0.20/0.44    ( ! [X3] : (r1_tarski(k3_xboole_0(X3,sK0),k3_xboole_0(X3,sK1))) )),
% 0.20/0.44    inference(superposition,[],[f286,f1590])).
% 0.20/0.44  fof(f1590,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK1,sK0)),
% 0.20/0.44    inference(forward_demodulation,[],[f1534,f54])).
% 0.20/0.44  fof(f1534,plain,(
% 0.20/0.44    k3_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK0)),
% 0.20/0.44    inference(superposition,[],[f744,f62])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.44    inference(superposition,[],[f33,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    sK1 = k2_xboole_0(sK0,sK1)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f25,f34])).
% 0.20/0.44  fof(f286,plain,(
% 0.20/0.44    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,X3))) )),
% 0.20/0.44    inference(superposition,[],[f32,f36])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (17315)------------------------------
% 0.20/0.44  % (17315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (17315)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (17315)Memory used [KB]: 7036
% 0.20/0.44  % (17315)Time elapsed: 0.055 s
% 0.20/0.44  % (17315)------------------------------
% 0.20/0.44  % (17315)------------------------------
% 0.20/0.44  % (17312)Success in time 0.087 s
%------------------------------------------------------------------------------
