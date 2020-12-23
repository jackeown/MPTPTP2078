%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 135 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :   70 ( 211 expanded)
%              Number of equality atoms :   31 (  87 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4052,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4036,f42])).

fof(f42,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f17,f39])).

fof(f39,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(forward_demodulation,[],[f36,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f36,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,X2)
      | r1_xboole_0(X2,k4_xboole_0(X3,k1_xboole_0)) ) ),
    inference(superposition,[],[f28,f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f17,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
          & r1_xboole_0(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

fof(f4036,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f33,f4035])).

fof(f4035,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f4004,f21])).

fof(f4004,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f2709,f830])).

fof(f830,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f816,f86])).

fof(f86,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f54,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k3_xboole_0(X1,k1_xboole_0),X0) ),
    inference(superposition,[],[f24,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f816,plain,(
    k3_xboole_0(sK2,sK0) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f445,f712])).

fof(f712,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f693,f22])).

fof(f693,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f692,f21])).

fof(f692,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f662,f86])).

fof(f662,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f26,f21])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f445,plain,(
    ! [X0] : k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,k2_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f411,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f411,plain,(
    ! [X0] : k3_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k3_xboole_0(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f43,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f18,f39])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f2709,plain,(
    ! [X8] : k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK2,X8)) ),
    inference(superposition,[],[f759,f411])).

fof(f759,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,X4) = k4_xboole_0(X2,k3_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(backward_demodulation,[],[f694,f712])).

fof(f694,plain,(
    ! [X4,X2,X3] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X4)) = k4_xboole_0(X2,k3_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f663,f23])).

fof(f663,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k3_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k1_xboole_0) ),
    inference(superposition,[],[f26,f22])).

fof(f33,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f19,f28])).

fof(f19,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (22315)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (22316)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (22320)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (22314)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (22324)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.46  % (22319)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.46  % (22325)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.47  % (22318)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.47  % (22321)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.47  % (22322)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.50  % (22317)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.50  % (22323)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.54  % (22316)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f4052,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f4036,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ~r1_xboole_0(sK1,sK0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f17,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r1_xboole_0(X3,X2) | r1_xboole_0(X2,X3)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f36,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r1_xboole_0(X3,X2) | r1_xboole_0(X2,k4_xboole_0(X3,k1_xboole_0))) )),
% 0.21/0.54    inference(superposition,[],[f28,f21])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).
% 0.21/0.54  fof(f4036,plain,(
% 0.21/0.54    r1_xboole_0(sK1,sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f33,f4035])).
% 0.21/0.54  fof(f4035,plain,(
% 0.21/0.54    sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f4004,f21])).
% 0.21/0.54  fof(f4004,plain,(
% 0.21/0.54    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f2709,f830])).
% 0.21/0.54  fof(f830,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f816,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f54,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k3_xboole_0(X1,k1_xboole_0),X0)) )),
% 0.21/0.54    inference(superposition,[],[f24,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.54  fof(f816,plain,(
% 0.21/0.54    k3_xboole_0(sK2,sK0) = k3_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f445,f712])).
% 0.21/0.54  fof(f712,plain,(
% 0.21/0.54    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.54    inference(superposition,[],[f693,f22])).
% 0.21/0.54  fof(f693,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f692,f21])).
% 0.21/0.54  fof(f692,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f662,f86])).
% 0.21/0.54  fof(f662,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(superposition,[],[f26,f21])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    ( ! [X0] : (k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,k2_xboole_0(X0,sK0))) )),
% 0.21/0.54    inference(superposition,[],[f411,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f411,plain,(
% 0.21/0.54    ( ! [X0] : (k3_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k3_xboole_0(sK2,X0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f43,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    r1_xboole_0(sK2,sK0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f18,f39])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    r1_xboole_0(sK0,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f2709,plain,(
% 0.21/0.54    ( ! [X8] : (k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK2,X8))) )),
% 0.21/0.54    inference(superposition,[],[f759,f411])).
% 0.21/0.54  fof(f759,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (k4_xboole_0(X2,X4) = k4_xboole_0(X2,k3_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f694,f712])).
% 0.21/0.54  fof(f694,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X4)) = k4_xboole_0(X2,k3_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f663,f23])).
% 0.21/0.54  fof(f663,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f26,f22])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f19,f28])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (22316)------------------------------
% 0.21/0.54  % (22316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22316)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (22316)Memory used [KB]: 8315
% 0.21/0.54  % (22316)Time elapsed: 0.109 s
% 0.21/0.54  % (22316)------------------------------
% 0.21/0.54  % (22316)------------------------------
% 0.21/0.54  % (22313)Success in time 0.178 s
%------------------------------------------------------------------------------
