%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 127 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 244 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(resolution,[],[f163,f73])).

fof(f73,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X6,X7] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X6,X7)),k9_relat_1(sK2,X6)) ),
    inference(forward_demodulation,[],[f62,f40])).

fof(f40,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK2,X6)) = k9_relat_1(sK2,X6) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f62,plain,(
    ! [X6,X7] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X6,X7))),k9_relat_1(sK2,X6)) ),
    inference(forward_demodulation,[],[f61,f41])).

fof(f41,plain,(
    ! [X8,X7] : k7_relat_1(k7_relat_1(sK2,X7),X8) = k7_relat_1(sK2,k3_xboole_0(X7,X8)) ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f61,plain,(
    ! [X6,X7] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X6),X7)),k9_relat_1(sK2,X6)) ),
    inference(forward_demodulation,[],[f50,f40])).

fof(f50,plain,(
    ! [X6,X7] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X6),X7)),k2_relat_1(k7_relat_1(sK2,X6))) ),
    inference(resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f42,plain,(
    ! [X9] : v1_relat_1(k7_relat_1(sK2,X9)) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f72,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f26,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f163,plain,(
    ! [X2,X3] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X2,X3)),k9_relat_1(sK2,X3)) ),
    inference(forward_demodulation,[],[f162,f40])).

fof(f162,plain,(
    ! [X2,X3] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))),k9_relat_1(sK2,X3)) ),
    inference(forward_demodulation,[],[f161,f40])).

fof(f161,plain,(
    ! [X2,X3] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))),k2_relat_1(k7_relat_1(sK2,X3))) ),
    inference(subsumption_resolution,[],[f160,f42])).

fof(f160,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X3))
      | r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))),k2_relat_1(k7_relat_1(sK2,X3))) ) ),
    inference(subsumption_resolution,[],[f154,f42])).

fof(f154,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3)))
      | ~ v1_relat_1(k7_relat_1(sK2,X3))
      | r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))),k2_relat_1(k7_relat_1(sK2,X3))) ) ),
    inference(resolution,[],[f83,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f83,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X2,X3)),k7_relat_1(sK2,X3)) ),
    inference(forward_demodulation,[],[f82,f41])).

fof(f82,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3)) ),
    inference(subsumption_resolution,[],[f81,f25])).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK2)
      | r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3)) ) ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X2))
      | ~ v1_relat_1(sK2)
      | r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f39,plain,(
    ! [X5] : r1_tarski(k7_relat_1(sK2,X5),sK2) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (23426)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.48  % (23407)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.48  % (23426)Refutation not found, incomplete strategy% (23426)------------------------------
% 0.22/0.48  % (23426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23409)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.48  % (23426)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23426)Memory used [KB]: 10618
% 0.22/0.48  % (23426)Time elapsed: 0.005 s
% 0.22/0.48  % (23426)------------------------------
% 0.22/0.48  % (23426)------------------------------
% 0.22/0.48  % (23423)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.49  % (23404)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (23408)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (23403)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (23410)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (23412)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (23420)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (23418)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (23424)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (23424)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(resolution,[],[f163,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f72,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X6,X7] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X6,X7)),k9_relat_1(sK2,X6))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f62,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X6] : (k2_relat_1(k7_relat_1(sK2,X6)) = k9_relat_1(sK2,X6)) )),
% 0.22/0.51    inference(resolution,[],[f25,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    v1_relat_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f11])).
% 0.22/0.51  fof(f11,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X6,X7] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X6,X7))),k9_relat_1(sK2,X6))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f61,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X8,X7] : (k7_relat_1(k7_relat_1(sK2,X7),X8) = k7_relat_1(sK2,k3_xboole_0(X7,X8))) )),
% 0.22/0.51    inference(resolution,[],[f25,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X6,X7] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X6),X7)),k9_relat_1(sK2,X6))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f50,f40])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X6,X7] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X6),X7)),k2_relat_1(k7_relat_1(sK2,X6)))) )),
% 0.22/0.51    inference(resolution,[],[f42,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X9] : (v1_relat_1(k7_relat_1(sK2,X9))) )),
% 0.22/0.51    inference(resolution,[],[f25,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 0.22/0.51    inference(resolution,[],[f26,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X2,X3)),k9_relat_1(sK2,X3))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f162,f40])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ( ! [X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))),k9_relat_1(sK2,X3))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f161,f40])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ( ! [X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))),k2_relat_1(k7_relat_1(sK2,X3)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f160,f42])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK2,X3)) | r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))),k2_relat_1(k7_relat_1(sK2,X3)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f154,f42])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))) | ~v1_relat_1(k7_relat_1(sK2,X3)) | r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))),k2_relat_1(k7_relat_1(sK2,X3)))) )),
% 0.22/0.51    inference(resolution,[],[f83,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X2,X3] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X2,X3)),k7_relat_1(sK2,X3))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f82,f41])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f81,f25])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_relat_1(sK2) | r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f76,f42])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK2,X2)) | ~v1_relat_1(sK2) | r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3))) )),
% 0.22/0.51    inference(resolution,[],[f39,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X5] : (r1_tarski(k7_relat_1(sK2,X5),sK2)) )),
% 0.22/0.51    inference(resolution,[],[f25,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (23424)------------------------------
% 0.22/0.51  % (23424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23424)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (23424)Memory used [KB]: 1663
% 0.22/0.51  % (23424)Time elapsed: 0.100 s
% 0.22/0.51  % (23424)------------------------------
% 0.22/0.51  % (23424)------------------------------
% 0.22/0.51  % (23405)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (23399)Success in time 0.15 s
%------------------------------------------------------------------------------
