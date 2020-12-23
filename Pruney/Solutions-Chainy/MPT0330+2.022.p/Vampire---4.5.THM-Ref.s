%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  56 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 106 expanded)
%              Number of equality atoms :   11 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f693,plain,(
    $false ),
    inference(subsumption_resolution,[],[f692,f156])).

fof(f156,plain,(
    ! [X1] : r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,X1))) ),
    inference(superposition,[],[f134,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f134,plain,(
    ! [X7] : r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,sK3),X7)) ),
    inference(superposition,[],[f36,f30])).

fof(f30,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(resolution,[],[f26,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f692,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5))) ),
    inference(subsumption_resolution,[],[f666,f289])).

fof(f289,plain,(
    ! [X3] : r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(X3,sK5))) ),
    inference(superposition,[],[f149,f24])).

fof(f149,plain,(
    ! [X8] : r1_tarski(sK1,k2_xboole_0(X8,k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f37,f31])).

fof(f31,plain,(
    k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f22,f18])).

fof(f18,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X4,X5,X3] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5))) ),
    inference(resolution,[],[f26,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f666,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5))) ),
    inference(resolution,[],[f106,f19])).

fof(f19,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f11])).

fof(f106,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( r1_tarski(k2_xboole_0(X11,X12),k2_zfmisc_1(k2_xboole_0(X8,X10),X9))
      | ~ r1_tarski(X12,k2_zfmisc_1(X10,X9))
      | ~ r1_tarski(X11,k2_zfmisc_1(X8,X9)) ) ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:23:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (4500)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.14/0.42  % (4493)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.14/0.42  % (4494)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.42  % (4495)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  % (4490)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.46  % (4498)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.46  % (4489)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.47  % (4497)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.47  % (4496)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.47  % (4499)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.48  % (4491)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.48  % (4492)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.52  % (4492)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f693,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f692,f156])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,X1)))) )),
% 0.21/0.52    inference(superposition,[],[f134,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X7] : (r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,sK3),X7))) )),
% 0.21/0.52    inference(superposition,[],[f36,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.52    inference(resolution,[],[f22,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 0.21/0.52    inference(resolution,[],[f26,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.52  fof(f692,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f666,f289])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    ( ! [X3] : (r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(X3,sK5)))) )),
% 0.21/0.52    inference(superposition,[],[f149,f24])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ( ! [X8] : (r1_tarski(sK1,k2_xboole_0(X8,k2_zfmisc_1(sK4,sK5)))) )),
% 0.21/0.52    inference(superposition,[],[f37,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.52    inference(resolution,[],[f22,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))) )),
% 0.21/0.52    inference(resolution,[],[f26,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(superposition,[],[f20,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f666,plain,(
% 0.21/0.52    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5)))),
% 0.21/0.52    inference(resolution,[],[f106,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X12,X10,X8,X11,X9] : (r1_tarski(k2_xboole_0(X11,X12),k2_zfmisc_1(k2_xboole_0(X8,X10),X9)) | ~r1_tarski(X12,k2_zfmisc_1(X10,X9)) | ~r1_tarski(X11,k2_zfmisc_1(X8,X9))) )),
% 0.21/0.52    inference(superposition,[],[f27,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (4492)------------------------------
% 0.21/0.52  % (4492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4492)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (4492)Memory used [KB]: 11513
% 0.21/0.52  % (4492)Time elapsed: 0.090 s
% 0.21/0.52  % (4492)------------------------------
% 0.21/0.52  % (4492)------------------------------
% 0.21/0.52  % (4488)Success in time 0.16 s
%------------------------------------------------------------------------------
