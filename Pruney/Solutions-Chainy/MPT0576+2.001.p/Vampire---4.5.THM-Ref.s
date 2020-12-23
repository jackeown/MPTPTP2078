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
% DateTime   : Thu Dec  3 12:50:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  55 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :   74 ( 175 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f557,plain,(
    $false ),
    inference(subsumption_resolution,[],[f553,f22])).

fof(f22,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).

fof(f553,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
    inference(superposition,[],[f217,f45])).

fof(f45,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f217,plain,(
    ! [X4,X5] : r1_tarski(k10_relat_1(sK2,X5),k10_relat_1(sK3,k2_xboole_0(X5,X4))) ),
    inference(superposition,[],[f62,f74])).

fof(f74,plain,(
    ! [X2,X3] : k2_xboole_0(k10_relat_1(sK3,X3),k10_relat_1(sK3,X2)) = k10_relat_1(sK3,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : k10_relat_1(sK3,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1)) ),
    inference(resolution,[],[f19,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(sK2,X2),k2_xboole_0(X3,k10_relat_1(sK3,X2))) ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f44,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2)) ),
    inference(subsumption_resolution,[],[f43,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK2)
      | r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2)) ) ),
    inference(subsumption_resolution,[],[f42,f19])).

fof(f42,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK3)
      | ~ v1_relat_1(sK2)
      | r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2)) ) ),
    inference(resolution,[],[f20,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

fof(f20,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:35:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (16945)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (16958)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (16940)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (16938)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (16950)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (16944)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (16942)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (16937)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (16948)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (16956)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (16957)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (16936)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (16954)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (16939)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (16952)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (16953)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (16947)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (16940)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (16941)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f557,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f553,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f9])).
% 0.22/0.54  fof(f9,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).
% 0.22/0.54  fof(f553,plain,(
% 0.22/0.54    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))),
% 0.22/0.54    inference(superposition,[],[f217,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.54    inference(resolution,[],[f21,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    ( ! [X4,X5] : (r1_tarski(k10_relat_1(sK2,X5),k10_relat_1(sK3,k2_xboole_0(X5,X4)))) )),
% 0.22/0.54    inference(superposition,[],[f62,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k2_xboole_0(k10_relat_1(sK3,X3),k10_relat_1(sK3,X2)) = k10_relat_1(sK3,k2_xboole_0(X2,X3))) )),
% 0.22/0.54    inference(superposition,[],[f36,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k10_relat_1(sK3,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1))) )),
% 0.22/0.54    inference(resolution,[],[f19,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    v1_relat_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,X2),k2_xboole_0(X3,k10_relat_1(sK3,X2)))) )),
% 0.22/0.54    inference(resolution,[],[f44,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f43,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2] : (~v1_relat_1(sK2) | r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f42,f19])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X2] : (~v1_relat_1(sK3) | ~v1_relat_1(sK2) | r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2))) )),
% 0.22/0.54    inference(resolution,[],[f20,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    r1_tarski(sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (16940)------------------------------
% 0.22/0.54  % (16940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16940)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (16940)Memory used [KB]: 6780
% 0.22/0.54  % (16940)Time elapsed: 0.122 s
% 0.22/0.54  % (16940)------------------------------
% 0.22/0.54  % (16940)------------------------------
% 0.22/0.54  % (16959)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (16934)Success in time 0.172 s
%------------------------------------------------------------------------------
