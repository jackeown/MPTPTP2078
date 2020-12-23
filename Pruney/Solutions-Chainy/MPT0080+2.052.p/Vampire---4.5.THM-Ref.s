%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:06 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   46 (  84 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 194 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f639,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f544,f635,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f635,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f58,f69])).

fof(f69,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f49,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f23,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f23,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k4_xboole_0(sK0,X1),sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK0,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f30,f24,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f24,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f544,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f42,f236])).

fof(f236,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f38,f108])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f81,f91])).

fof(f91,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f54,f38])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,sK2),X0) ),
    inference(unit_resulting_resolution,[],[f39,f33])).

fof(f39,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f24,f28])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),X0) ),
    inference(unit_resulting_resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f42,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (4819)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.51  % (4820)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.52  % (4820)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % (4831)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.52  % (4843)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.24/0.53  % (4840)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.53  % (4837)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.53  % (4818)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (4846)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.53  % (4821)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.53  % (4824)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.53  % (4815)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.53  % (4835)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.54  % (4822)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f639,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f544,f635,f33])).
% 1.24/0.54  fof(f33,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f20])).
% 1.24/0.54  fof(f20,plain,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f1])).
% 1.24/0.54  fof(f1,axiom,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.24/0.54  fof(f635,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,sK1))) )),
% 1.24/0.54    inference(superposition,[],[f58,f69])).
% 1.24/0.54  fof(f69,plain,(
% 1.24/0.54    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f49,f35])).
% 1.24/0.54  fof(f35,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f21])).
% 1.24/0.54  fof(f21,plain,(
% 1.24/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.24/0.54    inference(ennf_transformation,[],[f4])).
% 1.24/0.54  fof(f4,axiom,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.24/0.54  fof(f49,plain,(
% 1.24/0.54    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f23,f31])).
% 1.24/0.54  fof(f31,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f19])).
% 1.24/0.54  fof(f19,plain,(
% 1.24/0.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.24/0.54    inference(ennf_transformation,[],[f8])).
% 1.24/0.54  fof(f8,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.24/0.54  fof(f23,plain,(
% 1.24/0.54    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.24/0.54    inference(cnf_transformation,[],[f14])).
% 1.24/0.54  fof(f14,plain,(
% 1.24/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.24/0.54    inference(flattening,[],[f13])).
% 1.24/0.54  fof(f13,plain,(
% 1.24/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.24/0.54    inference(ennf_transformation,[],[f11])).
% 1.24/0.54  fof(f11,negated_conjecture,(
% 1.24/0.54    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.24/0.54    inference(negated_conjecture,[],[f10])).
% 1.24/0.54  fof(f10,conjecture,(
% 1.24/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.24/0.54  fof(f58,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k4_xboole_0(sK0,X1),sK2))) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f41,f28])).
% 1.24/0.54  fof(f28,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f18])).
% 1.24/0.54  fof(f18,plain,(
% 1.24/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.24/0.54    inference(ennf_transformation,[],[f12])).
% 1.24/0.54  fof(f12,plain,(
% 1.24/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.54    inference(rectify,[],[f3])).
% 1.24/0.54  fof(f3,axiom,(
% 1.24/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.24/0.54  fof(f41,plain,(
% 1.24/0.54    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,X0),sK2)) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f30,f24,f26])).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f16])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.24/0.54    inference(flattening,[],[f15])).
% 1.24/0.54  fof(f15,plain,(
% 1.24/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.24/0.54    inference(ennf_transformation,[],[f9])).
% 1.24/0.54  fof(f9,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.24/0.54  fof(f24,plain,(
% 1.24/0.54    r1_xboole_0(sK0,sK2)),
% 1.24/0.54    inference(cnf_transformation,[],[f14])).
% 1.24/0.54  fof(f30,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f5])).
% 1.24/0.54  fof(f5,axiom,(
% 1.24/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.24/0.54  fof(f544,plain,(
% 1.24/0.54    ~r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f42,f236])).
% 1.24/0.54  fof(f236,plain,(
% 1.24/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.24/0.54    inference(superposition,[],[f38,f108])).
% 1.24/0.54  fof(f108,plain,(
% 1.24/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.24/0.54    inference(forward_demodulation,[],[f81,f91])).
% 1.24/0.54  fof(f91,plain,(
% 1.24/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f54,f38])).
% 1.24/0.54  fof(f54,plain,(
% 1.24/0.54    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,sK2),X0)) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f39,f33])).
% 1.24/0.54  fof(f39,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK2))) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f24,f28])).
% 1.24/0.54  fof(f81,plain,(
% 1.24/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),X0)) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f54,f36])).
% 1.24/0.54  fof(f36,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f6])).
% 1.24/0.54  fof(f6,axiom,(
% 1.24/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.24/0.54  fof(f38,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f22])).
% 1.24/0.54  fof(f22,plain,(
% 1.24/0.54    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f7])).
% 1.24/0.54  fof(f7,axiom,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 1.24/0.54  fof(f42,plain,(
% 1.24/0.54    k1_xboole_0 != k4_xboole_0(sK0,sK1)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f25,f37])).
% 1.24/0.54  fof(f37,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f6])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ~r1_tarski(sK0,sK1)),
% 1.24/0.54    inference(cnf_transformation,[],[f14])).
% 1.24/0.54  % SZS output end Proof for theBenchmark
% 1.24/0.54  % (4820)------------------------------
% 1.24/0.54  % (4820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (4820)Termination reason: Refutation
% 1.24/0.54  
% 1.24/0.54  % (4820)Memory used [KB]: 6396
% 1.24/0.54  % (4820)Time elapsed: 0.112 s
% 1.24/0.54  % (4820)------------------------------
% 1.24/0.54  % (4820)------------------------------
% 1.24/0.54  % (4827)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.54  % (4812)Success in time 0.182 s
%------------------------------------------------------------------------------
